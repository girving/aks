#!/usr/bin/env -S cargo +nightly -Zscript
//! Diagnostic experiment: decompose siblingNativeCount into its mathematical sources.
//!
//! For the concrete split, we analyze the parent bag B = bags(level-1, p) at each stage.
//! Items in B are classified into four contiguous groups (sorted by perm value):
//!   s_lo (below-strangers) | n_L (left-native) | n_R (right-native) | s_hi (above-strangers)
//!
//! Key quantities:
//!   C = s_lo + n_L  (count of items with perm below child boundary)
//!   b = total items in parent bag
//!   siblingNativeCount(left child) = max(0, b/2 - C)  (right-native items in left half)
//!   siblingNativeCount(right child) = max(0, C - b/2)  (left-native items in right half)
//!
//! The bound we need: |C - b/2| ≤ cnativeCoeff * cap(parent)
//!
//! Sub-decomposition of |C - b/2|:
//!   C - b/2 = (n_L - n_R + s_lo - s_hi) / 2
//! So the bound reduces to bounding |n_L - n_R| + |s_lo - s_hi|.
//!
//! This experiment measures all these quantities and validates potential sub-lemma statements.

use std::collections::BTreeMap;

struct Params {
    a: f64,
    nu: f64,
    lambda: f64,
    eps: f64,
}

impl Params {
    fn seiferas() -> Self {
        Params { a: 10.0, nu: 0.65, lambda: 1.0/99.0, eps: 1.0/99.0 }
    }
    fn capacity(&self, n: usize, t: usize, level: usize) -> f64 {
        (n as f64) * self.nu.powi(t as i32) * self.a.powi(level as i32)
    }
    fn cnative_coeff(&self) -> f64 {
        self.eps / 2.0
            + 2.0 * self.lambda * self.eps * self.a.powi(2) / (1.0 - (2.0 * self.eps * self.a).powi(2))
            + 1.0 / (8.0 * self.a.powi(2) - 2.0)
    }
}

#[derive(Clone, Default)]
struct SplitResult {
    to_parent: Vec<usize>,
    to_left_child: Vec<usize>,
    to_right_child: Vec<usize>,
}

struct BagTree {
    n: usize,
    max_level: usize,
    bags: BTreeMap<(usize, usize), Vec<usize>>,
}

impl BagTree {
    fn new(n: usize) -> Self {
        assert!(n.is_power_of_two() && n >= 4);
        let max_level = n.trailing_zeros() as usize - 1;
        let mut bags = BTreeMap::new();
        bags.insert((0, 0), (0..n).collect());
        BagTree { n, max_level, bags }
    }

    fn bag_size(&self, level: usize) -> usize {
        self.n >> level
    }

    fn native_bag_idx(&self, level: usize, rank: usize) -> usize {
        let chunk_size = self.bag_size(level);
        if chunk_size == 0 { rank } else { rank / chunk_size }
    }

    fn is_j_stranger(&self, rank: usize, level: usize, idx: usize, j: usize) -> bool {
        if j == 0 || j > level { return false; }
        let check_level = level - (j - 1);
        let check_idx = idx >> (j - 1);
        self.native_bag_idx(check_level, rank) != check_idx
    }

    fn sibling_native_count(&self, items: &[usize], level: usize, idx: usize) -> usize {
        items.iter().filter(|&&rank| {
            self.is_j_stranger(rank, level, idx, 1) &&
            !self.is_j_stranger(rank, level, idx, 2)
        }).count()
    }

    fn do_stage_exact_sort(&mut self, params: &Params, t: usize)
        -> BTreeMap<(usize, usize), SplitResult>
    {
        let mut splits: BTreeMap<(usize, usize), SplitResult> = BTreeMap::new();
        let mut new_bags: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();

        let active: Vec<((usize, usize), Vec<usize>)> = self.bags.iter()
            .filter(|(_, items)| !items.is_empty())
            .map(|(&k, v)| (k, v.clone()))
            .collect();

        for ((level, idx), mut items) in active {
            items.sort();

            let b = params.capacity(self.n, t, level);
            let kick_per_side = (params.lambda * b).floor() as usize;
            let has_parent = level > 0;
            let has_children = level < self.max_level;

            let mut split = SplitResult::default();

            if !has_parent {
                let mid = items.len() / 2;
                split.to_left_child = items[..mid].to_vec();
                split.to_right_child = items[mid..].to_vec();
            } else if !has_children {
                split.to_parent = items;
            } else {
                let total = items.len();
                let kick_small = kick_per_side.min(total);
                let kick_large = kick_per_side.min(total.saturating_sub(kick_small));

                split.to_parent.extend_from_slice(&items[..kick_small]);
                split.to_parent.extend_from_slice(&items[total - kick_large..]);

                let mut middle: Vec<usize> = items[kick_small..total - kick_large].to_vec();

                if middle.len() % 2 == 1 {
                    let mid_idx = middle.len() / 2;
                    split.to_parent.push(middle.remove(mid_idx));
                }

                let half = middle.len() / 2;
                split.to_left_child = middle[..half].to_vec();
                split.to_right_child = middle[half..].to_vec();
            }

            if has_parent {
                new_bags.entry((level - 1, idx / 2)).or_default().extend(&split.to_parent);
            }
            if has_children {
                new_bags.entry((level + 1, 2 * idx)).or_default().extend(&split.to_left_child);
                new_bags.entry((level + 1, 2 * idx + 1)).or_default().extend(&split.to_right_child);
            }

            splits.insert((level, idx), split);
        }

        self.bags = new_bags;
        splits
    }
}

fn from_parent(splits: &BTreeMap<(usize, usize), SplitResult>, level: usize, idx: usize) -> Vec<usize> {
    if level == 0 { return vec![]; }
    let parent_key = (level - 1, idx / 2);
    match splits.get(&parent_key) {
        Some(s) => {
            if idx % 2 == 0 { s.to_left_child.clone() }
            else { s.to_right_child.clone() }
        }
        None => vec![],
    }
}

/// Decompose a parent bag's items into the four contiguous groups.
/// Returns (s_lo, n_L, n_R, s_hi, child_boundary)
fn decompose_parent(
    n: usize, parent_items: &[usize], parent_level: usize, parent_idx: usize,
) -> (usize, usize, usize, usize, usize) {
    let bs = n >> parent_level; // bagSize at parent level
    let child_boundary = parent_idx * bs + bs / 2; // perm value boundary between left/right native

    let lo = parent_idx * bs;
    let hi = (parent_idx + 1) * bs;

    let mut s_lo = 0usize;
    let mut n_l = 0usize;
    let mut n_r = 0usize;
    let mut s_hi = 0usize;

    for &rank in parent_items {
        if rank < lo {
            s_lo += 1;
        } else if rank < child_boundary {
            n_l += 1;
        } else if rank < hi {
            n_r += 1;
        } else {
            s_hi += 1;
        }
    }
    (s_lo, n_l, n_r, s_hi, child_boundary)
}

/// Validate that siblingNativeCount = max(0, b/2 - C) for left child
/// or max(0, C - b/2) for right child, where C = s_lo + n_L.
/// Returns (computed_formula, actual_sn_count, match).
fn validate_formula(
    tree: &BagTree, from_parent_items: &[usize],
    parent_items: &[usize], parent_level: usize, parent_idx: usize,
    child_level: usize, child_idx: usize,
) -> (usize, usize, bool) {
    let (s_lo, n_l, _n_r, _s_hi, _cb) = decompose_parent(
        tree.n, parent_items, parent_level, parent_idx,
    );
    let b = parent_items.len();
    let c = s_lo + n_l; // count of items with perm below child boundary
    let half_b = b / 2; // integer division

    // BUT the concreteSplit uses fringeSize + childSendSize, not just b/2.
    // Actually the split point between left and right children is at rank f + h = b/2 (integer).
    // But we need to account for the fringe and odd-middle kick.

    // Let's compute the actual sibling-native count
    let actual_sn = tree.sibling_native_count(from_parent_items, child_level, child_idx);

    // Now the formula: how many sibling-native items are in fromParent?
    // For LEFT child (idx even): sibling-native = right-native items in toLeftChild
    //   These are items with perm ≥ child_boundary in ranks [f, f+h)
    //   = items with rank ∈ [max(c, f), min(c + n_r, f+h))
    // For RIGHT child (idx odd): sibling-native = left-native items in toRightChild
    //   = items with rank ∈ [max(f+h, s_lo), min(f+h + ???, f+2h))
    //
    // Actually the simple formula is: if the concreteSplit sends items with rank [f, f+h)
    // to left child, then among those, the ones with perm ≥ boundary are right-native
    // (sibling-native for left child). The count is max(0, min(c + n_r, f+h) - max(c, f))
    // where c = s_lo + n_l is the index where right-native items start in rank order.

    // Simplified formula: |C - b/2| (approximately)
    let formula = if child_idx % 2 == 0 {
        // Left child: sibling-native = right-native in left half
        half_b.saturating_sub(c)
    } else {
        // Right child: sibling-native = left-native in right half
        c.saturating_sub(half_b)
    };

    (formula, actual_sn, formula == actual_sn)
}

#[derive(Default)]
struct Stats {
    total_sn: usize,
    total_formula_mismatch: usize,
    max_deviation_ratio: f64, // |C - b/2| / (cnc * cap)
    max_deviation_detail: String,
    max_stranger_asymmetry_ratio: f64, // |s_lo - s_hi| / (lam * cap)
    max_native_imbalance_ratio: f64,   // |n_L - n_R| / cap
    max_native_imbalance_detail: String,
    // Track sources of deviation
    max_stranger_contrib: f64, // |s_lo - s_hi| / (2 * cnc * cap)
    max_native_contrib: f64,   // |n_L - n_R| / (2 * cnc * cap)
}

fn main() {
    let params = Params::seiferas();
    let cnc = params.cnative_coeff();
    println!("cnativeCoeff = {:.8}", cnc);
    println!("eps/2       = {:.8}", params.eps / 2.0);
    println!("lam         = {:.8}", params.lambda);
    println!();

    let mut global = Stats::default();

    for exp in 3..=14 {
        let n = 1usize << exp;
        let mut tree = BagTree::new(n);
        let threshold = 2.0;
        let mut local = Stats::default();

        for t in 0..300 {
            let splits = tree.do_stage_exact_sort(&params, t);

            // For each child bag that receives items from parent
            for level in 1..=tree.max_level {
                if (t + 1 + level) % 2 != 0 { continue; }
                let parent_level = level - 1;
                let parent_cap = params.capacity(n, t, parent_level);

                for idx in 0..(1usize << level) {
                    let fp = from_parent(&splits, level, idx);
                    if fp.is_empty() { continue; }

                    let parent_idx = idx / 2;
                    // Get the parent bag's items BEFORE the split
                    // We need to look at the split result to reconstruct
                    let parent_key = (parent_level, parent_idx);
                    let parent_split = match splits.get(&parent_key) {
                        Some(s) => s,
                        None => continue,
                    };

                    // Reconstruct parent bag items (sorted)
                    let mut parent_items: Vec<usize> = Vec::new();
                    parent_items.extend_from_slice(&parent_split.to_parent);
                    parent_items.extend_from_slice(&parent_split.to_left_child);
                    parent_items.extend_from_slice(&parent_split.to_right_child);
                    parent_items.sort();

                    let b = parent_items.len();
                    if b == 0 { continue; }

                    // Decompose
                    let (s_lo, n_l, n_r, s_hi, _cb) = decompose_parent(
                        n, &parent_items, parent_level, parent_idx,
                    );

                    let c = s_lo + n_l;
                    let half_b = b / 2;

                    // Validate formula
                    let (formula, actual_sn, matches) = validate_formula(
                        &tree, &fp, &parent_items, parent_level, parent_idx, level, idx,
                    );
                    if !matches {
                        local.total_formula_mismatch += 1;
                        global.total_formula_mismatch += 1;
                    }
                    local.total_sn += actual_sn;
                    global.total_sn += actual_sn;

                    if actual_sn > 0 && parent_cap > 0.001 {
                        let sn_ratio = actual_sn as f64 / (cnc * parent_cap);
                        if sn_ratio > local.max_deviation_ratio {
                            local.max_deviation_ratio = sn_ratio;
                        }
                        if sn_ratio > global.max_deviation_ratio {
                            global.max_deviation_ratio = sn_ratio;
                            global.max_deviation_detail = format!(
                                "n={} t={} lev={} idx={}: sn={} formula={} b={} s_lo={} n_L={} n_R={} s_hi={} C={} b/2={} cap={:.1}",
                                n, t, level, idx, actual_sn, formula, b, s_lo, n_l, n_r, s_hi, c, half_b, parent_cap,
                            );
                        }
                    }

                    // Track stranger asymmetry and native imbalance
                    if parent_cap > 0.001 {
                        let stranger_asym = (s_lo as f64 - s_hi as f64).abs();
                        let native_imbal = (n_l as f64 - n_r as f64).abs();
                        let deviation = (c as f64 - half_b as f64).abs();

                        let stranger_ratio = stranger_asym / (2.0 * cnc * parent_cap);
                        let native_ratio = native_imbal / (2.0 * cnc * parent_cap);

                        if stranger_ratio > local.max_stranger_contrib {
                            local.max_stranger_contrib = stranger_ratio;
                        }
                        if native_ratio > local.max_native_contrib {
                            local.max_native_contrib = native_ratio;
                        }
                        if stranger_ratio > global.max_stranger_contrib {
                            global.max_stranger_contrib = stranger_ratio;
                        }
                        if native_ratio > global.max_native_contrib {
                            global.max_native_contrib = native_ratio;
                        }

                        let s_asym_ratio = if params.lambda * parent_cap > 0.1 {
                            stranger_asym / (params.lambda * parent_cap)
                        } else { 0.0 };
                        if s_asym_ratio > local.max_stranger_asymmetry_ratio {
                            local.max_stranger_asymmetry_ratio = s_asym_ratio;
                        }
                        if s_asym_ratio > global.max_stranger_asymmetry_ratio {
                            global.max_stranger_asymmetry_ratio = s_asym_ratio;
                        }

                        let ni_ratio = native_imbal / parent_cap;
                        if ni_ratio > local.max_native_imbalance_ratio {
                            local.max_native_imbalance_ratio = ni_ratio;
                        }
                        if ni_ratio > global.max_native_imbalance_ratio {
                            global.max_native_imbalance_ratio = ni_ratio;
                            global.max_native_imbalance_detail = format!(
                                "n={} t={} lev={} idx={}: |n_L-n_R|={} cap={:.1} s_lo={} s_hi={} n_L={} n_R={} b={}",
                                n, t, level, idx, (n_l as isize - n_r as isize).unsigned_abs(),
                                parent_cap, s_lo, s_hi, n_l, n_r, b,
                            );
                        }
                    }
                }
            }

            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < threshold { break; }
        }

        println!("n={:5}: sn={:6}  mismatch={:3}  sn_ratio={:.6}  stranger_c={:.6}  native_c={:.6}  s_asym={:.6}  n_imbal={:.6}",
            n, local.total_sn, local.total_formula_mismatch,
            local.max_deviation_ratio,
            local.max_stranger_contrib, local.max_native_contrib,
            local.max_stranger_asymmetry_ratio, local.max_native_imbalance_ratio);
    }

    println!();
    println!("=== GLOBAL SUMMARY ===");
    println!("Total sibling-native: {}", global.total_sn);
    println!("Formula mismatches:   {}", global.total_formula_mismatch);
    println!("Max sn/cnc*cap ratio: {:.6} [{}]", global.max_deviation_ratio,
        if global.max_deviation_ratio <= 1.001 { "OK" } else { "FAIL" });
    println!("Max stranger contrib: {:.6} (|s_lo-s_hi| / (2*cnc*cap))", global.max_stranger_contrib);
    println!("Max native contrib:   {:.6} (|n_L-n_R| / (2*cnc*cap))", global.max_native_contrib);
    println!("Max |s_lo-s_hi|/lam*cap: {:.6}", global.max_stranger_asymmetry_ratio);
    println!("Max |n_L-n_R|/cap:    {:.6}", global.max_native_imbalance_ratio);
    println!();
    if !global.max_deviation_detail.is_empty() {
        println!("Worst sn case: {}", global.max_deviation_detail);
    }
    if !global.max_native_imbalance_detail.is_empty() {
        println!("Worst native imbalance: {}", global.max_native_imbalance_detail);
    }
}
