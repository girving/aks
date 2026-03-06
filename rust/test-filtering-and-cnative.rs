#!/usr/bin/env -S cargo +nightly -Zscript
//! Experiments A, B, C: Deep diagnostics for fromParent_stranger_filtered
//! and cnative_from_parent_bound.
//!
//! Experiment A: Test the filtering bound directly
//!   For each (level, idx, j), compute:
//!     strangers_in_fromParent(level, idx, j) / (ε × strangers_in_parent_bag(level-1, idx/2, j))
//!   If this exceeds 1, then fromParent_stranger_filtered is FALSE as stated.
//!
//! Experiment B: Decompose cnative into three sub-sources
//!   For each sibling-native item in fromParent, classify by source:
//!     (b) Halving error: item is C-native (native to parent) but placed on wrong child side
//!     (c) Subtree stranger: item is a j-stranger (j≥2) at some ancestor level
//!     (d) Above-parent: item's native bag is NOT the parent bag (arrived from above)
//!
//! Experiment C: Measure fromParent strangeness distribution
//!   For items in fromParent(level, idx):
//!     - How many are j-strangers at parent level for each j?
//!     - What fraction of parent's j-strangers end up in each child?
//!
//! Usage: cargo +nightly -Zscript rust/test-filtering-and-cnative.rs

use std::collections::{BTreeMap, BTreeSet};

// ──────────────────────────────────────────────────────────────────────
// Infrastructure (copied from test-split-hypotheses.rs)
// ──────────────────────────────────────────────────────────────────────

#[derive(Clone, Debug)]
struct Params {
    a: f64,
    nu: f64,
    lambda: f64,
    eps: f64,
}

impl Params {
    fn seiferas_preview() -> Self {
        Params { a: 10.0, nu: 0.65, lambda: 1.0/99.0, eps: 1.0/99.0 }
    }

    fn capacity(&self, n: usize, t: usize, level: usize) -> f64 {
        (n as f64) * self.nu.powi(t as i32) * self.a.powi(level as i32)
    }

    fn cnative_coeff(&self) -> f64 {
        let a = self.a;
        let e = self.eps;
        let l = self.lambda;
        e / 2.0
            + 2.0 * l * e * a.powi(2) / (1.0 - (2.0 * e * a).powi(2))
            + 1.0 / (8.0 * a.powi(2) - 2.0)
    }
}

#[derive(Clone, Copy)]
enum SepModel {
    Adversarial { lambda: f64 },
}

fn apply_separator(items: &mut Vec<usize>, model: SepModel, eps: f64, _rng: &mut Rng) {
    items.sort();
    match model {
        SepModel::Adversarial { lambda } => {
            let m = items.len();
            if m <= 1 { return; }
            let fringe = (lambda * m as f64).floor() as usize;
            let middle_start = fringe;
            let middle_end = m.saturating_sub(fringe);
            let middle_size = middle_end.saturating_sub(middle_start);
            let half = middle_size / 2;
            let halving_errors = (eps * half as f64).floor() as usize;
            if halving_errors > 0 && half > 0 {
                for k in 0..halving_errors.min(half) {
                    let left_pos = middle_start + half - 1 - k;
                    let right_pos = middle_start + half + k;
                    if left_pos < right_pos && right_pos < middle_end {
                        items.swap(left_pos, right_pos);
                    }
                }
            }
            let fringe_errors = (eps * fringe as f64).floor() as usize;
            if fringe_errors > 0 && fringe > 0 && middle_size > 2 * halving_errors {
                let avail = (half.saturating_sub(halving_errors)).min(fringe_errors);
                for k in 0..avail {
                    items.swap(fringe - 1 - k, middle_start + k);
                }
                for k in 0..avail {
                    let right_fringe_pos = middle_end + k;
                    let right_mid_pos = middle_end - 1 - k;
                    if right_fringe_pos < m && right_mid_pos >= middle_start + half {
                        items.swap(right_fringe_pos, right_mid_pos);
                    }
                }
            }
        }
    }
}

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Rng(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
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

    fn native_bag_idx(&self, level: usize, rank: usize) -> usize {
        let chunk_size = self.n >> level;
        if chunk_size == 0 { rank } else { rank / chunk_size }
    }

    fn is_j_stranger(&self, rank: usize, level: usize, idx: usize, j: usize) -> bool {
        if j == 0 || j > level { return false; }
        let check_level = level - (j - 1);
        let check_idx = idx >> (j - 1);
        self.native_bag_idx(check_level, rank) != check_idx
    }

    fn j_stranger_count(&self, items: &[usize], level: usize, idx: usize, j: usize) -> usize {
        items.iter().filter(|&&rank| self.is_j_stranger(rank, level, idx, j)).count()
    }

    fn sibling_native_count(&self, items: &[usize], level: usize, idx: usize) -> usize {
        items.iter().filter(|&&rank| {
            self.is_j_stranger(rank, level, idx, 1) &&
            !self.is_j_stranger(rank, level, idx, 2)
        }).count()
    }

    fn do_stage_with_splits(&mut self, params: &Params, t: usize, model: SepModel, rng: &mut Rng)
        -> BTreeMap<(usize, usize), SplitResult>
    {
        let mut splits: BTreeMap<(usize, usize), SplitResult> = BTreeMap::new();
        let mut new_bags: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();

        let active: Vec<((usize, usize), Vec<usize>)> = self.bags.iter()
            .filter(|(_, items)| !items.is_empty())
            .map(|(&k, v)| (k, v.clone()))
            .collect();

        for ((level, idx), mut items) in active {
            apply_separator(&mut items, model, params.eps, rng);

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

// ──────────────────────────────────────────────────────────────────────
// Experiment A: Test fromParent_stranger_filtered
// ──────────────────────────────────────────────────────────────────────

fn experiment_a() {
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║  Experiment A: fromParent_stranger_filtered                 ║");
    println!("║                                                            ║");
    println!("║  Tests: jStrangerCount(fromParent, l-1, i/2, j)            ║");
    println!("║         ≤ ε × jStrangerCount(parent_bag, l-1, i/2, j)     ║");
    println!("║                                                            ║");
    println!("║  Ratio > 1 means the statement is FALSE.                   ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
    println!();

    let params = Params::seiferas_preview();
    let model = SepModel::Adversarial { lambda: params.lambda };

    // Track max ratio for each j
    let max_j = 16;
    let mut global_max_ratios = vec![0.0f64; max_j + 1];
    let mut global_max_details: Vec<String> = vec![String::new(); max_j + 1];
    let mut parent_zero_but_child_nonzero = 0usize; // cases where denominator=0 but numerator>0

    for exp in 3..=14 {
        let n = 1usize << exp;
        let mut tree = BagTree::new(n);
        let mut rng = Rng::new(42);
        let threshold = 2.0;
        let mut max_ratios_n = vec![0.0f64; max_j + 1];

        for t in 0..300 {
            // Save old bags to know parent bag contents
            let old_bags = tree.bags.clone();
            let splits = tree.do_stage_with_splits(&params, t, model, &mut rng);

            // For each child bag receiving fromParent items:
            for level in 1..=tree.max_level {
                if (t + 1 + level) % 2 != 0 { continue; } // skip inactive
                let parent_level = level - 1;

                for idx in 0..(1usize << level) {
                    let fp = from_parent(&splits, level, idx);
                    if fp.is_empty() { continue; }

                    let parent_idx = idx / 2;
                    let parent_bag = match old_bags.get(&(parent_level, parent_idx)) {
                        Some(v) => v.clone(),
                        None => vec![],
                    };

                    // Test for each j
                    for j in 1..=parent_level.min(max_j) {
                        let fp_strangers = tree.j_stranger_count(&fp, parent_level, parent_idx, j);
                        let parent_strangers = tree.j_stranger_count(&parent_bag, parent_level, parent_idx, j);

                        if parent_strangers == 0 {
                            if fp_strangers > 0 {
                                parent_zero_but_child_nonzero += 1;
                            }
                            continue;
                        }

                        let ratio = fp_strangers as f64 / (params.eps * parent_strangers as f64);
                        if ratio > max_ratios_n[j] {
                            max_ratios_n[j] = ratio;
                        }
                        if ratio > global_max_ratios[j] {
                            global_max_ratios[j] = ratio;
                            global_max_details[j] = format!(
                                "n={} t={} lev={} idx={} j={}: fp_str={} / (ε·parent_str={}) = {:.4}",
                                n, t, level, idx, j, fp_strangers, parent_strangers, ratio
                            );
                        }
                    }
                }
            }

            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < threshold { break; }
        }

        // Print per-n summary
        let max_over_j = max_ratios_n[1..].iter().cloned().fold(0.0f64, f64::max);
        let status = if max_over_j <= 1.001 { "OK" } else { "FAIL" };
        print!("  n={:5}: max_ratio={:.4} [{}]  by j:", n, max_over_j, status);
        for j in 1..=5.min(tree.max_level) {
            if max_ratios_n[j] > 0.001 {
                print!("  j{}={:.4}", j, max_ratios_n[j]);
            }
        }
        println!();
    }

    println!();
    println!("  Global max ratios by j:");
    for j in 1..=max_j {
        if global_max_ratios[j] > 0.0 {
            let status = if global_max_ratios[j] <= 1.001 { "OK" } else { "FAIL" };
            println!("    j={:2}: {:.6} [{}]  {}", j, global_max_ratios[j], status,
                &global_max_details[j]);
        }
    }
    if parent_zero_but_child_nonzero > 0 {
        println!("  WARNING: {} cases where parent had 0 j-strangers but fromParent had >0",
            parent_zero_but_child_nonzero);
    }
    println!();
}

// ──────────────────────────────────────────────────────────────────────
// Experiment B: Decompose cnative into three sub-sources
// ──────────────────────────────────────────────────────────────────────

fn experiment_b() {
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║  Experiment B: cnative three-source decomposition           ║");
    println!("║                                                            ║");
    println!("║  For each sibling-native item in fromParent, classify:      ║");
    println!("║    (b) halving error: C-native but wrong child side         ║");
    println!("║    (c) subtree stranger: ≥2-stranger at parent level        ║");
    println!("║    (d) above-parent: not native to parent bag               ║");
    println!("║                                                            ║");
    println!("║  Tests individual sub-source bounds vs theoretical coeffs.  ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
    println!();

    let params = Params::seiferas_preview();
    let model = SepModel::Adversarial { lambda: params.lambda };
    let cnc = params.cnative_coeff();

    // Theoretical sub-coefficients
    let coeff_b = params.eps / 2.0;
    let coeff_c = 2.0 * params.lambda * params.eps * params.a.powi(2)
        / (1.0 - (2.0 * params.eps * params.a).powi(2));
    let coeff_d = 1.0 / (8.0 * params.a.powi(2) - 2.0);

    println!("  cnativeCoeff = {:.8} = {:.8} + {:.8} + {:.8}",
        cnc, coeff_b, coeff_c, coeff_d);
    println!("    (b) halving: ε/2 = {:.8}", coeff_b);
    println!("    (c) subtree: 2λεA²/(1-(2εA)²) = {:.8}", coeff_c);
    println!("    (d) above:   1/(8A²-2) = {:.8}", coeff_d);
    println!();

    // Global trackers
    let mut global_max_total: f64 = 0.0;
    let mut global_max_b: f64 = 0.0;
    let mut global_max_c: f64 = 0.0;
    let mut global_max_d: f64 = 0.0;
    let mut global_total_items: [usize; 4] = [0; 4]; // [total, b, c, d]
    let mut unclassified_count = 0usize;

    for exp in 3..=14 {
        let n = 1usize << exp;
        let mut tree = BagTree::new(n);
        let mut rng = Rng::new(42);
        let threshold = 2.0;

        let mut max_ratio_total: f64 = 0.0;
        let mut max_ratio_b: f64 = 0.0;
        let mut max_ratio_c: f64 = 0.0;
        let mut max_ratio_d: f64 = 0.0;
        let mut count_b = 0usize;
        let mut count_c = 0usize;
        let mut count_d = 0usize;
        let mut count_total = 0usize;
        let mut unclassified_n = 0usize;

        for t in 0..300 {
            let old_bags = tree.bags.clone();
            let splits = tree.do_stage_with_splits(&params, t, model, &mut rng);

            for level in 1..=tree.max_level {
                if (t + 1 + level) % 2 != 0 { continue; }
                let parent_level = level - 1;
                let parent_cap = params.capacity(n, t, parent_level);

                for idx in 0..(1usize << level) {
                    let fp = from_parent(&splits, level, idx);
                    if fp.is_empty() { continue; }

                    let parent_idx = idx / 2;
                    let sibling_idx = if idx % 2 == 0 { idx + 1 } else { idx - 1 };

                    // Classify each sibling-native item in fromParent
                    let mut local_b = 0usize;
                    let mut local_c = 0usize;
                    let mut local_d = 0usize;
                    let mut local_total = 0usize;
                    let mut local_unclassified = 0usize;

                    for &rank in &fp {
                        // Is it sibling-native? (1-stranger but not 2-stranger at (level, idx))
                        let is_1stranger = tree.is_j_stranger(rank, level, idx, 1);
                        let is_2stranger = tree.is_j_stranger(rank, level, idx, 2);
                        if !is_1stranger || is_2stranger { continue; }

                        // Sibling-native: native to parent bag, native to sibling child,
                        // NOT native to this child
                        local_total += 1;

                        // Check which sub-source:
                        // Item's native bag at parent level
                        let native_at_parent = tree.native_bag_idx(parent_level, rank);
                        let native_at_child = tree.native_bag_idx(level, rank);

                        if native_at_parent != parent_idx {
                            // (d) Not native to parent: arrived from above
                            local_d += 1;
                        } else if native_at_child == sibling_idx {
                            // Native to parent AND native to sibling child
                            // Was it a j-stranger (j≥2) somewhere in the subtree?
                            // Check: is it a 2-stranger at the parent level?
                            // (i.e., not native to grandparent)
                            let is_2stranger_at_parent = if parent_level >= 2 {
                                tree.is_j_stranger(rank, parent_level, parent_idx, 2)
                            } else {
                                false
                            };

                            if is_2stranger_at_parent {
                                // (c) Subtree stranger: native to parent but stranger
                                // at grandparent or higher — accumulated through subtree
                                local_c += 1;
                            } else {
                                // (b) Halving error: native to parent, native to sibling,
                                // NOT a deeper stranger — the separator put it on the wrong side
                                local_b += 1;
                            }
                        } else {
                            // Native to parent but not native to either child?
                            // This shouldn't happen for power-of-2 n
                            local_unclassified += 1;
                        }
                    }

                    count_total += local_total;
                    count_b += local_b;
                    count_c += local_c;
                    count_d += local_d;
                    unclassified_n += local_unclassified;

                    // Compute ratios against theoretical bounds
                    if parent_cap > 0.001 {
                        let r_total = local_total as f64 / (cnc * parent_cap);
                        if r_total > max_ratio_total { max_ratio_total = r_total; }

                        let r_b = local_b as f64 / (coeff_b * parent_cap);
                        if coeff_b * parent_cap > 0.001 && r_b > max_ratio_b { max_ratio_b = r_b; }

                        let r_c = local_c as f64 / (coeff_c * parent_cap);
                        if coeff_c * parent_cap > 0.001 && r_c > max_ratio_c { max_ratio_c = r_c; }

                        let r_d = local_d as f64 / (coeff_d * parent_cap);
                        if coeff_d * parent_cap > 0.001 && r_d > max_ratio_d { max_ratio_d = r_d; }
                    }
                }
            }

            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < threshold { break; }
        }

        let status = if max_ratio_total <= 1.001 { "OK" } else { "FAIL" };
        println!("  n={:5}: total={:.4} [{}]  (b)halv={:.4}  (c)sub={:.4}  (d)above={:.4}  counts: b={} c={} d={} unc={}",
            n, max_ratio_total, status, max_ratio_b, max_ratio_c, max_ratio_d,
            count_b, count_c, count_d, unclassified_n);

        global_total_items[0] += count_total;
        global_total_items[1] += count_b;
        global_total_items[2] += count_c;
        global_total_items[3] += count_d;
        unclassified_count += unclassified_n;

        if max_ratio_total > global_max_total { global_max_total = max_ratio_total; }
        if max_ratio_b > global_max_b { global_max_b = max_ratio_b; }
        if max_ratio_c > global_max_c { global_max_c = max_ratio_c; }
        if max_ratio_d > global_max_d { global_max_d = max_ratio_d; }
    }

    println!();
    println!("  Global max ratios:");
    println!("    total (vs cnativeCoeff): {:.6} [{}]", global_max_total,
        if global_max_total <= 1.001 { "OK" } else { "FAIL" });
    println!("    (b) halving (vs ε/2): {:.6} [{}]", global_max_b,
        if global_max_b <= 1.001 { "OK" } else { "FAIL" });
    println!("    (c) subtree (vs 2λεA²/(1-(2εA)²)): {:.6} [{}]", global_max_c,
        if global_max_c <= 1.001 { "OK" } else { "FAIL" });
    println!("    (d) above (vs 1/(8A²-2)): {:.6} [{}]", global_max_d,
        if global_max_d <= 1.001 { "OK" } else { "FAIL" });
    println!("  Global counts: total={} b={} c={} d={} unclassified={}",
        global_total_items[0], global_total_items[1], global_total_items[2],
        global_total_items[3], unclassified_count);
    println!();
}

// ──────────────────────────────────────────────────────────────────────
// Experiment C: fromParent strangeness distribution by j
// ──────────────────────────────────────────────────────────────────────

fn experiment_c() {
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║  Experiment C: fromParent strangeness distribution          ║");
    println!("║                                                            ║");
    println!("║  For items in fromParent(level, idx), measure:              ║");
    println!("║    - j-stranger count at parent level for each j            ║");
    println!("║    - Fraction of parent's j-strangers ending in each child  ║");
    println!("║    - Compare: does left child ≈ right child?                ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
    println!();

    let params = Params::seiferas_preview();
    let model = SepModel::Adversarial { lambda: params.lambda };

    let max_j = 8;

    for &n in &[256, 1024, 4096, 16384] {
        let mut tree = BagTree::new(n);
        let mut rng = Rng::new(42);
        let threshold = 2.0;
        let tree_max_level = tree.max_level;

        // Track: for each j, total parent strangers, total in left child, total in right child
        let mut parent_total = vec![0usize; max_j + 1];
        let mut child_left = vec![0usize; max_j + 1];
        let mut child_right = vec![0usize; max_j + 1];

        // Also track: max ratio of (fp_strangers / parent_strangers) per j
        let mut max_fraction = vec![0.0f64; max_j + 1];
        let mut sample_count = 0usize;

        for t in 0..300 {
            let old_bags = tree.bags.clone();
            let splits = tree.do_stage_with_splits(&params, t, model, &mut rng);

            // For each parent bag that was split:
            for (&(level, idx), split) in &splits {
                if level == 0 || level >= tree_max_level { continue; }
                let old_items = match old_bags.get(&(level, idx)) {
                    Some(v) if !v.is_empty() => v,
                    _ => continue,
                };

                sample_count += 1;

                for j in 1..=level.min(max_j) {
                    // Strangers in the full parent bag
                    let parent_str: BTreeSet<usize> = old_items.iter()
                        .filter(|&&rank| tree.is_j_stranger(rank, level, idx, j))
                        .copied().collect();

                    if parent_str.is_empty() { continue; }
                    parent_total[j] += parent_str.len();

                    // How many of those strangers ended up in left child?
                    let in_left = split.to_left_child.iter()
                        .filter(|r| parent_str.contains(r)).count();
                    let in_right = split.to_right_child.iter()
                        .filter(|r| parent_str.contains(r)).count();

                    child_left[j] += in_left;
                    child_right[j] += in_right;

                    // Fraction going to each child
                    let total_to_children = in_left + in_right;
                    let frac = total_to_children as f64 / parent_str.len() as f64;
                    if frac > max_fraction[j] { max_fraction[j] = frac; }
                }
            }

            let leaf_cap = params.capacity(n, t + 1, tree_max_level);
            if leaf_cap < threshold { break; }
        }

        println!("  n={} ({} parent bags sampled):", n, sample_count);
        println!("    {:>4} {:>12} {:>10} {:>10} {:>10} {:>10} {:>10}",
            "j", "parent_str", "to_left", "to_right", "%_left", "%_right", "max_frac");
        for j in 1..=max_j {
            if parent_total[j] == 0 { continue; }
            let pt = parent_total[j] as f64;
            println!("    {:>4} {:>12} {:>10} {:>10} {:>9.1}% {:>9.1}% {:>10.6}",
                j, parent_total[j], child_left[j], child_right[j],
                100.0 * child_left[j] as f64 / pt,
                100.0 * child_right[j] as f64 / pt,
                max_fraction[j]);
        }
        println!();
    }
}

// ──────────────────────────────────────────────────────────────────────
// Experiment D: Alternative formulation — test at CHILD level
//
// The Lean statement says:
//   jStrangerCount(fromParent, l-1, i/2, j) ≤ ε × jStrangerCount(parent_bag, l-1, i/2, j)
//
// But maybe the correct formulation uses child-level stranger counts
// via the level shift? Let's test alternatives:
//
//   Alt 1: jStrangerCount(fromParent, level, idx, j+1) ≤ ε × jStrangerCount(parent_bag, level-1, parent_idx, j)
//   Alt 2: The bound uses subset monotonicity only (no ε): fromParent ⊆ split.toLeft ⊆ bags
//   Alt 3: The ε factor comes from the separator not the stranger count
// ──────────────────────────────────────────────────────────────────────

fn experiment_d() {
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║  Experiment D: Alternative formulations                     ║");
    println!("║                                                            ║");
    println!("║  Test whether ε filtering is even needed, or if subset      ║");
    println!("║  monotonicity alone suffices (since fromParent comes from   ║");
    println!("║  parent's toLeftChild/toRightChild, not the whole bag).     ║");
    println!("║                                                            ║");
    println!("║  Measures:                                                  ║");
    println!("║    R1: fp_str / parent_bag_str (subset monotonicity: ≤ 1)   ║");
    println!("║    R2: fp_str / (ε × parent_bag_str) (filtering: ≤ 1?)     ║");
    println!("║    R3: fp_str / (0.5 × parent_bag_str) (half: ≤ 1?)        ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
    println!();

    let params = Params::seiferas_preview();
    let model = SepModel::Adversarial { lambda: params.lambda };

    let max_j = 8;

    for &n in &[256, 1024, 4096, 16384] {
        let mut tree = BagTree::new(n);
        let mut rng = Rng::new(42);
        let threshold = 2.0;

        let mut max_r1 = vec![0.0f64; max_j + 1]; // subset monotonicity
        let mut max_r2 = vec![0.0f64; max_j + 1]; // ε filtering
        let mut max_r3 = vec![0.0f64; max_j + 1]; // half

        for t in 0..300 {
            let old_bags = tree.bags.clone();
            let splits = tree.do_stage_with_splits(&params, t, model, &mut rng);

            for level in 1..=tree.max_level {
                if (t + 1 + level) % 2 != 0 { continue; }

                for idx in 0..(1usize << level) {
                    let fp = from_parent(&splits, level, idx);
                    if fp.is_empty() { continue; }

                    let parent_level = level - 1;
                    let parent_idx = idx / 2;
                    let parent_bag = match old_bags.get(&(parent_level, parent_idx)) {
                        Some(v) => v.clone(),
                        None => vec![],
                    };

                    for j in 1..=parent_level.min(max_j) {
                        let fp_str = tree.j_stranger_count(&fp, parent_level, parent_idx, j);
                        let parent_str = tree.j_stranger_count(&parent_bag, parent_level, parent_idx, j);

                        if parent_str == 0 { continue; }

                        let r1 = fp_str as f64 / parent_str as f64;
                        let r2 = fp_str as f64 / (params.eps * parent_str as f64);
                        let r3 = fp_str as f64 / (0.5 * parent_str as f64);

                        if r1 > max_r1[j] { max_r1[j] = r1; }
                        if r2 > max_r2[j] { max_r2[j] = r2; }
                        if r3 > max_r3[j] { max_r3[j] = r3; }
                    }
                }
            }

            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < threshold { break; }
        }

        println!("  n={}:", n);
        println!("    {:>4} {:>12} {:>12} {:>12}", "j", "R1(⊆)", "R2(ε·)", "R3(½·)");
        for j in 1..=max_j {
            if max_r1[j] > 0.0 || max_r2[j] > 0.0 {
                let s1 = if max_r1[j] <= 1.001 { "OK" } else { "!!" };
                let s2 = if max_r2[j] <= 1.001 { "OK" } else { "!!" };
                let s3 = if max_r3[j] <= 1.001 { "OK" } else { "!!" };
                println!("    {:>4} {:>10.6} {} {:>10.6} {} {:>10.6} {}",
                    j, max_r1[j], s1, max_r2[j], s2, max_r3[j], s3);
            }
        }
        println!();
    }
}

fn main() {
    experiment_a();
    experiment_b();
    experiment_c();
    experiment_d();
}
// Note: multi-seed test is in the main test file (test-split-hypotheses.rs)
// and already confirmed robustness. These results are stable.
