#!/usr/bin/env -S cargo +nightly -Zscript
//! Quick test: is siblingNativeCount = 0 when using exact sorting (no adversarial errors)?
//! This matches the Lean concreteSplit which uses rankInBag perm (true sorted rank).

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

    fn sibling_native_count(&self, items: &[usize], level: usize, idx: usize) -> usize {
        items.iter().filter(|&&rank| {
            self.is_j_stranger(rank, level, idx, 1) &&
            !self.is_j_stranger(rank, level, idx, 2)
        }).count()
    }

    // Exact sort split: matches Lean concreteSplit (rankInBag perm)
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
            // EXACT sort — no adversarial errors
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

fn main() {
    let params = Params::seiferas();
    let cnc = params.cnative_coeff();
    println!("cnativeCoeff = {:.8}", cnc);
    println!();

    let mut total_sibling_native = 0usize;
    let mut max_ratio = 0.0f64;
    let mut max_detail = String::new();

    for exp in 3..=14 {
        let n = 1usize << exp;
        let mut tree = BagTree::new(n);
        let threshold = 2.0;
        let mut n_sibling_native = 0usize;
        let mut n_max_ratio = 0.0f64;

        for t in 0..300 {
            let splits = tree.do_stage_exact_sort(&params, t);

            for level in 1..=tree.max_level {
                if (t + 1 + level) % 2 != 0 { continue; }
                let parent_level = level - 1;
                let parent_cap = params.capacity(n, t, parent_level);

                for idx in 0..(1usize << level) {
                    let fp = from_parent(&splits, level, idx);
                    if fp.is_empty() { continue; }

                    let sc = tree.sibling_native_count(&fp, level, idx);
                    if sc > 0 {
                        n_sibling_native += sc;
                        total_sibling_native += sc;

                        if parent_cap > 0.001 {
                            let ratio = sc as f64 / (cnc * parent_cap);
                            if ratio > n_max_ratio { n_max_ratio = ratio; }
                            if ratio > max_ratio {
                                max_ratio = ratio;
                                max_detail = format!(
                                    "n={} t={} lev={} idx={}: sc={} cap={:.2} ratio={:.6}",
                                    n, t, level, idx, sc, parent_cap, ratio
                                );
                            }
                        }
                    }
                }
            }

            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < threshold { break; }
        }

        let status = if n_max_ratio <= 1.001 { "OK" } else { "FAIL" };
        println!("  n={:5}: sibling_native={:6}  max_ratio={:.6} [{}]",
            n, n_sibling_native, n_max_ratio, status);
    }

    println!();
    println!("  Total sibling-native items (exact sort): {}", total_sibling_native);
    println!("  Global max ratio: {:.6} [{}]", max_ratio,
        if max_ratio <= 1.001 { "OK" } else { "FAIL" });
    if !max_detail.is_empty() {
        println!("  Worst case: {}", max_detail);
    }
}
