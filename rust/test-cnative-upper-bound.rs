#!/usr/bin/env -S cargo +nightly -Zscript
//! Validate that siblingNativeCount ≤ max(0, ⌊b/2⌋ - C) always holds.
//! Also validate the decomposition: |C - b/2| ≤ (|n_L - n_R| + s_lo + s_hi) / 2.
//! And validate: (|n_L - n_R| + s_lo + s_hi) / 2 ≤ cnativeCoeff * cap(parent).

use std::collections::BTreeMap;

struct Params {
    a: f64, nu: f64, lambda: f64, eps: f64,
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
            + 2.0 * self.lambda * self.eps * self.a.powi(2)
                / (1.0 - (2.0 * self.eps * self.a).powi(2))
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

    fn bag_size(&self, level: usize) -> usize { self.n >> level }

    fn native_bag_idx(&self, level: usize, rank: usize) -> usize {
        let cs = self.bag_size(level);
        if cs == 0 { rank } else { rank / cs }
    }

    fn is_j_stranger(&self, rank: usize, level: usize, idx: usize, j: usize) -> bool {
        if j == 0 || j > level { return false; }
        self.native_bag_idx(level - (j - 1), rank) != idx >> (j - 1)
    }

    fn sibling_native_count(&self, items: &[usize], level: usize, idx: usize) -> usize {
        items.iter().filter(|&&r| {
            self.is_j_stranger(r, level, idx, 1) && !self.is_j_stranger(r, level, idx, 2)
        }).count()
    }

    fn do_stage(&mut self, params: &Params, t: usize) -> BTreeMap<(usize, usize), SplitResult> {
        let mut splits = BTreeMap::new();
        let mut new_bags: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();
        let active: Vec<_> = self.bags.iter()
            .filter(|(_, v)| !v.is_empty()).map(|(&k, v)| (k, v.clone())).collect();
        for ((level, idx), mut items) in active {
            items.sort();
            let b = params.capacity(self.n, t, level);
            let f = (params.lambda * b).floor() as usize;
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
                let ks = f.min(total);
                let kl = f.min(total.saturating_sub(ks));
                split.to_parent.extend_from_slice(&items[..ks]);
                split.to_parent.extend_from_slice(&items[total - kl..]);
                let mut middle: Vec<usize> = items[ks..total - kl].to_vec();
                if middle.len() % 2 == 1 {
                    let mi = middle.len() / 2;
                    split.to_parent.push(middle.remove(mi));
                }
                let half = middle.len() / 2;
                split.to_left_child = middle[..half].to_vec();
                split.to_right_child = middle[half..].to_vec();
            }
            if has_parent { new_bags.entry((level-1, idx/2)).or_default().extend(&split.to_parent); }
            if has_children {
                new_bags.entry((level+1, 2*idx)).or_default().extend(&split.to_left_child);
                new_bags.entry((level+1, 2*idx+1)).or_default().extend(&split.to_right_child);
            }
            splits.insert((level, idx), split);
        }
        self.bags = new_bags;
        splits
    }
}

fn from_parent(splits: &BTreeMap<(usize, usize), SplitResult>, level: usize, idx: usize) -> Vec<usize> {
    if level == 0 { return vec![]; }
    match splits.get(&(level-1, idx/2)) {
        Some(s) => if idx % 2 == 0 { s.to_left_child.clone() } else { s.to_right_child.clone() },
        None => vec![],
    }
}

fn main() {
    let params = Params::seiferas();
    let cnc = params.cnative_coeff();

    let mut violations_ub = 0usize;       // formula < actual (would be BAD)
    let mut violations_decomp = 0usize;   // triangle inequality fails (impossible)
    let mut violations_bound = 0usize;    // decomposition > cnc * cap (BAD)
    let mut total_checks = 0usize;

    for exp in 3..=14 {
        let n = 1usize << exp;
        let mut tree = BagTree::new(n);
        for t in 0..300 {
            let splits = tree.do_stage(&params, t);
            for level in 1..=tree.max_level {
                if (t + 1 + level) % 2 != 0 { continue; }
                for idx in 0..(1usize << level) {
                    let fp = from_parent(&splits, level, idx);
                    if fp.is_empty() { continue; }
                    let pkey = (level-1, idx/2);
                    let ps = match splits.get(&pkey) { Some(s) => s, None => continue };
                    let mut parent_items: Vec<usize> = Vec::new();
                    parent_items.extend(&ps.to_parent);
                    parent_items.extend(&ps.to_left_child);
                    parent_items.extend(&ps.to_right_child);
                    parent_items.sort();
                    let b = parent_items.len();
                    if b == 0 { continue; }

                    let pidx = idx / 2;
                    let bs = n >> (level - 1);
                    let boundary = pidx * bs + bs / 2;

                    let mut s_lo = 0usize;
                    let mut n_l = 0usize;
                    let mut n_r = 0usize;
                    let mut s_hi = 0usize;
                    for &r in &parent_items {
                        if r < pidx * bs { s_lo += 1; }
                        else if r < boundary { n_l += 1; }
                        else if r < (pidx + 1) * bs { n_r += 1; }
                        else { s_hi += 1; }
                    }

                    let c = s_lo + n_l;
                    let half_b = b / 2;
                    let actual_sn = tree.sibling_native_count(&fp, level, idx);

                    // Check 1: formula ≥ actual
                    let formula = if idx % 2 == 0 {
                        half_b.saturating_sub(c)
                    } else {
                        c.saturating_sub(half_b)
                    };
                    if formula < actual_sn {
                        violations_ub += 1;
                        eprintln!("UB VIOLATION: n={n} t={t} lev={level} idx={idx}: formula={formula} actual={actual_sn} b={b} C={c}");
                    }

                    // Check 2: |C - b/2| ≤ (|n_L - n_R| + s_lo + s_hi) / 2
                    let dev = (c as isize - half_b as isize).unsigned_abs();
                    let native_imbal = (n_l as isize - n_r as isize).unsigned_abs();
                    let triangle = (native_imbal + s_lo + s_hi) / 2;
                    // Note: integer division can round down. Use ceiling.
                    let triangle_ceil = (native_imbal + s_lo + s_hi + 1) / 2;
                    if dev > triangle_ceil {
                        violations_decomp += 1;
                    }

                    // Check 3: (|n_L - n_R| + s_lo + s_hi) / 2 ≤ cnc * cap
                    let cap = params.capacity(n, t, level - 1);
                    if cap > 0.001 {
                        let upper = (native_imbal + s_lo + s_hi) as f64 / 2.0;
                        if upper > cnc * cap * 1.001 {
                            violations_bound += 1;
                        }
                    }

                    total_checks += 1;
                }
            }
            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < 2.0 { break; }
        }
    }

    println!("Total checks:        {total_checks}");
    println!("UB violations:       {violations_ub}    (formula < actual: MUST be 0)");
    println!("Decomp violations:   {violations_decomp} (triangle ineq: MUST be 0)");
    println!("Bound violations:    {violations_bound}  (decomp > cnc*cap: MUST be 0)");

    if violations_ub == 0 && violations_bound == 0 {
        println!("\nAll sub-lemma statements VALIDATED.");
    } else {
        println!("\nFAILURES DETECTED!");
    }
}
