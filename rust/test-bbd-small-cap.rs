#!/usr/bin/env -S cargo +nightly -Zscript
//! Test below_boundary_deviation for ALL nonempty parent bags with random permutations.
//! The theorem says: for any nonempty parent bag B at (level-1, idx/2),
//!   |C - ⌊b/2⌋| ≤ cnativeCoeff * cap(level-1)
//! where C = |{i ∈ B : perm(i) < boundary}|, boundary = midpoint of parent interval.
//!
//! We test with both identity and random permutations.

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

struct BagTree {
    n: usize,
    max_level: usize,
    perm: Vec<usize>,  // perm[register] = sorted_rank
    bags: BTreeMap<(usize, usize), Vec<usize>>,  // bags[level,idx] = set of registers
}

impl BagTree {
    fn new(n: usize, perm: Vec<usize>) -> Self {
        assert!(n.is_power_of_two() && n >= 4);
        assert_eq!(perm.len(), n);
        let max_level = n.trailing_zeros() as usize - 1;
        let mut bags = BTreeMap::new();
        bags.insert((0, 0), (0..n).collect());
        BagTree { n, max_level, perm, bags }
    }

    fn bag_size(&self, level: usize) -> usize { self.n >> level }

    fn rank_in_bag(&self, bag_items: &[usize], reg: usize) -> usize {
        // rank of reg within the bag (by sorted order of perm values)
        bag_items.iter().filter(|&&r| self.perm[r] < self.perm[reg]).count()
    }

    fn do_stage(&mut self, params: &Params, t: usize) {
        let mut new_bags: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();
        let active: Vec<_> = self.bags.iter()
            .filter(|(_, v)| !v.is_empty()).map(|(&k, v)| (k, v.clone())).collect();
        for ((level, idx), items) in active {
            // Sort items by perm value (sorted rank)
            let mut sorted_items = items.clone();
            sorted_items.sort_by_key(|&r| self.perm[r]);

            let b_cap = params.capacity(self.n, t, level);
            let f = (params.lambda * b_cap).floor() as usize;
            let has_parent = level > 0;
            let has_children = level < self.max_level;
            if !has_parent {
                let mid = sorted_items.len() / 2;
                new_bags.entry((level+1, 2*idx)).or_default().extend(&sorted_items[..mid]);
                new_bags.entry((level+1, 2*idx+1)).or_default().extend(&sorted_items[mid..]);
            } else if !has_children {
                new_bags.entry((level-1, idx/2)).or_default().extend(&sorted_items);
            } else {
                let total = sorted_items.len();
                let ks = f.min(total);
                let kl = f.min(total.saturating_sub(ks));
                let mut to_parent = Vec::new();
                to_parent.extend_from_slice(&sorted_items[..ks]);
                to_parent.extend_from_slice(&sorted_items[total - kl..]);
                let mut middle: Vec<usize> = sorted_items[ks..total - kl].to_vec();
                if middle.len() % 2 == 1 {
                    let mi = middle.len() / 2;
                    to_parent.push(middle.remove(mi));
                }
                let half = middle.len() / 2;
                new_bags.entry((level-1, idx/2)).or_default().extend(&to_parent);
                new_bags.entry((level+1, 2*idx)).or_default().extend(&middle[..half]);
                new_bags.entry((level+1, 2*idx+1)).or_default().extend(&middle[half..]);
            }
        }
        self.bags = new_bags;
    }
}

// Simple LCG random number generator
struct Rng { state: u64 }
impl Rng {
    fn new(seed: u64) -> Self { Rng { state: seed } }
    fn next(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state >> 33
    }
    fn shuffle(&mut self, v: &mut [usize]) {
        for i in (1..v.len()).rev() {
            let j = (self.next() as usize) % (i + 1);
            v.swap(i, j);
        }
    }
}

fn run_test(n: usize, perm: &[usize], params: &Params, cnc: f64) -> (usize, usize, usize, String) {
    let mut tree = BagTree::new(n, perm.to_vec());
    let mut violations = 0usize;
    let mut total = 0usize;
    let mut small_cap = 0usize;
    let mut worst_info = String::new();

    for t in 0..500 {
        let bags_snapshot: Vec<_> = tree.bags.iter()
            .filter(|(_, v)| !v.is_empty())
            .map(|(&k, v)| (k, v.clone()))
            .collect();

        for &((plevel, pidx), ref items) in &bags_snapshot {
            let b = items.len();
            if b == 0 { continue; }

            let bs_parent = tree.bag_size(plevel);
            if bs_parent == 0 { continue; }
            let child_level = plevel + 1;
            let bs_child = tree.bag_size(child_level);
            let boundary = pidx * bs_parent + bs_child;

            // C = count of items in B with perm(r) < boundary
            let c = items.iter().filter(|&&r| perm[r] < boundary).count();
            let half_b = b / 2;
            let dev = (c as isize - half_b as isize).unsigned_abs();
            let cap = params.capacity(n, t, plevel);
            let bound = cnc * cap;

            if cap < 100.0 { small_cap += 1; }

            if (dev as f64) > bound + 1e-9 {
                violations += 1;
                if violations <= 5 {
                    worst_info = format!(
                        "n={n} t={t} parent=({plevel},{pidx}) b={b} C={c} dev={dev} cap={cap:.4} bound={bound:.6}"
                    );
                    eprintln!("VIOLATION: {worst_info}");
                }
            }
            total += 1;
        }

        tree.do_stage(params, t);
        let leaf_cap = params.capacity(n, t + 1, tree.max_level);
        if leaf_cap < 0.5 { break; }
    }

    (violations, total, small_cap, worst_info)
}

fn main() {
    let params = Params::seiferas();
    let cnc = params.cnative_coeff();
    println!("cnativeCoeff = {cnc:.6}");

    let mut rng = Rng::new(42);
    let mut total_violations = 0usize;
    let mut total_checks = 0usize;
    let mut total_small = 0usize;

    // Test with random permutations
    for exp in 2..=12 {
        let n = 1usize << exp;
        let num_perms = if n <= 32 { 200 } else if n <= 256 { 50 } else { 10 };

        for trial in 0..num_perms {
            let mut perm: Vec<usize> = (0..n).collect();
            if trial > 0 {
                rng.shuffle(&mut perm);
            }
            // else trial 0 = identity

            let (v, t, s, info) = run_test(n, &perm, &params, cnc);
            total_violations += v;
            total_checks += t;
            total_small += s;
        }
        println!("n={n:5}: done ({num_perms} perms), violations so far: {total_violations}");
    }

    println!("\nTotal checks:      {total_checks}");
    println!("Small cap checks:  {total_small} (cap < 100)");
    println!("Violations:        {total_violations}");
    if total_violations == 0 {
        println!("\nbelow_boundary_deviation VALIDATED with random permutations.");
    } else {
        println!("\nFAILURES DETECTED! Statement may need fixing.");
    }
}
