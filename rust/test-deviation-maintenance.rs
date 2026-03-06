#!/usr/bin/env -S cargo +nightly -Zscript
//! Test that clause 9 (deviation bound) is maintained through rebag.
//!
//! For each bag at (level, idx) at stage t, the deviation bound says:
//!   |C - ⌊b/2⌋| ≤ cnativeCoeff * cap(t, level)
//! where C = |{r ∈ B : perm(r) < boundary}|, boundary = idx*bagSize(level) + bagSize(level+1),
//! and b = |B|.

use std::collections::BTreeMap;

#[derive(Clone, Debug)]
struct Params {
    a: f64,
    nu: f64,
    lambda: f64,
    eps: f64,
}

impl Params {
    fn capacity(&self, n: usize, t: usize, level: usize) -> f64 {
        n as f64 * self.nu.powi(t as i32) * self.a.powi(level as i32)
    }

    fn cnative_coeff(&self) -> f64 {
        let e2a2 = (2.0 * self.eps * self.a).powi(2);
        self.eps / 2.0
            + 2.0 * self.lambda * self.eps * self.a.powi(2) / (1.0 - e2a2)
            + 1.0 / (8.0 * self.a.powi(2) - 2.0)
    }
}

fn bag_size(n: usize, level: usize) -> usize {
    n / (1 << level)
}

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn next_usize(&mut self, bound: usize) -> usize {
        (self.next_u64() % bound as u64) as usize
    }
    fn next_f64(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 / (1u64 << 53) as f64
    }
}

/// Apply adversarial separator: sort, then introduce worst-case errors
fn apply_adversarial_separator(items: &mut Vec<usize>, eps: f64, lambda: f64) {
    items.sort();
    let m = items.len();
    if m <= 1 { return; }

    let fringe = (lambda * m as f64).floor() as usize;
    let middle_start = fringe;
    let middle_end = m.saturating_sub(fringe);
    let middle_size = middle_end.saturating_sub(middle_start);
    let half = middle_size / 2;

    // Halving errors: swap ⌊ε·half⌋ items between left and right middle
    let halving_errors = (eps * half as f64).floor() as usize;
    if halving_errors > 0 && half > 0 {
        for k in 0..halving_errors.min(half) {
            let left_pos = middle_start + half - 1 - k;
            let right_pos = middle_start + half + k;
            if left_pos < right_pos && right_pos < m {
                items.swap(left_pos, right_pos);
            }
        }
    }

    // Fringe leakage: swap ⌊ε·F⌋ items from each fringe into middle
    if fringe > 0 {
        let fringe_errors = (eps * fringe as f64).floor() as usize;
        for k in 0..fringe_errors.min(fringe).min(middle_size) {
            // Low fringe leaks into middle
            let fringe_pos = fringe - 1 - k;
            let middle_pos = middle_start + k;
            if fringe_pos < middle_pos {
                items.swap(fringe_pos, middle_pos);
            }
            // High fringe leaks into middle
            let high_fringe_pos = middle_end + k;
            let high_middle_pos = middle_end - 1 - k;
            if high_middle_pos < high_fringe_pos && high_fringe_pos < m {
                items.swap(high_middle_pos, high_fringe_pos);
            }
        }
    }
}

struct BagTree {
    n: usize,
    max_level: usize,
    bags: BTreeMap<(usize, usize), Vec<usize>>,
    perm: Vec<usize>,
}

impl BagTree {
    fn new(n: usize) -> Self {
        assert!(n.is_power_of_two() && n >= 2);
        let max_level = n.trailing_zeros() as usize - 1;
        let mut bags = BTreeMap::new();
        let perm: Vec<usize> = (0..n).collect();
        bags.insert((0, 0), (0..n).collect());
        Self { n, max_level, bags, perm }
    }

    fn get_bag(&self, level: usize, idx: usize) -> &[usize] {
        self.bags.get(&(level, idx)).map_or(&[], |v| v.as_slice())
    }

    /// Compute rank of item i in bag
    fn rank_in_bag(&self, bag: &[usize], i: usize) -> usize {
        bag.iter().filter(|&&j| self.perm[j] < self.perm[i]).count()
    }

    /// Perform one stage of the bag-tree sorting network
    fn do_stage(&mut self, params: &Params, t: usize) {
        let mut splits: BTreeMap<(usize, usize), (Vec<usize>, Vec<usize>, Vec<usize>)> = BTreeMap::new();

        // For each active bag, compute the split
        for (&(level, idx), items) in &self.bags {
            if items.is_empty() { continue; }
            if (t + level) % 2 != 0 { continue; }

            let mut sorted_items = items.clone();
            apply_adversarial_separator(&mut sorted_items, params.eps, params.lambda);

            let b = sorted_items.len();
            let cap = params.capacity(self.n, t, level);
            let f = (params.lambda * cap).floor() as usize;

            if level == 0 {
                // Root: no fringe kick, split at b/2
                let half = b / 2;
                let to_parent: Vec<usize> = sorted_items.iter()
                    .filter(|&&i| self.rank_in_bag(&sorted_items, i) >= 2 * (b / 2))
                    .copied().collect();
                let to_left: Vec<usize> = sorted_items.iter()
                    .filter(|&&i| self.rank_in_bag(&sorted_items, i) < half)
                    .copied().collect();
                let to_right: Vec<usize> = sorted_items.iter()
                    .filter(|&&i| {
                        let r = self.rank_in_bag(&sorted_items, i);
                        r >= half && r < 2 * (b / 2)
                    })
                    .copied().collect();
                splits.insert((level, idx), (to_parent, to_left, to_right));
            } else if level >= self.max_level {
                // Leaf: all items to parent (no children)
                // NOTE: in the Lean code, only fringe goes to parent at leaves.
                // Here we send ALL to match what the test-bags.rs does.
                splits.insert((level, idx), (sorted_items, vec![], vec![]));
            } else {
                // Interior: fringe to parent, middle to children
                let h = (b / 2).saturating_sub(f);
                let to_parent: Vec<usize> = sorted_items.iter()
                    .filter(|&&i| {
                        let r = self.rank_in_bag(&sorted_items, i);
                        r < f || r >= f + 2 * h
                    })
                    .copied().collect();
                let to_left: Vec<usize> = sorted_items.iter()
                    .filter(|&&i| {
                        let r = self.rank_in_bag(&sorted_items, i);
                        r >= f && r < f + h
                    })
                    .copied().collect();
                let to_right: Vec<usize> = sorted_items.iter()
                    .filter(|&&i| {
                        let r = self.rank_in_bag(&sorted_items, i);
                        r >= f + h && r < f + 2 * h
                    })
                    .copied().collect();
                splits.insert((level, idx), (to_parent, to_left, to_right));
            }
        }

        // Rebag: each bag receives kicks from children + items from parent
        let mut new_bags: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();
        for level in 0..=self.max_level {
            if (t + 1 + level) % 2 != 0 { continue; }
            let num_bags = 1usize << level;
            for idx in 0..num_bags {
                let mut bag = Vec::new();
                // Kick from left child
                if let Some((tp, _, _)) = splits.get(&(level + 1, 2 * idx)) {
                    bag.extend(tp);
                }
                // Kick from right child
                if let Some((tp, _, _)) = splits.get(&(level + 1, 2 * idx + 1)) {
                    bag.extend(tp);
                }
                // From parent
                if level > 0 {
                    if let Some((_, tl, tr)) = splits.get(&(level - 1, idx / 2)) {
                        if idx % 2 == 0 {
                            bag.extend(tl);
                        } else {
                            bag.extend(tr);
                        }
                    }
                }
                new_bags.insert((level, idx), bag);
            }
        }

        self.bags = new_bags;
    }

    /// Check deviation bound: |C - b/2| ≤ cnativeCoeff * cap(t, level)
    fn check_deviation_bound(&self, params: &Params, t: usize) -> Result<(), String> {
        let coeff = params.cnative_coeff();
        let mut max_ratio: f64 = 0.0;
        let mut max_detail = String::new();

        for (&(level, idx), items) in &self.bags {
            if items.is_empty() { continue; }

            let b = items.len();
            let boundary = idx * bag_size(self.n, level) + bag_size(self.n, level + 1);
            let c = items.iter().filter(|&&i| self.perm[i] < boundary).count();
            let deviation = (c as i64 - (b / 2) as i64).unsigned_abs() as f64;
            let cap = params.capacity(self.n, t, level);
            let bound = coeff * cap;

            if bound > 0.0 {
                let ratio = deviation / bound;
                if ratio > max_ratio {
                    max_ratio = ratio;
                    max_detail = format!(
                        "({},{}) b={} c={} dev={} bound={:.4} ratio={:.6}",
                        level, idx, b, c, deviation as u64, bound, ratio
                    );
                }
            }

            if deviation > bound + 0.001 {
                return Err(format!(
                    "VIOLATION at ({},{}) t={}: |C-b/2| = {} > cnativeCoeff*cap = {:.4} (ratio={:.4})",
                    level, idx, t, deviation as u64, bound, deviation / bound
                ));
            }
        }

        if max_ratio > 0.0 {
            eprintln!("  t={}: max deviation ratio = {:.6} @ {}", t, max_ratio, max_detail);
        }

        Ok(())
    }
}

fn main() {
    let params = Params {
        a: 10.0,
        nu: 0.65,
        lambda: 0.01,
        eps: 0.01,
    };

    println!("cnativeCoeff = {:.8}", params.cnative_coeff());
    println!();

    let mut any_violation = false;

    for k in 3..=14 {
        let n = 1 << k;
        print!("n = {} (2^{}):", n, k);

        let mut tree = BagTree::new(n);

        // Check initial deviation
        if let Err(e) = tree.check_deviation_bound(&params, 0) {
            println!(" INITIAL {}", e);
            any_violation = true;
            continue;
        }

        let max_stages = 200;
        let mut converged = false;

        for t in 0..max_stages {
            tree.do_stage(&params, t);

            if let Err(e) = tree.check_deviation_bound(&params, t + 1) {
                println!(" {}", e);
                any_violation = true;
                break;
            }

            // Check convergence
            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < 2.0 {
                println!(" OK (converged at t={}, {} stages)", t + 1, t + 1);
                converged = true;
                break;
            }
        }

        if !converged && !any_violation {
            println!(" OK (did not converge in {} stages)", max_stages);
        }
    }

    if any_violation {
        println!("\nSOME VIOLATIONS FOUND");
        std::process::exit(1);
    } else {
        println!("\nAll deviation bounds maintained. ✓");
    }
}
