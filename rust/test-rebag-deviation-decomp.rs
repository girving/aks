#!/usr/bin/env -S cargo +nightly -Zscript
//! Decompose the deviation after rebag into contributions from three sources:
//! 1. kick_L (from left child's toParent)
//! 2. kick_R (from right child's toParent)
//! 3. fromParent (from parent's toLeftChild or toRightChild)
//!
//! For each rebag bag, compute:
//! - Total deviation |C - b/2|
//! - Deviation contribution from each source
//! - The parent's deviation at stage t (used inductively)
//!
//! Key question: is fromParent deviation ≤ parent_deviation / 2 + small correction?

use std::collections::BTreeMap;

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
    if (1usize << level) > n { return 0; }
    n / (1 << level)
}

fn apply_adversarial_separator(items: &mut Vec<usize>, eps: f64, lambda: f64) {
    items.sort();
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
            if left_pos < right_pos && right_pos < m {
                items.swap(left_pos, right_pos);
            }
        }
    }
    if fringe > 0 {
        let fringe_errors = (eps * fringe as f64).floor() as usize;
        for k in 0..fringe_errors.min(fringe).min(middle_size) {
            let fringe_pos = fringe - 1 - k;
            let middle_pos = middle_start + k;
            if fringe_pos < middle_pos { items.swap(fringe_pos, middle_pos); }
            let high_fringe_pos = middle_end + k;
            let high_middle_pos = middle_end - 1 - k;
            if high_middle_pos < high_fringe_pos && high_fringe_pos < m {
                items.swap(high_middle_pos, high_fringe_pos);
            }
        }
    }
}

#[derive(Clone)]
struct SplitResult {
    to_parent: Vec<usize>,
    to_left: Vec<usize>,
    to_right: Vec<usize>,
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

    fn rank_in_bag(&self, bag: &[usize], i: usize) -> usize {
        bag.iter().filter(|&&j| self.perm[j] < self.perm[i]).count()
    }

    /// Compute the deviation for a set of items
    fn compute_deviation(&self, items: &[usize], level: usize, idx: usize) -> (usize, usize, i64) {
        let boundary = idx * bag_size(self.n, level) + bag_size(self.n, level + 1);
        let c = items.iter().filter(|&&i| self.perm[i] < boundary).count();
        let b = items.len();
        let dev = c as i64 - (b / 2) as i64;
        (c, b, dev)
    }

    fn do_stage_with_tracking(&mut self, params: &Params, t: usize) -> Vec<RebagInfo> {
        let mut splits: BTreeMap<(usize, usize), SplitResult> = BTreeMap::new();

        for (&(level, idx), items) in &self.bags {
            if items.is_empty() { continue; }
            if (t + level) % 2 != 0 { continue; }

            let mut sorted_items = items.clone();
            apply_adversarial_separator(&mut sorted_items, params.eps, params.lambda);
            let b = sorted_items.len();
            let cap = params.capacity(self.n, t, level);
            let f = (params.lambda * cap).floor() as usize;

            let result = if level == 0 {
                let half = b / 2;
                SplitResult {
                    to_parent: sorted_items.iter()
                        .filter(|&&i| self.rank_in_bag(&sorted_items, i) >= 2 * (b / 2))
                        .copied().collect(),
                    to_left: sorted_items.iter()
                        .filter(|&&i| self.rank_in_bag(&sorted_items, i) < half)
                        .copied().collect(),
                    to_right: sorted_items.iter()
                        .filter(|&&i| {
                            let r = self.rank_in_bag(&sorted_items, i);
                            r >= half && r < 2 * (b / 2)
                        })
                        .copied().collect(),
                }
            } else if level >= self.max_level {
                SplitResult { to_parent: sorted_items, to_left: vec![], to_right: vec![] }
            } else {
                let h = (b / 2).saturating_sub(f);
                SplitResult {
                    to_parent: sorted_items.iter()
                        .filter(|&&i| {
                            let r = self.rank_in_bag(&sorted_items, i);
                            r < f || r >= f + 2 * h
                        })
                        .copied().collect(),
                    to_left: sorted_items.iter()
                        .filter(|&&i| {
                            let r = self.rank_in_bag(&sorted_items, i);
                            r >= f && r < f + h
                        })
                        .copied().collect(),
                    to_right: sorted_items.iter()
                        .filter(|&&i| {
                            let r = self.rank_in_bag(&sorted_items, i);
                            r >= f + h && r < f + 2 * h
                        })
                        .copied().collect(),
                }
            };

            splits.insert((level, idx), result);
        }

        // Compute parent deviations before rebag
        let mut parent_devs: BTreeMap<(usize, usize), i64> = BTreeMap::new();
        for (&(level, idx), items) in &self.bags {
            if !items.is_empty() {
                let (_, _, dev) = self.compute_deviation(items, level, idx);
                parent_devs.insert((level, idx), dev);
            }
        }

        // Rebag with tracking
        let mut infos = Vec::new();
        let mut new_bags: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();

        for level in 0..=self.max_level {
            if (t + 1 + level) % 2 != 0 { continue; }
            let num_bags = 1usize << level;
            for idx in 0..num_bags {
                let kick_l: Vec<usize> = splits.get(&(level + 1, 2 * idx))
                    .map_or(vec![], |s| s.to_parent.clone());
                let kick_r: Vec<usize> = splits.get(&(level + 1, 2 * idx + 1))
                    .map_or(vec![], |s| s.to_parent.clone());
                let from_parent: Vec<usize> = if level > 0 {
                    if let Some(s) = splits.get(&(level - 1, idx / 2)) {
                        if idx % 2 == 0 { s.to_left.clone() } else { s.to_right.clone() }
                    } else { vec![] }
                } else { vec![] };

                let mut bag = Vec::new();
                bag.extend(&kick_l);
                bag.extend(&kick_r);
                bag.extend(&from_parent);

                let boundary = idx * bag_size(self.n, level) + bag_size(self.n, level + 1);

                // Compute per-source below-boundary counts
                let c_kl = kick_l.iter().filter(|&&i| self.perm[i] < boundary).count();
                let c_kr = kick_r.iter().filter(|&&i| self.perm[i] < boundary).count();
                let c_fp = from_parent.iter().filter(|&&i| self.perm[i] < boundary).count();
                let c_total = c_kl + c_kr + c_fp;
                let b_total = bag.len();

                // Get parent's deviation at stage t
                let parent_dev = if level > 0 {
                    parent_devs.get(&(level - 1, idx / 2)).copied().unwrap_or(0)
                } else { 0 };

                // Parent's C_lo: items in parent with perm < my_boundary
                let parent_c_lo = if level > 0 {
                    if let Some(parent_items) = self.bags.get(&(level - 1, idx / 2)) {
                        parent_items.iter().filter(|&&i| self.perm[i] < boundary).count() as i64
                    } else { 0 }
                } else { 0 };

                // Parent's C_parent: items in parent with perm < parent_boundary
                let parent_boundary_val = if level > 0 {
                    (idx / 2) * bag_size(self.n, level - 1) + bag_size(self.n, level)
                } else { 0 };
                let parent_c_parent = if level > 0 {
                    if let Some(parent_items) = self.bags.get(&(level - 1, idx / 2)) {
                        parent_items.iter().filter(|&&i| self.perm[i] < parent_boundary_val).count() as i64
                    } else { 0 }
                } else { 0 };

                let cap_new = params.capacity(self.n, t + 1, level);

                let info = RebagInfo {
                    level, idx,
                    b_total, c_total,
                    kick_l_size: kick_l.len(), c_kick_l: c_kl,
                    kick_r_size: kick_r.len(), c_kick_r: c_kr,
                    from_parent_size: from_parent.len(), c_from_parent: c_fp,
                    parent_dev,
                    parent_c_lo,
                    parent_c_parent,
                    cap_new,
                };
                infos.push(info);

                new_bags.insert((level, idx), bag);
            }
        }

        self.bags = new_bags;
        infos
    }
}

struct RebagInfo {
    level: usize,
    idx: usize,
    b_total: usize,
    c_total: usize,
    kick_l_size: usize,
    c_kick_l: usize,
    kick_r_size: usize,
    c_kick_r: usize,
    from_parent_size: usize,
    c_from_parent: usize,
    parent_dev: i64,
    parent_c_lo: i64,
    parent_c_parent: i64,
    cap_new: f64,
}

fn main() {
    let params = Params {
        a: 10.0,
        nu: 0.65,
        lambda: 0.01,
        eps: 0.01,
    };

    let coeff = params.cnative_coeff();
    println!("cnativeCoeff = {:.8}", coeff);
    println!();

    let mut max_total_dev_ratio = 0.0f64;
    let mut max_from_parent_dev_ratio = 0.0f64;
    let mut max_kick_dev_ratio = 0.0f64;
    let mut max_from_parent_vs_parent_dev = 0.0f64;
    let mut max_cases = Vec::new();

    for k in 3..=12 {
        let n = 1 << k;
        eprint!("n = {} (2^{}):", n, k);

        let mut tree = BagTree::new(n);
        let max_stages = 100;

        for t in 0..max_stages {
            let infos = tree.do_stage_with_tracking(&params, t);

            for info in &infos {
                if info.b_total == 0 { continue; }

                let dev = (info.c_total as i64 - (info.b_total / 2) as i64).unsigned_abs() as f64;
                let bound = coeff * info.cap_new;

                if bound > 0.001 {
                    let ratio = dev / bound;
                    if ratio > max_total_dev_ratio {
                        max_total_dev_ratio = ratio;
                    }
                }

                // fromParent deviation
                if info.from_parent_size > 0 {
                    let fp_dev = (info.c_from_parent as i64 - (info.from_parent_size / 2) as i64).unsigned_abs() as f64;
                    if info.cap_new > 0.001 {
                        let fp_ratio = fp_dev / info.cap_new;
                        if fp_ratio > max_from_parent_dev_ratio {
                            max_from_parent_dev_ratio = fp_ratio;
                        }
                    }

                    // How does fromParent deviation relate to parent's deviation?
                    let parent_dev_abs = info.parent_dev.unsigned_abs() as f64;
                    if parent_dev_abs > 0.5 {
                        let fp_vs_parent = fp_dev / parent_dev_abs;
                        if fp_vs_parent > max_from_parent_vs_parent_dev {
                            max_from_parent_vs_parent_dev = fp_vs_parent;
                            max_cases.push(format!(
                                "  ({},{}) t={}: fp_dev={:.0} parent_dev={:.0} ratio={:.4} fp_size={} kl={} kr={} b={} c_lo={} c_par={}",
                                info.level, info.idx, t+1, fp_dev, parent_dev_abs, fp_vs_parent,
                                info.from_parent_size, info.kick_l_size, info.kick_r_size,
                                info.b_total, info.parent_c_lo, info.parent_c_parent
                            ));
                        }
                    }
                }

                // Kick deviation
                let kick_size = info.kick_l_size + info.kick_r_size;
                if kick_size > 0 {
                    let kick_c = info.c_kick_l + info.c_kick_r;
                    let kick_dev = (kick_c as i64 - (kick_size / 2) as i64).unsigned_abs() as f64;
                    if info.cap_new > 0.001 {
                        let kick_ratio = kick_dev / info.cap_new;
                        if kick_ratio > max_kick_dev_ratio {
                            max_kick_dev_ratio = kick_ratio;
                        }
                    }
                }
            }

            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < 2.0 {
                eprintln!(" converged at t={}", t + 1);
                break;
            }
        }
    }

    println!("=== RESULTS ===");
    println!("Max total deviation / (cnc*cap):   {:.6}", max_total_dev_ratio);
    println!("Max fromParent dev / cap(t+1):     {:.6}", max_from_parent_dev_ratio);
    println!("Max kick dev / cap(t+1):           {:.6}", max_kick_dev_ratio);
    println!("Max fromParent_dev / parent_dev:    {:.6}", max_from_parent_vs_parent_dev);
    println!();
    println!("Top cases where fromParent_dev / parent_dev is high:");
    for case in max_cases.iter().rev().take(10) {
        println!("{}", case);
    }

    // Now compute: what bound on fromParent deviation is needed?
    // If total_dev ≤ cnc * cap(t+1, level)
    // and kick_dev ≤ kick_size/2
    // then fromParent_dev ≤ total_dev + kick_dev (triangle ineq wrong direction)
    // Actually: total_dev ≤ fromParent_dev + kick_dev (approx)
    // So: fromParent_dev ≤ cnc * cap(t+1) + kick_size/2
    // We need: fromParent_dev ≤ f(parent_dev, cap, kick_size)
    println!();

    // Test: is fromParent_dev ≤ parent_dev (i.e., deviation doesn't increase)?
    if max_from_parent_vs_parent_dev <= 1.0 + 0.01 {
        println!("fromParent deviation ≤ parent deviation (ratio {:.4})", max_from_parent_vs_parent_dev);
        println!("→ Deviation is non-increasing through concreteSplit!");
    } else {
        println!("fromParent deviation can EXCEED parent deviation (ratio {:.4})", max_from_parent_vs_parent_dev);
    }
}
