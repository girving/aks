#!/usr/bin/env -S cargo +nightly -Zscript
//! Test whether deviation |C - b/2| can be bounded by stranger counts alone.
//!
//! For each bag at (level, idx) at stage t, we compute:
//! 1. The deviation |C - ⌊b/2⌋|
//! 2. The stranger counts S_1, S_2, ..., S_level (actual values)
//! 3. Various candidate formulas for bounding deviation from stranger counts
//!
//! If a formula works, it means clause 9 (deviation_bound) can be derived
//! from clause 4 (stranger_bound) without maintaining it separately.

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
            if fringe_pos < middle_pos {
                items.swap(fringe_pos, middle_pos);
            }
            let high_fringe_pos = middle_end + k;
            let high_middle_pos = middle_end - 1 - k;
            if high_middle_pos < high_fringe_pos && high_fringe_pos < m {
                items.swap(high_middle_pos, high_fringe_pos);
            }
        }
    }
}

/// Check if item with rank `r` is j-strange at bag (level, idx)
fn is_j_stranger(n: usize, rank: usize, level: usize, idx: usize, j: usize) -> bool {
    if j < 1 || j > level { return false; }
    let check_level = level - (j - 1);
    let bs = bag_size(n, check_level);
    if bs == 0 { return false; }
    let native_idx = rank / bs;
    let ancestor_idx = idx / (1 << (j - 1));
    native_idx != ancestor_idx
}

/// Count j-strangers in a bag
fn j_stranger_count(n: usize, perm: &[usize], items: &[usize], level: usize, idx: usize, j: usize) -> usize {
    items.iter().filter(|&&i| is_j_stranger(n, perm[i], level, idx, j)).count()
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

    fn do_stage(&mut self, params: &Params, t: usize) {
        let mut splits: BTreeMap<(usize, usize), (Vec<usize>, Vec<usize>, Vec<usize>)> = BTreeMap::new();

        for (&(level, idx), items) in &self.bags {
            if items.is_empty() { continue; }
            if (t + level) % 2 != 0 { continue; }

            let mut sorted_items = items.clone();
            apply_adversarial_separator(&mut sorted_items, params.eps, params.lambda);

            let b = sorted_items.len();
            let cap = params.capacity(self.n, t, level);
            let f = (params.lambda * cap).floor() as usize;

            if level == 0 {
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
                splits.insert((level, idx), (sorted_items, vec![], vec![]));
            } else {
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

        let mut new_bags: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();
        for level in 0..=self.max_level {
            if (t + 1 + level) % 2 != 0 { continue; }
            let num_bags = 1usize << level;
            for idx in 0..num_bags {
                let mut bag = Vec::new();
                if let Some((tp, _, _)) = splits.get(&(level + 1, 2 * idx)) {
                    bag.extend(tp);
                }
                if let Some((tp, _, _)) = splits.get(&(level + 1, 2 * idx + 1)) {
                    bag.extend(tp);
                }
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

    /// For each nonempty bag, compute deviation and stranger counts.
    /// Returns max ratio of deviation / (candidate bound).
    fn analyze_deviation_vs_strangers(&self, params: &Params, t: usize) -> AnalysisResult {
        let mut result = AnalysisResult::default();
        let coeff = params.cnative_coeff();

        for (&(level, idx), items) in &self.bags {
            if items.is_empty() { continue; }

            let b = items.len();
            let boundary = idx * bag_size(self.n, level) + bag_size(self.n, level + 1);
            let c = items.iter().filter(|&&i| self.perm[i] < boundary).count();
            let deviation = (c as i64 - (b / 2) as i64).unsigned_abs() as f64;

            // Compute stranger counts
            let mut stranger_counts = vec![];
            for j in 1..=level {
                stranger_counts.push(j_stranger_count(self.n, &self.perm, items, level, idx, j) as f64);
            }

            let cap = params.capacity(self.n, t, level);
            let cnc_bound = coeff * cap;

            // Compute native imbalance
            let s1 = if !stranger_counts.is_empty() { stranger_counts[0] } else { 0.0 };
            let bs = bag_size(self.n, level) as f64;

            // n_L = items native to left child (perm in [idx*BS, idx*BS + BS/2))
            let left_native = items.iter().filter(|&&i| {
                let p = self.perm[i];
                let lo = idx * bag_size(self.n, level);
                let mid = lo + bag_size(self.n, level + 1);
                p >= lo && p < mid
            }).count() as f64;

            // n_R = items native to right child
            let right_native = items.iter().filter(|&&i| {
                let p = self.perm[i];
                let mid = idx * bag_size(self.n, level) + bag_size(self.n, level + 1);
                let hi = (idx + 1) * bag_size(self.n, level);
                p >= mid && p < hi
            }).count() as f64;

            let native_imbalance = (left_native - right_native).abs();

            // Formula F1: deviation ≤ (S₁ + native_imbalance) / 2
            // (exact decomposition, trivially true but checks native_imbalance)
            let f1_bound = (s1 + native_imbalance) / 2.0;

            // Formula F2: deviation ≤ S₁ (just stranger count)
            let f2_bound = s1;

            // Formula F3: compute Σ σ_k * (S_k - S_{k+1}) and native_imbalance
            // Check if 2*deviation ≤ stranger_sum + native_imbalance
            let stranger_sum: f64 = stranger_counts.iter().sum();

            // Formula F4: deviation ≤ (stranger_sum + b_odd) / 2
            // where b_odd = b % 2 (rounding contribution)
            let f4_bound = (stranger_sum + (b % 2) as f64) / 2.0;

            // Formula F5: deviation ≤ cnativeCoeff * cap (the original bound)
            // This should always work since it's maintained inductively
            let f5_bound = cnc_bound;

            // Track max ratios
            if deviation > 0.001 {
                if f1_bound > 0.001 {
                    let r = deviation / f1_bound;
                    if r > result.max_ratio_f1 {
                        result.max_ratio_f1 = r;
                        result.max_f1_detail = format!(
                            "({},{}) t={} dev={:.1} nL={:.0} nR={:.0} S1={:.0} f1={:.1}",
                            level, idx, t, deviation, left_native, right_native, s1, f1_bound
                        );
                    }
                }
                if f2_bound > 0.001 {
                    result.max_ratio_f2 = result.max_ratio_f2.max(deviation / f2_bound);
                }
                if f4_bound > 0.001 {
                    result.max_ratio_f4 = result.max_ratio_f4.max(deviation / f4_bound);
                }
                if f5_bound > 0.001 {
                    result.max_ratio_f5 = result.max_ratio_f5.max(deviation / f5_bound);
                }

                // Track native_imbalance vs S1
                if s1 > 0.001 {
                    result.max_native_imb_over_s1 = result.max_native_imb_over_s1.max(native_imbalance / s1);
                }

                // Track native_imbalance vs cap
                if cap > 0.001 {
                    result.max_native_imb_over_cap = result.max_native_imb_over_cap.max(native_imbalance / cap);
                }

                // Track native_imbalance vs stranger_sum
                if stranger_sum > 0.001 {
                    result.max_native_imb_over_strangers = result.max_native_imb_over_strangers.max(native_imbalance / stranger_sum);
                }

                // New: track 2*deviation vs native_imbalance + S1 + b%2
                // (this should be EXACT by the decomposition formula)
                let exact_check = native_imbalance + s1 + (b % 2) as f64;
                let two_dev = 2.0 * deviation;
                if two_dev > exact_check + 0.1 {
                    result.decomp_violations += 1;
                    eprintln!("  DECOMP VIOLATION: ({},{}) t={} 2*dev={:.1} > nI+S1+b%2={:.1}",
                        level, idx, t, two_dev, exact_check);
                }
            }
        }

        result
    }
}

#[derive(Default)]
struct AnalysisResult {
    max_ratio_f1: f64,  // deviation / ((S1 + native_imb) / 2)
    max_ratio_f2: f64,  // deviation / S1
    max_ratio_f4: f64,  // deviation / ((total_strangers + b%2) / 2)
    max_ratio_f5: f64,  // deviation / (cnativeCoeff * cap)
    max_native_imb_over_s1: f64,      // |nL - nR| / S1
    max_native_imb_over_cap: f64,     // |nL - nR| / cap
    max_native_imb_over_strangers: f64, // |nL - nR| / Σ S_j
    max_f1_detail: String,
    decomp_violations: usize,
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

    // Global trackers
    let mut global_max_f1 = 0.0_f64;
    let mut global_max_f2 = 0.0_f64;
    let mut global_max_f4 = 0.0_f64;
    let mut global_max_f5 = 0.0_f64;
    let mut global_max_ni_s1 = 0.0_f64;
    let mut global_max_ni_cap = 0.0_f64;
    let mut global_max_ni_str = 0.0_f64;
    let mut total_decomp_violations = 0;

    for k in 3..=12 {
        let n = 1 << k;
        eprint!("n = {} (2^{}):", n, k);

        let mut tree = BagTree::new(n);

        let max_stages = 100;
        for t in 0..max_stages {
            tree.do_stage(&params, t);
            let r = tree.analyze_deviation_vs_strangers(&params, t + 1);

            global_max_f1 = global_max_f1.max(r.max_ratio_f1);
            global_max_f2 = global_max_f2.max(r.max_ratio_f2);
            global_max_f4 = global_max_f4.max(r.max_ratio_f4);
            global_max_f5 = global_max_f5.max(r.max_ratio_f5);
            global_max_ni_s1 = global_max_ni_s1.max(r.max_native_imb_over_s1);
            global_max_ni_cap = global_max_ni_cap.max(r.max_native_imb_over_cap);
            global_max_ni_str = global_max_ni_str.max(r.max_native_imb_over_strangers);
            total_decomp_violations += r.decomp_violations;

            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < 2.0 {
                eprintln!(" converged at t={}", t + 1);
                break;
            }
        }
    }

    println!("=== RESULTS ===");
    println!("Max ratio F1 (dev / ((S1+nativeImb)/2)):  {:.6}", global_max_f1);
    println!("Max ratio F2 (dev / S1):                  {:.6}", global_max_f2);
    println!("Max ratio F4 (dev / ((Σsj+b%2)/2)):       {:.6}", global_max_f4);
    println!("Max ratio F5 (dev / (cnc*cap)):            {:.6}", global_max_f5);
    println!();
    println!("Max |nL-nR| / S1:                         {:.6}", global_max_ni_s1);
    println!("Max |nL-nR| / cap:                        {:.6}", global_max_ni_cap);
    println!("Max |nL-nR| / Σ S_j:                      {:.6}", global_max_ni_str);
    println!();
    println!("Decomposition violations (2*dev > nI+S1+b%2): {}", total_decomp_violations);

    if total_decomp_violations > 0 {
        println!("\nWARNING: decomposition formula violated!");
        std::process::exit(1);
    }

    // Key question: is native_imbalance bounded by a function of stranger counts?
    if global_max_ni_s1 > 1.5 {
        println!("\nNative imbalance NOT bounded by S1 (ratio {:.4})", global_max_ni_s1);
        println!("→ Cannot derive deviation from local stranger count alone");
    } else {
        println!("\nNative imbalance bounded by ~{:.2}×S1", global_max_ni_s1);
        println!("→ Derivation from stranger counts MAY be feasible");
    }
}
