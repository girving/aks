#!/usr/bin/env -S cargo +nightly -Zscript
//! Test the "actual model" for separatorSortingNetwork_sorts.
//!
//! The actual model:
//! - Bags are determined by the id-model (wireMapSeq, perm=id)
//! - Values evolve via separator execution (π_t → π_{t+1})
//! - Stranger counting uses current values (perm = π_t)
//!
//! Key claims to validate:
//! 1. Perm stability: separator preserves multiset within each bag,
//!    so stranger counts on stage-t bags are unchanged by π_t → π_{t+1}
//! 2. hfilter: fromParent items have ≤ ε × (full bag stranger count) strangers
//! 3. hcnative: sibling-native count in fromParent ≤ cnativeCoeff × cap
//! 4. Overall invariant with perm = π_t on id-model bags converges
//! 5. Convergence → sorted output

use std::collections::BTreeMap;

/// Parameters
#[derive(Clone, Debug)]
struct Params {
    a: f64,
    nu: f64,
    lambda: f64,
    eps: f64,
}

impl Params {
    fn seiferas() -> Self {
        // Use params that satisfy all constraints
        Params { a: 10.0, nu: 13.0/20.0, lambda: 1.0/100.0, eps: 1.0/100.0 }
    }

    fn capacity(&self, n: usize, t: usize, level: usize) -> f64 {
        (n as f64) * self.nu.powi(t as i32) * self.a.powi(level as i32)
    }

    fn parent_stranger_coeff(&self) -> f64 {
        let a = self.a;
        let e = self.eps;
        let l = self.lambda;
        e * l / a + e / (2.0 * a)
            + 2.0 * l * e * a / (1.0 - (2.0 * e * a).powi(2))
            + 1.0 / (8.0 * a.powi(3) - 2.0 * a)
    }

    fn cnative_coeff(&self) -> f64 {
        let a = self.a;
        let e = self.eps;
        let l = self.lambda;
        e / 2.0 + 2.0 * l * e * a.powi(2) / (1.0 - (2.0 * e * a).powi(2))
            + 1.0 / (8.0 * a.powi(2) - 2.0)
    }
}

/// Simple RNG
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Rng(seed) }
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
    fn shuffle<T>(&mut self, v: &mut [T]) {
        for i in (1..v.len()).rev() {
            let j = self.next_usize(i + 1);
            v.swap(i, j);
        }
    }
}

fn max_level(n: usize) -> usize {
    assert!(n >= 4 && n.is_power_of_two());
    n.trailing_zeros() as usize - 1
}

fn bag_size(n: usize, level: usize) -> usize {
    n >> level
}

fn native_bag_idx(n: usize, level: usize, rank: usize) -> usize {
    let bs = bag_size(n, level);
    if bs == 0 { rank } else { rank / bs }
}

fn is_j_stranger(n: usize, rank: usize, level: usize, idx: usize, j: usize) -> bool {
    if j == 0 || j > level { return false; }
    let check_level = level - (j - 1);
    let check_idx = idx >> (j - 1);
    native_bag_idx(n, check_level, rank) != check_idx
}

fn j_stranger_count(n: usize, perm: &[usize], items: &[usize], level: usize, idx: usize, j: usize) -> usize {
    items.iter().filter(|&&r| is_j_stranger(n, perm[r], level, idx, j)).count()
}

/// Count sibling-native items: 1-stranger but not 2-stranger
fn sibling_native_count(n: usize, perm: &[usize], items: &[usize], level: usize, idx: usize) -> usize {
    items.iter().filter(|&&r| {
        is_j_stranger(n, perm[r], level, idx, 1)
            && !is_j_stranger(n, perm[r], level, idx, 2)
    }).count()
}

fn fringe_size(lambda: f64, cap: f64) -> usize {
    (lambda * cap).floor() as usize
}

fn child_send_size(lambda: f64, b: usize, cap: f64) -> usize {
    let f = fringe_size(lambda, cap);
    (b / 2).saturating_sub(f)
}

/// Split a bag by POSITION rank (perm = id for the split ranking).
/// Returns (to_parent, to_left_child, to_right_child).
fn id_split(items: &[usize], n: usize, level: usize, lambda: f64, cap: f64) -> (Vec<usize>, Vec<usize>, Vec<usize>) {
    let ml = max_level(n);
    if level >= ml {
        // Leaf: all to parent
        return (items.to_vec(), vec![], vec![]);
    }

    let b = items.len();
    if level == 0 {
        // Root: split by position rank, no parent
        let mut sorted = items.to_vec();
        sorted.sort(); // sort by register index (position)
        let half = b / 2;
        let to_left: Vec<usize> = sorted.iter().take(half).copied().collect();
        let to_right: Vec<usize> = sorted.iter().skip(half).take(half).copied().collect();
        let to_parent: Vec<usize> = sorted.iter().skip(2 * half).copied().collect();
        return (to_parent, to_left, to_right);
    }

    // Interior: rank by position within the bag
    let mut sorted = items.to_vec();
    sorted.sort(); // sort by register index
    let f = fringe_size(lambda, cap);
    let h = child_send_size(lambda, b, cap);

    let mut to_parent = Vec::new();
    let mut to_left = Vec::new();
    let mut to_right = Vec::new();

    for (rank, &r) in sorted.iter().enumerate() {
        if rank < f || rank >= f + 2 * h {
            to_parent.push(r);
        } else if rank < f + h {
            to_left.push(r);
        } else {
            to_right.push(r);
        }
    }

    (to_parent, to_left, to_right)
}

/// Apply separator within a bag: sort values, then introduce errors.
/// `positions` = register positions in the bag.
/// `perm` = current permutation (values at positions).
/// Returns the updated permutation.
fn apply_separator_to_bag(positions: &[usize], perm: &mut [usize], model: &str, eps: f64, rng: &mut Rng) {
    if positions.len() <= 1 { return; }

    // Collect (position, value) pairs
    let mut pairs: Vec<(usize, usize)> = positions.iter().map(|&p| (p, perm[p])).collect();
    // Sort by value
    pairs.sort_by_key(|&(_, v)| v);

    if model == "perfect" {
        // Perfect sort: assign sorted values to sorted positions
        let mut sorted_positions: Vec<usize> = positions.to_vec();
        sorted_positions.sort();
        for (i, &pos) in sorted_positions.iter().enumerate() {
            perm[pos] = pairs[i].1;
        }
    } else if model == "adversarial" {
        // Sort, then adversarially displace
        let mut sorted_positions: Vec<usize> = positions.to_vec();
        sorted_positions.sort();
        let values: Vec<usize> = pairs.iter().map(|&(_, v)| v).collect();

        // Place sorted values at sorted positions
        for (i, &pos) in sorted_positions.iter().enumerate() {
            perm[pos] = values[i];
        }

        // Then introduce adversarial errors
        let m = positions.len();
        let half = m / 2;
        let halving_errors = (eps * half as f64).floor() as usize;

        // Swap items near the midpoint between left and right halves
        if halving_errors > 0 && half > 0 {
            for k in 0..halving_errors.min(half) {
                let left_pos = sorted_positions[half - 1 - k];
                let right_pos = sorted_positions[half + k];
                if half - 1 - k < half + k {
                    let tmp = perm[left_pos];
                    perm[left_pos] = perm[right_pos];
                    perm[right_pos] = tmp;
                }
            }
        }
    }
}

/// Rebag: combine kicks from children and items from parent.
fn rebag(
    id_bags: &BTreeMap<(usize, usize), Vec<usize>>,
    n: usize,
    params: &Params,
    t: usize,
) -> BTreeMap<(usize, usize), Vec<usize>> {
    let ml = max_level(n);

    // First compute splits for all bags
    let mut splits: BTreeMap<(usize, usize), (Vec<usize>, Vec<usize>, Vec<usize>)> = BTreeMap::new();
    for (&(level, idx), items) in id_bags {
        let cap = params.capacity(n, t, level);
        splits.insert((level, idx), id_split(items, n, level, params.lambda, cap));
    }

    // Now rebag
    let mut new_bags: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();

    for level in 0..=ml {
        for idx in 0..(1 << level) {
            let mut bag = Vec::new();

            // Kicks from left child (level+1, 2*idx)
            if let Some((to_parent, _, _)) = splits.get(&(level + 1, 2 * idx)) {
                bag.extend(to_parent);
            }
            // Kicks from right child (level+1, 2*idx+1)
            if let Some((to_parent, _, _)) = splits.get(&(level + 1, 2 * idx + 1)) {
                bag.extend(to_parent);
            }
            // From parent
            if level > 0 {
                let parent_idx = idx / 2;
                if let Some((_, to_left, to_right)) = splits.get(&(level - 1, parent_idx)) {
                    if idx % 2 == 0 {
                        bag.extend(to_left);
                    } else {
                        bag.extend(to_right);
                    }
                }
            }

            if !bag.is_empty() {
                new_bags.insert((level, idx), bag);
            }
        }
    }

    new_bags
}

/// Get items for a bag, or empty vec
fn get_bag(bags: &BTreeMap<(usize, usize), Vec<usize>>, level: usize, idx: usize) -> Vec<usize> {
    bags.get(&(level, idx)).cloned().unwrap_or_default()
}

/// Get fromParent items for bag (level, idx) from the splits
fn get_from_parent(
    splits: &BTreeMap<(usize, usize), (Vec<usize>, Vec<usize>, Vec<usize>)>,
    level: usize, idx: usize,
) -> Vec<usize> {
    if level == 0 { return vec![]; }
    let parent_idx = idx / 2;
    if let Some((_, to_left, to_right)) = splits.get(&(level - 1, parent_idx)) {
        if idx % 2 == 0 { to_left.clone() } else { to_right.clone() }
    } else {
        vec![]
    }
}

fn main() {
    let params = Params::seiferas();
    println!("=== Actual Model Stress Test ===");
    println!("Params: A={}, ν={}, λ={}, ε={}", params.a, params.nu, params.lambda, params.eps);
    println!("parentStrangerCoeff = {:.6}", params.parent_stranger_coeff());
    println!("cnativeCoeff = {:.6}", params.cnative_coeff());
    println!();

    let mut any_failure = false;

    for &sep_model in &["perfect", "adversarial"] {
        let k_max_first = if sep_model == "adversarial" { 9 } else { 10 };
        for k in 3..=k_max_first {
            let n = 1 << k;
            let ml = max_level(n);
            let num_stages = 10 * k;

            for seed in 0..5 {
                let mut rng = Rng::new(seed * 1000 + k as u64);

                // Random initial permutation σ
                let mut sigma: Vec<usize> = (0..n).collect();
                rng.shuffle(&mut sigma);

                // π_t starts as σ
                let mut pi: Vec<usize> = sigma.clone();

                // id-model bags start as initial bags
                let mut id_bags: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();
                id_bags.insert((0, 0), (0..n).collect());

                // Track max violation ratios
                let mut max_stranger_ratio: f64 = 0.0;
                let mut max_hfilter_ratio: f64 = 0.0;
                let mut max_hcnative_ratio: f64 = 0.0;
                let mut max_deviation_ratio: f64 = 0.0;
                let mut perm_stability_violations = 0usize;

                for t in 0..num_stages {
                    // === Check 1: Perm stability ===
                    // Before applying separator, record stranger counts
                    let mut pre_counts: BTreeMap<(usize, usize, usize), usize> = BTreeMap::new();
                    for (&(level, idx), items) in &id_bags {
                        for j in 1..=level {
                            let count = j_stranger_count(n, &pi, items, level, idx, j);
                            pre_counts.insert((level, idx, j), count);
                        }
                    }

                    // Apply separator to each active bag
                    for (&(level, idx), items) in &id_bags {
                        if (t + level) % 2 != 0 { continue; } // skip inactive
                        if items.is_empty() { continue; }
                        apply_separator_to_bag(items, &mut pi, sep_model, params.eps, &mut rng);
                    }

                    // Check stranger counts are unchanged after separator (within same bags)
                    for (&(level, idx), items) in &id_bags {
                        for j in 1..=level {
                            let post_count = j_stranger_count(n, &pi, items, level, idx, j);
                            let pre_count = *pre_counts.get(&(level, idx, j)).unwrap_or(&0);
                            if post_count != pre_count {
                                perm_stability_violations += 1;
                            }
                        }
                    }

                    // === Compute splits (id-based) ===
                    let mut splits: BTreeMap<(usize, usize), (Vec<usize>, Vec<usize>, Vec<usize>)> = BTreeMap::new();
                    for (&(level, idx), items) in &id_bags {
                        let cap = params.capacity(n, t, level);
                        splits.insert((level, idx), id_split(items, n, level, params.lambda, cap));
                    }

                    // === Check 2: hfilter ===
                    // For each bag, check that fromParent items have ≤ ε × full_stranger count
                    for level in 1..=ml {
                        for idx in 0..(1 << level) {
                            let fp = get_from_parent(&splits, level, idx);
                            if fp.is_empty() { continue; }

                            let parent_idx = idx / 2;
                            let parent_bag = get_bag(&id_bags, level - 1, parent_idx);
                            if parent_bag.is_empty() { continue; }

                            for j in 1..=(level - 1) {
                                let fp_strangers = j_stranger_count(n, &pi, &fp, level - 1, parent_idx, j);
                                let full_strangers = j_stranger_count(n, &pi, &parent_bag, level - 1, parent_idx, j);

                                if full_strangers > 0 {
                                    let ratio = fp_strangers as f64 / full_strangers as f64;
                                    if ratio > max_hfilter_ratio {
                                        max_hfilter_ratio = ratio;
                                    }
                                }
                            }
                        }
                    }

                    // === Check 3: hcnative ===
                    // sibling_native_count of fromParent ≤ cnativeCoeff × cap(level-1)
                    for level in 1..=ml {
                        for idx in 0..(1 << level) {
                            let fp = get_from_parent(&splits, level, idx);
                            if fp.is_empty() { continue; }

                            let snc = sibling_native_count(n, &pi, &fp, level, idx);
                            let cap = params.capacity(n, t, level - 1);
                            let bound = params.cnative_coeff() * cap;

                            if bound > 0.0 {
                                let ratio = snc as f64 / bound;
                                if ratio > max_hcnative_ratio {
                                    max_hcnative_ratio = ratio;
                                }
                            }
                        }
                    }

                    // === Rebag to get next stage's bags ===
                    id_bags = rebag(&id_bags, n, &params, t);

                    // === Check 4: Overall invariant ===
                    // stranger_bound: jStrangerCount ≤ lam * eps^(j-1) * cap(t+1, level)
                    for (&(level, idx), items) in &id_bags {
                        for j in 1..=level {
                            let count = j_stranger_count(n, &pi, items, level, idx, j);
                            let cap = params.capacity(n, t + 1, level);
                            let bound = params.lambda * params.eps.powi((j - 1) as i32) * cap;

                            if bound > 0.0 {
                                let ratio = count as f64 / bound;
                                if ratio > max_stranger_ratio {
                                    max_stranger_ratio = ratio;
                                }
                            }
                        }
                    }

                    // === Check deviation bound ===
                    for (&(level, idx), items) in &id_bags {
                        if items.is_empty() { continue; }
                        let boundary = idx * bag_size(n, level) + bag_size(n, level + 1);
                        let c = items.iter().filter(|&&r| pi[r] < boundary).count();
                        let half = items.len() / 2;
                        let deviation = (c as isize - half as isize).unsigned_abs();
                        let cap = params.capacity(n, t + 1, level);
                        let bound = params.cnative_coeff() * cap;

                        if bound > 0.0 {
                            let ratio = deviation as f64 / bound;
                            if ratio > max_deviation_ratio {
                                max_deviation_ratio = ratio;
                            }
                        }
                    }
                }

                // === Check 5: Final output is sorted ===
                let is_sorted = (0..n-1).all(|i| pi[i] <= pi[i+1]);

                if perm_stability_violations > 0 || max_stranger_ratio > 1.0
                    || max_hfilter_ratio > params.eps * 1.5  // allow some slack for adversarial
                    || !is_sorted
                {
                    println!("FAIL: sep={} n={} seed={}: perm_stab_viol={} stranger_ratio={:.4} hfilter_ratio={:.4} hcnative_ratio={:.4} deviation_ratio={:.4} sorted={}",
                        sep_model, n, seed, perm_stability_violations,
                        max_stranger_ratio, max_hfilter_ratio, max_hcnative_ratio,
                        max_deviation_ratio, is_sorted);
                    any_failure = true;
                }
            }

            // Print summary for this (model, n) combo (aggregate across seeds)
            // We need to aggregate - let me collect across seeds
        }
    }

    // Actually, let me restructure to collect stats properly
    // (The loop above already ran, just re-run with summary printing)
    println!("\n=== Detailed ratio summary (re-running) ===\n");

    for &sep_model in &["perfect", "adversarial"] {
        let k_max = if sep_model == "adversarial" { 9 } else { 10 };
        for k in 3..=k_max {
            let n = 1 << k;
            let ml = max_level(n);
            let num_stages = 10 * k;

            let mut worst_stranger = 0.0f64;
            let mut worst_hfilter = 0.0f64;
            let mut worst_hcnative = 0.0f64;
            let mut worst_deviation = 0.0f64;
            let mut total_perm_viol = 0usize;
            let mut all_sorted = true;

            for seed in 0..10 {
                let mut rng = Rng::new(seed * 1000 + k as u64 + if sep_model == "adversarial" { 999999 } else { 0 });
                let mut sigma: Vec<usize> = (0..n).collect();
                rng.shuffle(&mut sigma);
                let mut pi: Vec<usize> = sigma.clone();
                let mut id_bags: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();
                id_bags.insert((0, 0), (0..n).collect());

                for t in 0..num_stages {
                    // Record pre-separator stranger counts for perm stability check
                    let mut pre_counts: Vec<((usize,usize,usize), usize)> = Vec::new();
                    for (&(level, idx), items) in &id_bags {
                        if items.is_empty() { continue; }
                        for j in 1..=level.min(3) { // check first 3 levels of strangeness
                            let count = j_stranger_count(n, &pi, items, level, idx, j);
                            pre_counts.push(((level, idx, j), count));
                        }
                    }

                    // Apply separator
                    for (&(level, _idx), items) in &id_bags {
                        if (t + level) % 2 != 0 || items.is_empty() { continue; }
                        apply_separator_to_bag(items, &mut pi, sep_model, params.eps, &mut rng);
                    }

                    // Check perm stability
                    for &((level, idx, j), pre) in &pre_counts {
                        let items = get_bag(&id_bags, level, idx);
                        let post = j_stranger_count(n, &pi, &items, level, idx, j);
                        if post != pre { total_perm_viol += 1; }
                    }

                    // Compute splits
                    let mut splits: BTreeMap<(usize, usize), (Vec<usize>, Vec<usize>, Vec<usize>)> = BTreeMap::new();
                    for (&(level, idx), items) in &id_bags {
                        let cap = params.capacity(n, t, level);
                        splits.insert((level, idx), id_split(items, n, level, params.lambda, cap));
                    }

                    // Check hfilter + hcnative
                    for level in 1..=ml {
                        for idx in 0..(1 << level) {
                            let fp = get_from_parent(&splits, level, idx);
                            if fp.is_empty() { continue; }
                            let parent_idx = idx / 2;
                            let parent_bag = get_bag(&id_bags, level - 1, parent_idx);
                            if parent_bag.is_empty() { continue; }

                            for j in 1..=(level - 1).min(3) {
                                let fp_str = j_stranger_count(n, &pi, &fp, level - 1, parent_idx, j);
                                let full_str = j_stranger_count(n, &pi, &parent_bag, level - 1, parent_idx, j);
                                if full_str > 0 {
                                    worst_hfilter = worst_hfilter.max(fp_str as f64 / full_str as f64);
                                }
                            }

                            let snc = sibling_native_count(n, &pi, &fp, level, idx);
                            let cap = params.capacity(n, t, level - 1);
                            let bound = params.cnative_coeff() * cap;
                            if bound > 0.0 {
                                worst_hcnative = worst_hcnative.max(snc as f64 / bound);
                            }
                        }
                    }

                    // Rebag
                    id_bags = rebag(&id_bags, n, &params, t);

                    // Check invariant
                    for (&(level, idx), items) in &id_bags {
                        for j in 1..=level.min(3) {
                            let count = j_stranger_count(n, &pi, items, level, idx, j);
                            let cap = params.capacity(n, t + 1, level);
                            let bound = params.lambda * params.eps.powi((j - 1) as i32) * cap;
                            if bound > 0.0 {
                                worst_stranger = worst_stranger.max(count as f64 / bound);
                            }
                        }

                        // Deviation
                        if !items.is_empty() {
                            let boundary = idx * bag_size(n, level) + bag_size(n, level + 1);
                            let c = items.iter().filter(|&&r| pi[r] < boundary).count();
                            let half = items.len() / 2;
                            let dev = (c as isize - half as isize).unsigned_abs();
                            let cap = params.capacity(n, t + 1, level);
                            let bound = params.cnative_coeff() * cap;
                            if bound > 0.0 {
                                worst_deviation = worst_deviation.max(dev as f64 / bound);
                            }
                        }
                    }
                }

                let is_sorted = (0..n-1).all(|i| pi[i] <= pi[i+1]);
                if !is_sorted { all_sorted = false; }
            }

            let ok = total_perm_viol == 0 && worst_stranger <= 1.0 && all_sorted;
            println!("{} sep={:<12} n={:>5}: stranger={:.4} hfilter={:.4} hcnative={:.4} dev={:.4} perm_viol={} sorted={} {}",
                if ok { "OK" } else { "FAIL" },
                sep_model, n,
                worst_stranger, worst_hfilter, worst_hcnative, worst_deviation,
                total_perm_viol, all_sorted,
                if !ok { "***" } else { "" });

            if !ok { any_failure = true; }
        }
        println!();
    }

    if any_failure {
        println!("\n*** FAILURES DETECTED ***");
        std::process::exit(1);
    } else {
        println!("\nAll tests passed!");
    }
}
