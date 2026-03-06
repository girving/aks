#!/usr/bin/env -S cargo +nightly -Zscript
//! Test the RELATIVE stranger bound: jStrangerCount / bagCard ≤ λ.
//!
//! The cap-based invariant gives: jStrangerCount ≤ λ · ε^{j-1} · cap.
//! For the SepInitial argument (filtering), we also need: jStrangerCount / m ≤ λ
//! (the stranger FRACTION is bounded by λ, regardless of cap/m ratio).
//!
//! This test checks whether jStrangerCount(j=1) ≤ λ · m holds at every stage
//! and level, with both perfect and adversarial separators.
//! Also checks the ratio jStrangerCount(j=1) / m and reports the maximum.

use std::collections::BTreeMap;

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

fn bag_size(n: usize, level: usize) -> usize { n >> level }

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

fn fringe_size(lambda: f64, cap: f64) -> usize {
    (lambda * cap).floor() as usize
}

fn child_send_size(lambda: f64, b: usize, cap: f64) -> usize {
    let f = fringe_size(lambda, cap);
    (b / 2).saturating_sub(f)
}

fn capacity(n: usize, t: usize, level: usize, a: f64, nu: f64) -> f64 {
    (n as f64) * nu.powi(t as i32) * a.powi(level as i32)
}

/// Split by position rank (perm = id)
fn id_split(items: &[usize], n: usize, level: usize, lambda: f64, cap: f64) -> (Vec<usize>, Vec<usize>, Vec<usize>) {
    let ml = max_level(n);
    if level >= ml {
        return (items.to_vec(), vec![], vec![]);
    }
    let b = items.len();
    if level == 0 {
        let mut sorted = items.to_vec();
        sorted.sort();
        let half = b / 2;
        let to_left: Vec<usize> = sorted.iter().take(half).copied().collect();
        let to_right: Vec<usize> = sorted.iter().skip(half).take(half).copied().collect();
        let to_parent: Vec<usize> = sorted.iter().skip(2 * half).copied().collect();
        return (to_parent, to_left, to_right);
    }
    let mut sorted = items.to_vec();
    sorted.sort();
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

/// Apply separator (sort values within bag, then introduce adversarial errors)
fn apply_separator(positions: &[usize], perm: &mut [usize], adversarial: bool, eps: f64, rng: &mut Rng) {
    if positions.len() <= 1 { return; }
    let mut pairs: Vec<(usize, usize)> = positions.iter().map(|&p| (p, perm[p])).collect();
    pairs.sort_by_key(|&(_, v)| v);
    let mut sorted_positions: Vec<usize> = positions.to_vec();
    sorted_positions.sort();
    let values: Vec<usize> = pairs.iter().map(|&(_, v)| v).collect();
    for (i, &pos) in sorted_positions.iter().enumerate() {
        perm[pos] = values[i];
    }
    if adversarial {
        let m = positions.len();
        let half = m / 2;
        let errors = (eps * half as f64).floor() as usize;
        if errors > 0 && half > 0 {
            for k in 0..errors.min(half) {
                let lp = sorted_positions[half - 1 - k];
                let rp = sorted_positions[half + k];
                let tmp = perm[lp]; perm[lp] = perm[rp]; perm[rp] = tmp;
            }
        }
    }
}

fn rebag(
    bags: &BTreeMap<(usize, usize), Vec<usize>>,
    n: usize, t: usize, lambda: f64, a: f64, nu: f64,
) -> BTreeMap<(usize, usize), Vec<usize>> {
    let ml = max_level(n);
    let mut splits: BTreeMap<(usize, usize), (Vec<usize>, Vec<usize>, Vec<usize>)> = BTreeMap::new();
    for (&(level, idx), items) in bags {
        let cap = capacity(n, t, level, a, nu);
        splits.insert((level, idx), id_split(items, n, level, lambda, cap));
    }
    let mut new_bags: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();
    for level in 0..=ml {
        for idx in 0..(1 << level) {
            let mut bag = Vec::new();
            if let Some((tp, _, _)) = splits.get(&(level + 1, 2 * idx)) { bag.extend(tp); }
            if let Some((tp, _, _)) = splits.get(&(level + 1, 2 * idx + 1)) { bag.extend(tp); }
            if level > 0 {
                if let Some((_, tl, tr)) = splits.get(&(level - 1, idx / 2)) {
                    if idx % 2 == 0 { bag.extend(tl); } else { bag.extend(tr); }
                }
            }
            if !bag.is_empty() { new_bags.insert((level, idx), bag); }
        }
    }
    new_bags
}

fn main() {
    let a = 10.0_f64;
    let nu = 13.0 / 20.0;
    let lambda = 1.0 / 100.0;
    let eps = 1.0 / 100.0;

    println!("=== Relative Stranger Bound Test ===");
    println!("Testing: jStrangerCount(j=1) / bag_card ≤ λ = {}", lambda);
    println!("Params: A={}, ν={}, λ={}, ε={}\n", a, nu, lambda, eps);

    for &adversarial in &[false, true] {
        let model_name = if adversarial { "adversarial" } else { "perfect" };
        println!("--- Separator model: {} ---", model_name);

        let mut global_max_ratio = 0.0_f64;
        let mut global_max_info = String::new();
        let mut violations = 0usize;
        let mut total_checks = 0usize;

        let k_max = if adversarial { 10 } else { 12 };
        for k in 3..=k_max {
            let n = 1 << k;
            let ml = max_level(n);
            let num_stages = 10 * k;

            for seed in 0..10 {
                let mut rng = Rng::new(seed * 7919 + k as u64 + if adversarial { 50000 } else { 0 });
                let mut pi: Vec<usize> = (0..n).collect();
                rng.shuffle(&mut pi);
                let mut bags: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();
                bags.insert((0, 0), (0..n).collect());

                for t in 0..num_stages {
                    // Apply separator
                    for (&(level, _idx), items) in &bags {
                        if (t + level) % 2 != 0 { continue; }
                        if items.is_empty() { continue; }
                        apply_separator(items, &mut pi, adversarial, eps, &mut rng);
                    }

                    // Rebag
                    bags = rebag(&bags, n, t, lambda, a, nu);

                    // Check relative stranger bound on NEW bags (stage t+1)
                    for (&(level, idx), items) in &bags {
                        let m = items.len();
                        if m == 0 { continue; }

                        for j in 1..=level.min(5) {
                            let s = j_stranger_count(n, &pi, items, level, idx, j);
                            let bound = (lambda * m as f64).floor() as usize;
                            let ratio = s as f64 / (lambda * m as f64).max(1e-10);
                            total_checks += 1;

                            if ratio > global_max_ratio {
                                global_max_ratio = ratio;
                                let cap = capacity(n, t + 1, level, a, nu);
                                global_max_info = format!(
                                    "n={} t={} level={} idx={} j={} s={} m={} cap={:.1} s/m={:.6} λ·m={:.1} λ·cap={:.1} cap/m={:.1}",
                                    n, t + 1, level, idx, j, s, m, cap,
                                    s as f64 / m as f64, lambda * m as f64, lambda * cap, cap / m as f64
                                );
                            }

                            if s > bound + 1 { // +1 for floor rounding
                                violations += 1;
                                if violations <= 5 {
                                    let cap = capacity(n, t + 1, level, a, nu);
                                    println!("  VIOLATION: n={} t={} lev={} idx={} j={} s={} m={} bound={} cap/m={:.1}",
                                        n, t + 1, level, idx, j, s, m, bound, cap / m as f64);
                                }
                            }
                        }
                    }
                }
            }
        }

        println!("  Total checks: {}", total_checks);
        println!("  Violations (s > ⌊λ·m⌋+1): {}", violations);
        println!("  Max ratio s/(λ·m): {:.6}", global_max_ratio);
        println!("  Worst case: {}", global_max_info);
        println!();
    }
}
