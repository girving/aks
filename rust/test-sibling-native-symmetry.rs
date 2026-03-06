#!/usr/bin/env -S cargo +nightly -Zscript
//! Test whether sibling-native counts in kicks are equal: SL = SR?
//!
//! For the kick_native_deviation_bound proof, we need:
//!   |nLkL - nRkL + nLkR - nRkR| ≤ 2·lam·ε·cap
//!
//! My analysis shows this equals (XR - XL) + 2(SR - SL) where:
//! - XL, XR = 1-strangers at parent level in kL, kR (bounded by kick_stranger_bound)
//! - SL = sibling-native items in kL (contribute to nRkL)
//! - SR = sibling-native items in kR (contribute to nLkR)
//!
//! If SL = SR, the imbalance simplifies to XR - XL, bounded by 2·lam·ε·cap.
//! This test checks empirically whether SL ≈ SR.

use std::collections::BTreeSet;

const A: f64 = 10.0;
const NU: f64 = 0.65;
const LAM: f64 = 0.01;
const EPS: f64 = 0.01;

fn max_level(n: usize) -> usize {
    if n <= 1 { return 0; }
    (n as f64).log2().floor() as usize
}

fn bag_size(n: usize, level: usize) -> usize {
    if (1 << level) > n { return 0; }
    n / (1 << level)
}

fn bag_capacity(n: usize, t: usize, level: usize) -> f64 {
    n as f64 * NU.powi(t as i32) * A.powi(level as i32)
}

fn fringe_size(cap: f64) -> usize {
    (LAM * cap).floor().max(0.0) as usize
}

fn child_send_size(b: usize, cap: f64) -> usize {
    let f = fringe_size(cap);
    if f > b / 2 { 0 } else { b / 2 - f }
}

/// Check if item is a 1-stranger at (level, idx) but NOT a 2-stranger
/// This is the sibling-native condition
fn is_sibling_native(n: usize, perm_val: usize, level: usize, idx: usize) -> bool {
    let bs = bag_size(n, level);
    if bs == 0 { return false; }

    // Native bag index at this level
    let native_idx = perm_val / bs;

    // 1-stranger: native_idx != idx
    let is_1_stranger = native_idx != idx;

    // 2-stranger: native bag index at level-1 != idx/2
    let is_2_stranger = if level >= 1 {
        let bs_parent = bag_size(n, level - 1);
        if bs_parent == 0 { false }
        else {
            let native_parent_idx = perm_val / bs_parent;
            native_parent_idx != idx / 2
        }
    } else {
        false // Can't be 2-stranger at level 0
    };

    is_1_stranger && !is_2_stranger
}

/// Check if item is a 1-stranger at parent level (level, idx)
/// These are the "true strangers" that contribute to XL, XR
fn is_parent_stranger(n: usize, perm_val: usize, level: usize, idx: usize) -> bool {
    let bs = bag_size(n, level);
    if bs == 0 { return false; }
    let native_idx = perm_val / bs;
    native_idx != idx
}

#[derive(Clone)]
struct BagAssignment {
    n: usize,
    bags: Vec<Vec<BTreeSet<usize>>>,
}

impl BagAssignment {
    fn new(n: usize) -> Self {
        let ml = max_level(n);
        let mut bags = Vec::new();
        for level in 0..=ml + 1 {
            let count = 1usize.checked_shl(level as u32).unwrap_or(usize::MAX);
            bags.push(vec![BTreeSet::new(); count.min(n)]);
        }
        if !bags.is_empty() && !bags[0].is_empty() {
            for r in 0..n {
                bags[0][0].insert(r);
            }
        }
        BagAssignment { n, bags }
    }

    fn get(&self, level: usize, idx: usize) -> &BTreeSet<usize> {
        static EMPTY: std::sync::LazyLock<BTreeSet<usize>> =
            std::sync::LazyLock::new(BTreeSet::new);
        if level < self.bags.len() && idx < self.bags[level].len() {
            &self.bags[level][idx]
        } else {
            &EMPTY
        }
    }
}

fn rank_in_bag(perm: &[usize], bag: &BTreeSet<usize>, item: usize) -> usize {
    bag.iter().filter(|&&j| perm[j] < perm[item]).count()
}

fn split_bag(
    perm: &[usize], bag: &BTreeSet<usize>, n: usize, cap: f64, level: usize,
) -> (BTreeSet<usize>, BTreeSet<usize>, BTreeSet<usize>) {
    let b = bag.len();
    let ml = max_level(n);

    if ml <= level {
        return (bag.clone(), BTreeSet::new(), BTreeSet::new());
    }
    if level == 0 {
        let half = b / 2;
        let mut to_parent = BTreeSet::new();
        let mut to_left = BTreeSet::new();
        let mut to_right = BTreeSet::new();
        for &item in bag {
            let r = rank_in_bag(perm, bag, item);
            if r < half {
                to_left.insert(item);
            } else if r < 2 * half {
                to_right.insert(item);
            } else {
                to_parent.insert(item);
            }
        }
        return (to_parent, to_left, to_right);
    }

    let f = fringe_size(cap);
    let h = child_send_size(b, cap);
    let mut to_parent = BTreeSet::new();
    let mut to_left = BTreeSet::new();
    let mut to_right = BTreeSet::new();
    for &item in bag {
        let r = rank_in_bag(perm, bag, item);
        if r < f || r >= f + 2 * h {
            to_parent.insert(item);
        } else if r < f + h {
            to_left.insert(item);
        } else {
            to_right.insert(item);
        }
    }
    (to_parent, to_left, to_right)
}

/// Analyze sibling-native symmetry in kicks at a given rebag location
struct KickAnalysis {
    // Kick sizes
    kl_size: usize,
    kr_size: usize,
    // Sibling-native counts
    sl: usize,  // sibling-native in kL
    sr: usize,  // sibling-native in kR
    // Parent-level stranger counts
    xl: usize,  // 1-strangers at parent level in kL
    xr: usize,  // 1-strangers at parent level in kR
    // Native decomposition
    nl_kl: usize,  // items in kL with perm in left half of parent
    nr_kl: usize,  // items in kL with perm in right half of parent
    nl_kr: usize,  // items in kR with perm in left half of parent
    nr_kr: usize,  // items in kR with perm in right half of parent
    // The imbalance we're trying to bound
    imbalance: i64,
}

fn analyze_kicks(
    perm: &[usize],
    bags: &BagAssignment,
    t: usize,
    level: usize,
    idx: usize,
) -> Option<KickAnalysis> {
    let n = bags.n;
    let ml = max_level(n);

    // Skip if children are out of range
    if level + 1 > ml { return None; }
    let child_l_idx = 2 * idx;
    let child_r_idx = 2 * idx + 1;
    if child_l_idx >= (1 << (level + 1)) { return None; }

    let cap = bag_capacity(n, t, level + 1);

    // Get child bags
    let bag_l = bags.get(level + 1, child_l_idx);
    let bag_r = bags.get(level + 1, child_r_idx);

    if bag_l.is_empty() && bag_r.is_empty() { return None; }

    // Split children
    let (kl, _, _) = split_bag(perm, bag_l, n, cap, level + 1);
    let (kr, _, _) = split_bag(perm, bag_r, n, cap, level + 1);

    if kl.is_empty() && kr.is_empty() { return None; }

    // Parent region boundaries
    let lo = idx * bag_size(n, level);
    let boundary = lo + bag_size(n, level + 1);
    let hi = lo + bag_size(n, level);

    // Count sibling-natives and strangers in each kick
    let mut sl = 0usize;
    let mut xl = 0usize;
    let mut nl_kl = 0usize;
    let mut nr_kl = 0usize;

    for &item in &kl {
        let pv = perm[item];
        // Sibling-native at child level (level+1, child_l_idx)
        if is_sibling_native(n, pv, level + 1, child_l_idx) {
            sl += 1;
        }
        // Parent-level stranger (level, idx)
        if is_parent_stranger(n, pv, level, idx) {
            xl += 1;
        }
        // Count by position relative to parent boundary
        if lo <= pv && pv < boundary {
            nl_kl += 1;
        } else if boundary <= pv && pv < hi {
            nr_kl += 1;
        }
    }

    let mut sr = 0usize;
    let mut xr = 0usize;
    let mut nl_kr = 0usize;
    let mut nr_kr = 0usize;

    for &item in &kr {
        let pv = perm[item];
        if is_sibling_native(n, pv, level + 1, child_r_idx) {
            sr += 1;
        }
        if is_parent_stranger(n, pv, level, idx) {
            xr += 1;
        }
        if lo <= pv && pv < boundary {
            nl_kr += 1;
        } else if boundary <= pv && pv < hi {
            nr_kr += 1;
        }
    }

    let imbalance = (nl_kl as i64 - nr_kl as i64) + (nl_kr as i64 - nr_kr as i64);

    Some(KickAnalysis {
        kl_size: kl.len(),
        kr_size: kr.len(),
        sl, sr, xl, xr,
        nl_kl, nr_kl, nl_kr, nr_kr,
        imbalance,
    })
}

fn do_stage(bags: &BagAssignment, perm: &[usize], t: usize) -> BagAssignment {
    let n = bags.n;
    let ml = max_level(n);

    let mut splits: Vec<Vec<(BTreeSet<usize>, BTreeSet<usize>, BTreeSet<usize>)>> = Vec::new();
    for level in 0..=ml + 1 {
        let count = 1usize.checked_shl(level as u32).unwrap_or(usize::MAX).min(n);
        let cap = bag_capacity(n, t, level);
        let mut level_splits = Vec::new();
        for idx in 0..count {
            let bag = bags.get(level, idx);
            level_splits.push(split_bag(perm, bag, n, cap, level));
        }
        splits.push(level_splits);
    }

    let mut new_bags = BagAssignment {
        n,
        bags: vec![vec![BTreeSet::new(); 1]; ml + 2],
    };
    for level in 0..=ml + 1 {
        let count = 1usize.checked_shl(level as u32).unwrap_or(usize::MAX).min(n);
        new_bags.bags[level] = vec![BTreeSet::new(); count];
    }

    for level in 0..=ml {
        let count = 1usize.checked_shl(level as u32).unwrap_or(usize::MAX).min(n);
        for idx in 0..count {
            let child_l = 2 * idx;
            let child_r = 2 * idx + 1;

            if level + 1 < splits.len() {
                if child_l < splits[level + 1].len() {
                    for &item in &splits[level + 1][child_l].0 {
                        new_bags.bags[level][idx].insert(item);
                    }
                }
                if child_r < splits[level + 1].len() {
                    for &item in &splits[level + 1][child_r].0 {
                        new_bags.bags[level][idx].insert(item);
                    }
                }
            }

            if level > 0 {
                let parent_idx = idx / 2;
                if parent_idx < splits[level - 1].len() {
                    let from_parent = if idx % 2 == 0 {
                        &splits[level - 1][parent_idx].1
                    } else {
                        &splits[level - 1][parent_idx].2
                    };
                    for &item in from_parent {
                        new_bags.bags[level][idx].insert(item);
                    }
                }
            }
        }
    }

    new_bags
}

fn main() {
    println!("Testing sibling-native symmetry: SL vs SR in kicks\n");
    println!("Parameters: A={}, ν={}, λ={}, ε={}", A, NU, LAM, EPS);
    println!();

    let mut max_sl_sr_diff = 0i64;
    let mut max_sl_sr_diff_case = String::new();
    let mut total_cases = 0usize;
    let mut exact_equality_cases = 0usize;
    let mut cases_with_large_diff = 0usize;

    // Also track actual imbalance vs bound
    let mut max_imbalance_ratio = 0.0f64;

    // Track ratio relative to total budget (2*cnativeCoeff - lam) * cap
    let cnative_coeff = {
        let e2a2 = (2.0 * EPS * A) * (2.0 * EPS * A);
        EPS / 2.0 + 2.0 * LAM * EPS * A * A / (1.0 - e2a2) + 1.0 / (8.0 * A * A - 2.0)
    };
    let total_budget_coeff = 2.0 * cnative_coeff - LAM;
    let mut max_total_ratio = 0.0f64;
    let mut max_total_case = String::new();

    // Track what fraction of the TOTAL budget the kick imbalance uses
    let mut max_kick_of_total = 0.0f64;

    for k in 4..=10 {
        let n = 1 << k;
        let perm: Vec<usize> = (0..n).collect(); // Identity permutation initially
        let mut bags = BagAssignment::new(n);

        for t in 0..50 {
            let ml = max_level(n);

            for level in 0..ml {
                let count = 1usize.checked_shl(level as u32).unwrap_or(usize::MAX).min(n);
                for idx in 0..count {
                    if let Some(analysis) = analyze_kicks(&perm, &bags, t, level, idx) {
                        total_cases += 1;

                        let sl_sr_diff = (analysis.sr as i64 - analysis.sl as i64).abs();

                        if analysis.sl == analysis.sr {
                            exact_equality_cases += 1;
                        }

                        if sl_sr_diff > max_sl_sr_diff {
                            max_sl_sr_diff = sl_sr_diff;
                            max_sl_sr_diff_case = format!(
                                "n={} t={} level={} idx={}: kL={} kR={} SL={} SR={} XL={} XR={}",
                                n, t, level, idx,
                                analysis.kl_size, analysis.kr_size,
                                analysis.sl, analysis.sr, analysis.xl, analysis.xr
                            );
                        }

                        // Check formula: imbalance should equal (XR - XL) + 2(SR - SL)
                        // But actually, let me verify: nLkL = items native to left, etc.
                        // From my analysis:
                        // - nRkL = SL (sibling-native in kL all have perm >= boundary)
                        // - nLkR = SR (sibling-native in kR all have perm < boundary)
                        // - nLkL = kL items with perm in [lo, boundary) that are NOT sibling-native
                        // - nRkR = kR items with perm in [boundary, hi) that are NOT sibling-native
                        //
                        // Actually let's verify by direct computation:
                        // nRkL should equal SL if all sibling-native in kL go to right
                        let nr_kl_vs_sl = analysis.nr_kl as i64 - analysis.sl as i64;
                        let nl_kr_vs_sr = analysis.nl_kr as i64 - analysis.sr as i64;

                        // These should be 0 if sibling-native characterization is correct
                        // (sibling-native from even child go right, from odd child go left)
                        // But they might not be exactly SL/SR due to parent-level strangers

                        // The expected formula for imbalance:
                        // = (nLkL - nRkL) + (nLkR - nRkR)
                        // = (nLkL + nLkR) - (nRkL + nRkR)
                        let computed_imbalance = (analysis.nl_kl as i64 - analysis.nr_kl as i64)
                            + (analysis.nl_kr as i64 - analysis.nr_kr as i64);

                        if computed_imbalance != analysis.imbalance {
                            println!("BUG: imbalance mismatch at n={} t={} level={} idx={}", n, t, level, idx);
                        }

                        // Check if imbalance is bounded by 2*lam*eps*cap
                        let cap_t1_level = bag_capacity(n, t + 1, level);
                        let kick_bound = 2.0 * LAM * EPS * cap_t1_level;
                        if kick_bound > 0.001 {
                            let ratio = analysis.imbalance.abs() as f64 / kick_bound;
                            if ratio > max_imbalance_ratio {
                                max_imbalance_ratio = ratio;
                            }
                            if ratio > 1.0 {
                                cases_with_large_diff += 1;
                            }
                        }

                        // Check ratio relative to total budget
                        let total_bound = total_budget_coeff * cap_t1_level;
                        if total_bound > 0.001 {
                            let ratio = analysis.imbalance.abs() as f64 / total_bound;
                            if ratio > max_total_ratio {
                                max_total_ratio = ratio;
                                max_total_case = format!(
                                    "n={} t={} lev={} idx={}: imbal={} total_bound={:.2} ratio={:.4} SL={} SR={} XL={} XR={}",
                                    n, t, level, idx, analysis.imbalance, total_bound, ratio,
                                    analysis.sl, analysis.sr, analysis.xl, analysis.xr
                                );
                            }
                            let kick_frac = analysis.imbalance.abs() as f64 / total_bound;
                            if kick_frac > max_kick_of_total {
                                max_kick_of_total = kick_frac;
                            }
                        }
                    }
                }
            }

            bags = do_stage(&bags, &perm, t);
        }
    }

    println!("Results:");
    println!("  Total kick analysis cases: {}", total_cases);
    println!("  Cases with SL = SR exactly: {} ({:.1}%)",
        exact_equality_cases,
        100.0 * exact_equality_cases as f64 / total_cases as f64);
    println!();
    println!("  Max |SL - SR|: {}", max_sl_sr_diff);
    println!("  Worst case: {}", max_sl_sr_diff_case);
    println!();
    println!("  Max imbalance / (2·λ·ε·cap(t+1,level)) ratio: {:.4}", max_imbalance_ratio);
    println!("  Cases exceeding kick bound: {}", cases_with_large_diff);
    println!();
    println!("  cnativeCoeff = {:.6}", cnative_coeff);
    println!("  Total budget coeff (2·cnativeCoeff - lam) = {:.6}", total_budget_coeff);
    println!("  kickCoeff (2·lam·ε) = {:.6}", 2.0 * LAM * EPS);
    println!("  kickCoeff / total = {:.4}", 2.0 * LAM * EPS / total_budget_coeff);
    println!();
    println!("  Max kick imbalance / total_budget: {:.4}", max_total_ratio);
    println!("  Worst total case: {}", max_total_case);

    // Additional analysis: check formula components
    println!("\n--- Detailed formula check ---");

    // Re-run with more detail on a specific case
    let n = 256;
    let perm: Vec<usize> = (0..n).collect();
    let mut bags = BagAssignment::new(n);

    println!("\nSample cases at n={}:", n);
    for t in 0..10 {
        let ml = max_level(n);
        for level in 0..ml.min(3) {
            let count = 1usize.checked_shl(level as u32).unwrap_or(usize::MAX).min(n);
            for idx in 0..count.min(2) {
                if let Some(a) = analyze_kicks(&perm, &bags, t, level, idx) {
                    if a.kl_size > 0 || a.kr_size > 0 {
                        println!("  t={} lev={} idx={}: |kL|={} |kR|={} SL={} SR={} XL={} XR={} imbal={}",
                            t, level, idx, a.kl_size, a.kr_size, a.sl, a.sr, a.xl, a.xr, a.imbalance);

                        // Verify: nr_kl should be close to sl (sibling-native go to right)
                        // Actually, sibling-native in kL have perm in sibling region, which is [boundary, hi)
                        // So they contribute to nr_kl
                        // But some items in nr_kl might be parent-level strangers with perm in [boundary, hi)
                        // Wait, parent-level strangers have perm OUTSIDE [lo, hi), so they don't contribute
                        // Therefore nr_kl = sl exactly!
                        if a.nr_kl != a.sl {
                            println!("    NOTE: nr_kl={} but sl={}", a.nr_kl, a.sl);
                        }
                        if a.nl_kr != a.sr {
                            println!("    NOTE: nl_kr={} but sr={}", a.nl_kr, a.sr);
                        }
                    }
                }
            }
        }
        bags = do_stage(&bags, &perm, t);
    }
}
