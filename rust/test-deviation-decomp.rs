#!/usr/bin/env -S cargo +nightly -Zscript
//! Diagnostic test for the deviation decomposition:
//!   C_new - b_new/2 = (L_R - R_L) + (Cfp - |fp|/2)
//!
//! Checks:
//! 1. The decomposition identity holds
//! 2. How |L_R - R_L| compares to individual bounds (lam·A·cap) vs budget (cnativeCoeff·cap(t+1))
//! 3. Whether L_R - R_L + Cfp - |fp|/2 can be related to the parent's deviation at our boundary
//! 4. How the parent's deviation at our boundary relates to inv.deviation_bound at the parent's own boundary (hi)

use std::collections::BTreeSet;

const A: f64 = 10.0;
const NU: f64 = 0.65;
const LAM: f64 = 0.01;
const EPS: f64 = 0.01;

fn bag_size(n: usize, level: usize) -> usize {
    if (1usize << level) > n { return 0; }
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

fn max_level(n: usize) -> usize {
    if n <= 1 { 0 } else { (n as f64).log2().floor() as usize - 1 }
}

fn cnative_coeff() -> f64 {
    let ea = 2.0 * EPS * A;
    EPS / 2.0 + 2.0 * LAM * EPS * A * A / (1.0 - ea * ea) + 1.0 / (8.0 * A * A - 2.0)
}

/// Rank of item `i` among `regs` by perm value
fn rank_in_bag(perm: &[usize], regs: &BTreeSet<usize>, i: usize) -> usize {
    regs.iter().filter(|&&j| perm[j] < perm[i]).count()
}

/// Concrete split: returns (toParent, toLeftChild, toRightChild) as BTreeSets
fn concrete_split(
    n: usize, perm: &[usize], bag: &BTreeSet<usize>, cap: f64, level: usize,
) -> (BTreeSet<usize>, BTreeSet<usize>, BTreeSet<usize>) {
    let b = bag.len();
    if max_level(n) <= level {
        return (bag.clone(), BTreeSet::new(), BTreeSet::new());
    }
    if level == 0 {
        let half = b / 2;
        let mut tp = BTreeSet::new();
        let mut lc = BTreeSet::new();
        let mut rc = BTreeSet::new();
        for &i in bag {
            let r = rank_in_bag(perm, bag, i);
            if r < half { lc.insert(i); }
            else if r < 2 * half { rc.insert(i); }
            else { tp.insert(i); }
        }
        return (tp, lc, rc);
    }
    let f = fringe_size(cap);
    let h = child_send_size(b, cap);
    let mut tp = BTreeSet::new();
    let mut lc = BTreeSet::new();
    let mut rc = BTreeSet::new();
    for &i in bag {
        let r = rank_in_bag(perm, bag, i);
        if r < f || r >= f + 2 * h {
            tp.insert(i);
        } else if r < f + h {
            lc.insert(i);
        } else {
            rc.insert(i);
        }
    }
    (tp, lc, rc)
}

fn main() {
    let cnc = cnative_coeff();
    println!("cnativeCoeff = {:.6}", cnc);
    println!("2*cnativeCoeff - lam = {:.6}", 2.0 * cnc - LAM);
    println!();

    let mut max_ratio = 0.0f64;
    let mut max_lr_minus_rl = 0.0f64;
    let mut max_cfp_dev = 0.0f64;
    let mut max_combined = 0.0f64;
    let mut violations = 0u64;
    let mut checks = 0u64;

    for k in 3..=10 {
        let n = 1 << k;
        for t in 0..=20 {
            // Initialize bags: all items in root at t=0
            let mut bags: Vec<Vec<BTreeSet<usize>>> = vec![vec![BTreeSet::new(); n]; k + 1];

            // Random permutation
            let mut perm: Vec<usize> = (0..n).collect();
            // Simple deterministic shuffle based on t, k
            let seed = (t * 1000 + k * 7) as u64;
            let mut rng = seed;
            for i in (1..n).rev() {
                rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                let j = (rng >> 33) as usize % (i + 1);
                perm.swap(i, j);
            }

            bags[0][0] = (0..n).collect();

            // Run t stages
            for stage in 0..t {
                let cap_fn = |level: usize| bag_capacity(n, stage, level);
                let mut new_bags = vec![vec![BTreeSet::new(); n]; k + 1];

                for level in 0..=k {
                    for idx in 0..(1 << level).min(n) {
                        let (tp, lc, rc) = concrete_split(n, &perm, &bags[level][idx], cap_fn(level), level);

                        // kL/kR to parent
                        if level > 0 {
                            for &i in &tp {
                                new_bags[level - 1][idx / 2].insert(i);
                            }
                        }
                        // toLeftChild to child
                        if level + 1 <= k {
                            for &i in &lc {
                                new_bags[level + 1][2 * idx].insert(i);
                            }
                            for &i in &rc {
                                new_bags[level + 1][2 * idx + 1].insert(i);
                            }
                        }
                    }
                }
                bags = new_bags;
            }

            // Now check the deviation decomposition at each (level, idx)
            let cap_fn = |level: usize| bag_capacity(n, t, level);

            for level in 1..k {
                for idx in 0..(1usize << level).min(n) {
                    let lo = idx * bag_size(n, level);
                    let boundary = lo + bag_size(n, level + 1);
                    let hi = lo + bag_size(n, level);

                    // Children
                    let left_child = &bags[level + 1][2 * idx];
                    let right_child = &bags[level + 1][2 * idx + 1];

                    // Split children
                    let (kl, ml_l, ml_r) = concrete_split(n, &perm, left_child, cap_fn(level + 1), level + 1);
                    let (kr, mr_l, mr_r) = concrete_split(n, &perm, right_child, cap_fn(level + 1), level + 1);

                    // Parent
                    let parent_idx = idx / 2;
                    let parent = &bags[level - 1][parent_idx];
                    let (_kp, fp_or_sib_l, fp_or_sib_r) = concrete_split(n, &perm, parent, cap_fn(level - 1), level - 1);

                    let fp = if idx % 2 == 0 { &fp_or_sib_l } else { &fp_or_sib_r };

                    // Rebag = kL ∪ kR ∪ fp
                    let mut rebag = BTreeSet::new();
                    for &i in kl.iter().chain(kr.iter()).chain(fp.iter()) {
                        rebag.insert(i);
                    }
                    let b_new = rebag.len();

                    // C_new = items in rebag below boundary
                    let c_new = rebag.iter().filter(|&&i| perm[i] < boundary).count();

                    // Deviation
                    let dev = c_new as f64 - b_new as f64 / 2.0;

                    // L_R = items in right child with perm < boundary
                    let l_r: usize = right_child.iter().filter(|&&i| perm[i] < boundary).count();
                    // R_L = items in left child with perm >= boundary
                    let r_l: usize = left_child.iter().filter(|&&i| perm[i] >= boundary).count();

                    // Cfp = items in fp below boundary
                    let cfp: usize = fp.iter().filter(|&&i| perm[i] < boundary).count();
                    let fp_sz = fp.len();

                    // Check decomposition: C_new - b/2 = (L_R - R_L) + (Cfp - |fp|/2)
                    let kick_dev = (kl.len() as f64 / 2.0 - r_l as f64) + (l_r as f64 - kr.len() as f64 / 2.0);
                    let fp_dev = cfp as f64 - fp_sz as f64 / 2.0;
                    // Note: dev ≈ kick_dev + fp_dev (up to parity)

                    let combined = (l_r as i64 - r_l as i64) as f64 + (cfp as f64 - fp_sz as f64 / 2.0);

                    // Parent's deviation at OUR boundary
                    let c_parent_at_bdy = parent.iter().filter(|&&i| perm[i] < boundary).count();
                    let parent_dev_at_bdy = c_parent_at_bdy as f64 - parent.len() as f64 / 2.0;

                    // Parent's deviation at hi (its own boundary)
                    let c_parent_at_hi = parent.iter().filter(|&&i| perm[i] < hi).count();
                    let parent_dev_at_hi = c_parent_at_hi as f64 - parent.len() as f64 / 2.0;

                    // Old bag at (level, idx) deviation at our boundary
                    let old_bag = &bags[level][idx];
                    let c_old = old_bag.iter().filter(|&&i| perm[i] < boundary).count();
                    let old_dev = c_old as f64 - old_bag.len() as f64 / 2.0;

                    let cap_t1 = bag_capacity(n, t + 1, level);
                    let budget = cnc * cap_t1;

                    if b_new > 0 {
                        let ratio = dev.abs() / budget;
                        max_ratio = max_ratio.max(ratio);
                        max_lr_minus_rl = max_lr_minus_rl.max((l_r as f64 - r_l as f64).abs());
                        max_cfp_dev = max_cfp_dev.max(fp_dev.abs());
                        max_combined = max_combined.max(combined.abs());
                        checks += 1;

                        if dev.abs() > budget + 0.5 {
                            violations += 1;
                        }

                        // Check the exact identity: C - floor(b/2) = L_R - R_L + Cfp - floor(|fp|/2)
                        // when |kL| = |kR|
                        let c_minus_bh = c_new as i64 - (b_new / 2) as i64;
                        let formula = l_r as i64 - r_l as i64 + cfp as i64 - (fp_sz / 2) as i64;
                        let identity_ok = c_minus_bh == formula;

                        // Compute bound terms
                        let cap_t_level = bag_capacity(n, t, level);
                        let cap_t_level_minus1 = if level > 0 { bag_capacity(n, t, level - 1) } else { bag_capacity(n, t, 0) };
                        let cnc_cap_t1 = cnc * bag_capacity(n, t + 1, level);
                        let cnc_cap_parent = cnc * cap_t_level_minus1;

                        // Check if concreteSplit_cnative_bound on fp would bound the formula
                        let sn_fp_bound = cnc * cap_t_level_minus1;  // concreteSplit_cnative_bound

                        let parent_bound_ok = (formula.unsigned_abs() as f64) <= cnc_cap_parent + 0.5;
                        if !identity_ok || !parent_bound_ok || (formula.unsigned_abs() as f64 > cnc_cap_t1 + 0.5) {
                            println!("k={} t={} level={} idx={}: C-b/2={} formula={} identity={} |kL|={} |kR|={} |fp|={} L_R={} R_L={} Cfp={} fp/2={} cnc*cap(t+1)={:.1} cnc*cap(par)={:.1}",
                                k, t, level, idx, c_minus_bh, formula, identity_ok, kl.len(), kr.len(), fp_sz, l_r, r_l, cfp, fp_sz/2, cnc_cap_t1, cnc_cap_parent);
                        }
                    }
                }
            }
        }
    }

    println!("\n=== Summary ===");
    println!("Checks: {}", checks);
    println!("Violations: {}", violations);
    println!("Max |dev|/budget ratio: {:.4}", max_ratio);
    println!("Max |L_R - R_L|: {:.1}", max_lr_minus_rl);
    println!("Max |Cfp - fp/2|: {:.1}", max_cfp_dev);
    println!("Max |combined|: {:.1}", max_combined);
}
