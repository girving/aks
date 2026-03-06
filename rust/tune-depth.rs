#!/usr/bin/env -S cargo +nightly -Zscript
---
[dependencies]
num = "0.4"
---

//! Comprehensive search to minimize `seiferasParams.depth` (AKS/Bags/Depth.lean).
//!
//! # Background
//!
//! The Seiferas sorting network depth decomposes as:
//!   depth = stagesFactor × separatorDepth + 9
//!         = stagesFactor × (2·(numSepLevels+1)+1) × halverDepth(ε₀) + 9
//! where halverDepth uses the MGG expander with p graph squarings:
//!   halverDepth(ε₀) = 8^(2^p) × (7·Q₀+10)
//! and p is the smallest integer with (89/100)^(2^p) ≤ ε₀.
//!
//! The depth is utterly dominated by 8^(2^p) ≈ 2^192 for p=6, so we can write:
//!   depth ≈ cofactor × 8^64 + 9
//! where cofactor = stagesFactor × (2·(numSepLevels+1)+1) × (7·Q₀+10).
//!
//! # Results
//!
//! All feasible (A, γ, ε) parameters give p=6 — reducing to p=5 is infeasible
//! (see tune-depth3.rs for analysis). Within p=6, the best cofactor improvement
//! is ~1.4× at A=8, γ=1/64 (cofactor ~1.6M vs current ~2.2M).
//!
//! # Seiferas `Params` constraints (from AKS/Bags/Params.lean)
//!
//!   ε < 1/(2A)           [h2εA]
//!   γ ≥ 1/A²             [hA2_le]
//!   ν ≥ 4γA + 5/(2A)     [hC3]
//!   2Aε + 1/A ≤ ν        [hC4_gt1]
//!   j=1 master ≤ γν      [hC4_eq1: the tightest constraint on ε]
//!   ν < 1
//!
//! The j=1 constraint (hC4_eq1) dominates and severely limits ε, which in turn
//! forces large numSepLevels and stagesFactor.
//!
//! Run: CARGO_HOME=/tmp/cargo CARGO_TARGET_DIR=/tmp/cargo-target cargo +nightly -Zscript rust/tune-depth.rs

use num::rational::BigRational;
use num::bigint::BigInt;
use num::traits::{One, Zero, Pow};
use num::Integer;
use std::cmp::max;

type R = BigRational;

fn rat(n: i64, d: i64) -> R { R::new(BigInt::from(n), BigInt::from(d)) }
fn rnat(n: u64) -> R { R::new(BigInt::from(n), BigInt::from(1u64)) }

fn ceil_nat(r: &R) -> u64 {
    if r <= &R::zero() { return 0; }
    let (q, rem) = r.numer().div_rem(r.denom());
    let q: u64 = q.try_into().unwrap_or(u64::MAX);
    if rem.is_zero() { q } else { q + 1 }
}

fn clog2(n: u64) -> u64 {
    if n <= 1 { 0 } else { 64 - (n - 1).leading_zeros() as u64 }
}

fn num_sep_levels(gamma: &R) -> u64 {
    if gamma <= &R::zero() { return 0; }
    clog2(ceil_nat(&(R::one() / (rat(2, 1) * gamma))))
}

fn sep_total_layers(gamma: &R) -> u64 { num_sep_levels(gamma) + 2 }

fn stages_factor(nu: &R, a: &R) -> u64 {
    let two_a = rat(2, 1) * a;
    let one = R::one();
    let mut power = R::one();
    for c in 0..10000 {
        if &power * &two_a < one { return c; }
        power = power * nu;
    }
    10000
}

/// j=1 LHS - γν (negative means constraint satisfied)
fn j1_slack(gamma: &R, eps: &R, nu: &R, a: &R) -> R {
    let one = R::one();
    let two_eps_a = rat(2, 1) * eps * a;
    let denom = &one - two_eps_a.clone().pow(2u32);
    let eight_a3_minus_2a = rat(8, 1) * a.clone().pow(3u32) - rat(2, 1) * a;
    let lhs = rat(2, 1) * gamma * eps * a
        + eps * gamma / a
        + eps / (rat(2, 1) * a)
        + rat(2, 1) * gamma * eps * a / &denom
        + R::one() / &eight_a3_minus_2a
        + gamma / a
        + R::one() / &eight_a3_minus_2a;
    lhs - gamma * nu
}

/// Check all constraints
fn check_all(gamma: &R, eps: &R, nu: &R, a: &R) -> bool {
    let one = R::one();
    let zero = R::zero();
    if gamma <= &zero || gamma > &rat(1, 2) { return false; }
    if eps <= &zero || eps >= &one { return false; }
    if a <= &one { return false; }
    if nu <= &zero || nu >= &one { return false; }
    if (rat(2, 1) * eps * a).pow(2u32) >= one { return false; }
    if nu < &(rat(4, 1) * gamma * a + rat(5, 1) / (rat(2, 1) * a)) { return false; }
    if &(rat(2, 1) * a * eps + R::one() / a) > nu { return false; }
    if j1_slack(gamma, eps, nu, a) > zero { return false; }
    if rat(6, 1) * a / (rat(4, 1) + rat(2, 1) * gamma) > rat(1024, 1) { return false; }
    if gamma * a.clone().pow(2u32) < one { return false; }
    true
}

/// For given (A, γ, ε), find minimum ν satisfying C3 and C4_gt1, then
/// binary search for max ε satisfying j=1.
fn find_best_eps(a: &R, gamma: &R, eps_lo: &R, eps_hi: &R) -> Option<(R, R)> {
    // Binary search for the largest ε in [eps_lo, eps_hi) satisfying all constraints.
    // For each ε, ν must be at least max(C3, C4_gt1) and at most 1.
    // Check j=1 with ν = max(C3, C4_gt1) [smallest valid ν → smallest RHS γν].
    // Actually j=1 LHS increases with ε and RHS = γν also increases with ε (via C4_gt1).
    // It's complicated, so just binary search.

    let mut lo = eps_lo.clone();
    let mut hi = eps_hi.clone();

    // First check if lo is feasible
    let check_eps = |eps: &R| -> bool {
        let c3 = rat(4, 1) * gamma * a + rat(5, 1) / (rat(2, 1) * a);
        let c4 = rat(2, 1) * a * eps + R::one() / a;
        let nu = if &c3 > &c4 { c3 } else { c4 };
        if nu >= R::one() { return false; }
        check_all(gamma, eps, &nu, a)
    };

    if !check_eps(&lo) {
        // Even the lowest ε doesn't work
        return None;
    }

    // Binary search for max feasible ε
    for _ in 0..60 {
        let mid = (&lo + &hi) / rat(2, 1);
        if check_eps(&mid) {
            lo = mid;
        } else {
            hi = mid;
        }
    }

    // lo is the best feasible ε
    let eps = lo;
    let c3 = rat(4, 1) * gamma * a + rat(5, 1) / (rat(2, 1) * a);
    let c4 = rat(2, 1) * a * &eps + R::one() / a;
    let nu = if &c3 > &c4 { c3 } else { c4 };
    Some((eps, nu))
}

fn mgg_q0_with_beta(eps0: &R, beta: &R) -> u64 {
    let a = eps0.clone().pow(2u32) - beta.clone().pow(2u32) * (R::one() - eps0).pow(2u32);
    if a <= R::zero() { return u64::MAX; }
    let three_eps = rat(3, 1) * eps0;
    let ratio = &three_eps / &a;
    let q_min = ceil_nat(&ratio);
    for q in q_min..=q_min + 2 {
        if rnat(q) * &a > three_eps { return max(1, q); }
    }
    max(1, q_min + 1)
}

fn rat_to_f64(r: &R) -> f64 {
    let n = r.numer().to_string();
    let d = r.denom().to_string();
    if n.len() < 18 && d.len() < 18 {
        n.parse::<f64>().unwrap() / d.parse::<f64>().unwrap()
    } else {
        2.0f64.powi(r.numer().bits() as i32 - r.denom().bits() as i32)
    }
}

fn main() {
    // Precompute thresholds: thresholds[p] = (89/100)^(2^p)
    let mut thresholds: Vec<R> = Vec::new();
    {
        let mut cur = rat(89, 100);
        for _ in 0..=8 {
            thresholds.push(cur.clone());
            cur = &cur * &cur;
        }
    }

    println!("=== Squaring thresholds ===");
    for p in 0..=8 {
        println!("  p={}: (89/100)^{} ≈ {:.6e}", p, 1u64 << p, rat_to_f64(&thresholds[p]));
    }

    println!("\n=== Current seiferasParams ===");
    {
        let gamma = rat(1, 100); let eps = rat(1, 100);
        let nu = rat(13, 20); let a = rat(10, 1);
        let sf = stages_factor(&nu, &a);
        let stl = sep_total_layers(&gamma);
        let nsl = num_sep_levels(&gamma);
        let eps0 = &eps / rnat(stl);
        let mut p = 0u64;
        for pp in 0..thresholds.len() { if thresholds[pp] <= eps0 { p = pp as u64; break; } }
        let q0 = mgg_q0_with_beta(&eps0, &thresholds[p as usize]);
        let df = 7 * q0 + 10; let sm = 2 * (nsl + 1) + 1;
        println!("γ=1/100, ε=1/100, ν=13/20, A=10");
        println!("sf={sf} nsl={nsl} stl={stl} p={p} q0={q0} df={df} sm={sm}");
        let depth_log2 = (sf as f64).log2() + (sm as f64).log2()
            + (3 * (1u64 << p)) as f64 + (df as f64).log2();
        println!("depth ≈ 2^{depth_log2:.2}  [cofactor ≈ 2^{:.2}]",
                 depth_log2 - (3 * (1u64 << p)) as f64);
    }

    println!("\n=== Feasibility analysis ===");
    // For any (A, γ), max ε is bounded by BOTH h2εA and j=1.
    // For A in 7..30 with γ=1/A² (minimum), find the actual max ε.
    for a_int in [7, 8, 9, 10, 12, 15, 20, 30] {
        let a = rnat(a_int);
        let gamma = R::one() / a.clone().pow(2u32);
        let eps_max_h2ea = R::one() / (rat(2, 1) * &a);
        // search
        match find_best_eps(&a, &gamma, &rat(1, 10000), &eps_max_h2ea) {
            Some((eps, nu)) => {
                let stl = sep_total_layers(&gamma);
                let eps0 = &eps / rnat(stl);
                let mut p = 0u64;
                for pp in 0..thresholds.len() { if thresholds[pp] <= eps0 { p = pp as u64; break; } }
                let sf = stages_factor(&nu, &a);
                let q0 = mgg_q0_with_beta(&eps0, &thresholds[p as usize]);
                let nsl = num_sep_levels(&gamma);
                let sm = 2 * (nsl + 1) + 1;
                let df = 7 * q0 + 10;
                let depth_log2 = (sf as f64).log2() + (sm as f64).log2()
                    + (3 * (1u64 << p)) as f64 + (df as f64).log2();
                println!("A={a_int} γ=1/{}: ε≈{:.6} ν≈{:.6} sf={sf} stl={stl} p={p} q0={q0} df={df} sm={sm} depth≈2^{depth_log2:.1}",
                    a_int*a_int, rat_to_f64(&eps), rat_to_f64(&nu));
            }
            None => println!("A={a_int} γ=1/{}: no valid params", a_int*a_int),
        }
    }

    println!("\n=== Comprehensive search ===");
    let mut best_bits = f64::MAX;
    let mut best_desc = String::new();

    // A = n/d for n=65..300, d=1,2,4,10
    for d in [1i64, 2, 4, 10] {
        for n in 65..=300i64 {
            let a = rat(n, d);
            let a_f = n as f64 / d as f64;
            if a_f <= 6.5 || a_f > 30.0 { continue; }
            let a_sq = a.clone().pow(2u32);

            // γ = c/A² for c from 1 to max
            let max_gc = ceil_nat(&(&a_sq / rat(2, 1))).min(100) as i64;
            if max_gc == 0 { continue; }

            for gc in 1..=max_gc {
                let gamma = rat(gc, 1) / &a_sq;
                if gamma > rat(1, 2) || gamma <= R::zero() { continue; }

                let eps_max = R::one() / (rat(2, 1) * &a);
                let result = find_best_eps(&a, &gamma, &rat(1, 10000), &eps_max);
                let (eps, nu) = match result {
                    Some(x) => x,
                    None => continue,
                };

                let stl = sep_total_layers(&gamma);
                let nsl = num_sep_levels(&gamma);
                let sm = 2 * (nsl + 1) + 1;
                let sf = stages_factor(&nu, &a);
                let eps0 = &eps / rnat(stl);
                let mut p = 0u64;
                for pp in 0..thresholds.len() { if thresholds[pp] <= eps0 { p = pp as u64; break; } }
                if p > 6 { continue; }
                let q0 = mgg_q0_with_beta(&eps0, &thresholds[p as usize]);
                if q0 == u64::MAX { continue; }
                let df = 7 * q0 + 10;
                let depth_log2 = (sf as f64).log2() + (sm as f64).log2()
                    + (3 * (1u64 << p)) as f64 + (df as f64).log2();

                if depth_log2 < best_bits {
                    best_bits = depth_log2;
                    best_desc = format!(
                        "γ={gamma}, ε≈{:.8}, ν≈{:.8}, A={n}/{d}\n  sf={sf} nsl={nsl} stl={stl} p={p} q0={q0} df={df} sm={sm}\n  depth ≈ 2^{depth_log2:.2}  [cofactor ≈ 2^{:.2}]",
                        rat_to_f64(&eps), rat_to_f64(&nu),
                        depth_log2 - (3 * (1u64 << p)) as f64
                    );
                    println!("NEW BEST: 2^{depth_log2:.1} | A={n}/{d} γ={gamma} sf={sf} stl={stl} p={p} q0={q0}");
                }
            }
        }
    }

    // Also try non-minimum γ with specific nice fractions
    println!("\n--- Trying non-minimum γ values ---");
    for d in [1i64, 2, 4, 10] {
        for n in 65..=300i64 {
            let a = rat(n, d);
            let a_f = n as f64 / d as f64;
            if a_f <= 6.5 || a_f > 30.0 { continue; }
            let a_sq = a.clone().pow(2u32);
            let gamma_min = R::one() / &a_sq;

            // Try γ slightly above minimum (2/A², 3/A², ...)
            for gc in 2..=10i64 {
                let gamma = rat(gc, 1) / &a_sq;
                if gamma > rat(1, 2) || gamma <= R::zero() { continue; }
                if gamma <= gamma_min { continue; }

                let eps_max = R::one() / (rat(2, 1) * &a);
                let result = find_best_eps(&a, &gamma, &rat(1, 10000), &eps_max);
                let (eps, nu) = match result {
                    Some(x) => x,
                    None => continue,
                };

                let stl = sep_total_layers(&gamma);
                let nsl = num_sep_levels(&gamma);
                let sm = 2 * (nsl + 1) + 1;
                let sf = stages_factor(&nu, &a);
                let eps0 = &eps / rnat(stl);
                let mut p = 0u64;
                for pp in 0..thresholds.len() { if thresholds[pp] <= eps0 { p = pp as u64; break; } }
                if p > 6 { continue; }
                let q0 = mgg_q0_with_beta(&eps0, &thresholds[p as usize]);
                if q0 == u64::MAX { continue; }
                let df = 7 * q0 + 10;
                let depth_log2 = (sf as f64).log2() + (sm as f64).log2()
                    + (3 * (1u64 << p)) as f64 + (df as f64).log2();

                if depth_log2 < best_bits {
                    best_bits = depth_log2;
                    best_desc = format!(
                        "γ={gamma}, ε≈{:.8}, ν≈{:.8}, A={n}/{d}\n  sf={sf} nsl={nsl} stl={stl} p={p} q0={q0} df={df} sm={sm}\n  depth ≈ 2^{depth_log2:.2}  [cofactor ≈ 2^{:.2}]",
                        rat_to_f64(&eps), rat_to_f64(&nu),
                        depth_log2 - (3 * (1u64 << p)) as f64
                    );
                    println!("NEW BEST: 2^{depth_log2:.1} | A={n}/{d} γ={gamma} sf={sf} stl={stl} p={p} q0={q0}");
                }
            }
        }
    }

    println!("\n=============================");
    println!("OVERALL BEST:\n{best_desc}");
    println!("=============================");
}
