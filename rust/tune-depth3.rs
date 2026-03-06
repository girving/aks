#!/usr/bin/env -S cargo +nightly -Zscript
---
[dependencies]
num = "0.4"
---

//! Feasibility analysis for reducing graph squarings from p=6 to p=5.
//!
//! Saving one squaring would halve the degree exponent (8^64 → 8^32), cutting
//! ~96 bits from the depth. But this requires ε₀ ≥ β^(2^p) = β^32, and the
//! Seiferas constraints make ε₀ too small.
//!
//! # Two levers analyzed
//!
//! 1. **Maximize ε₀** by optimizing (A, γ, ε) within `Params` constraints.
//!    Best achievable: ε₀ ≈ 0.002 (at A=8, γ=1/64 with stl=7).
//!
//! 2. **Tighter β** (proved bound is 5√2/8 ≈ 0.8839, currently rounded to 89/100).
//!    Even the tightest valid rational β gives β^32 ≈ 0.016, which is 8× above
//!    the max ε₀ of 0.002.
//!
//! # Conclusion
//!
//! p=5 is infeasible with the MGG expander and current Seiferas constraints.
//! The bottleneck is C3 (ν ≥ 4γA + 5/(2A)) forcing ν close to 1, which forces
//! small γ (~1/A²), which forces large stl (≥7), which crushes ε₀ = ε/stl.
//! Saving a squaring would require either:
//!   - A Ramanujan expander (ratio log(d)/log(1/β) ≈ 5 vs MGG's ~17)
//!   - A different separator construction with fewer layers
//!   - A zig-zag family approach (avoids the d^(2^p) degree blowup)
//!
//! Run: CARGO_HOME=/tmp/cargo CARGO_TARGET_DIR=/tmp/cargo-target cargo +nightly -Zscript rust/tune-depth3.rs

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
fn clog2(n: u64) -> u64 { if n <= 1 { 0 } else { 64 - (n - 1).leading_zeros() as u64 } }
fn num_sep_levels(gamma: &R) -> u64 {
    if gamma <= &R::zero() { return 0; }
    clog2(ceil_nat(&(R::one() / (rat(2, 1) * gamma))))
}
fn sep_total_layers(gamma: &R) -> u64 { num_sep_levels(gamma) + 2 }
fn stages_factor(nu: &R, a: &R) -> u64 {
    let two_a = rat(2, 1) * a;
    let mut power = R::one();
    for c in 0..10000 { if &power * &two_a < R::one() { return c; } power = power * nu; }
    10000
}

fn check_all(gamma: &R, eps: &R, nu: &R, a: &R) -> bool {
    let one = R::one(); let zero = R::zero();
    if gamma <= &zero || gamma > &rat(1, 2) { return false; }
    if eps <= &zero || eps >= &one { return false; }
    if a <= &one { return false; }
    if nu <= &zero || nu >= &one { return false; }
    let two_eps_a = rat(2, 1) * eps * a;
    if two_eps_a.clone().pow(2u32) >= one { return false; }
    if nu < &(rat(4, 1) * gamma * a + rat(5, 1) / (rat(2, 1) * a)) { return false; }
    if &(rat(2, 1) * a * eps + R::one() / a) > nu { return false; }
    let denom = &one - two_eps_a.clone().pow(2u32);
    let eight_a3 = rat(8, 1) * a.clone().pow(3u32) - rat(2, 1) * a;
    if eight_a3 <= zero { return false; }
    let lhs = rat(2, 1) * gamma * eps * a
        + eps * gamma / a + eps / (rat(2, 1) * a)
        + rat(2, 1) * gamma * eps * a / &denom
        + R::one() / &eight_a3 + gamma / a + R::one() / &eight_a3;
    if lhs > gamma * nu { return false; }
    if rat(6, 1) * a / (rat(4, 1) + rat(2, 1) * gamma) > rat(1024, 1) { return false; }
    if gamma * a.clone().pow(2u32) < one { return false; }
    true
}

/// Binary search for max ε satisfying all constraints at minimum ν.
fn max_eps(a: &R, gamma: &R) -> Option<(R, R)> {
    let check = |eps: &R| -> bool {
        let c3 = rat(4, 1) * gamma * a + rat(5, 1) / (rat(2, 1) * a);
        let c4 = rat(2, 1) * a * eps + R::one() / a;
        let nu = if &c3 > &c4 { c3 } else { c4 };
        if nu >= R::one() { return false; }
        check_all(gamma, eps, &nu, a)
    };
    let lo_init = rat(1, 100000);
    if !check(&lo_init) { return None; }
    let hi_init = R::one() / (rat(2, 1) * a);
    let mut lo = lo_init; let mut hi = hi_init;
    for _ in 0..80 { let mid = (&lo + &hi) / rat(2, 1); if check(&mid) { lo = mid; } else { hi = mid; } }
    let eps = lo;
    let c3 = rat(4, 1) * gamma * a + rat(5, 1) / (rat(2, 1) * a);
    let c4 = rat(2, 1) * a * &eps + R::one() / a;
    let nu = if &c3 > &c4 { c3 } else { c4 };
    Some((eps, nu))
}

fn iter_sq(c: &R, p: u64) -> R {
    if p == 0 { c.clone() } else { let h = iter_sq(c, p - 1); &h * &h }
}

fn mgg_q0_with_beta(eps0: &R, beta: &R) -> u64 {
    let a = eps0.clone().pow(2u32) - beta.clone().pow(2u32) * (R::one() - eps0).pow(2u32);
    if a <= R::zero() { return u64::MAX; }
    let q_min = ceil_nat(&(rat(3, 1) * eps0 / &a));
    for q in q_min..=q_min + 2 { if rnat(q) * &a > rat(3, 1) * eps0 { return max(1, q); } }
    max(1, q_min + 1)
}

fn rat_to_f64(r: &R) -> f64 {
    let n = r.numer().to_string(); let d = r.denom().to_string();
    if n.len() < 18 && d.len() < 18 { n.parse::<f64>().unwrap() / d.parse::<f64>().unwrap() }
    else { 2.0f64.powi(r.numer().bits() as i32 - r.denom().bits() as i32) }
}

fn main() {
    println!("=== Lever 1: What's the max ε₀ achievable? ===\n");

    // For each A (integer, from 7 to 15), γ = c/A² for c=1..max,
    // find max ε, compute ε₀ = ε/stl.
    let mut global_max_eps0 = R::zero();
    let mut global_max_desc = String::new();

    for a_int in 7..=15i64 {
        let a = rnat(a_int as u64);
        let a_sq = a.clone().pow(2u32);
        let max_gc = ceil_nat(&(&a_sq / rat(2, 1))).min(20) as i64;

        let mut best_eps0_for_a = R::zero();
        let mut best_for_a = String::new();

        for gc in 1..=max_gc {
            let gamma = rat(gc, 1) / &a_sq;
            if gamma > rat(1, 2) { continue; }

            let (eps, nu) = match max_eps(&a, &gamma) { Some(x) => x, None => continue };
            let stl = sep_total_layers(&gamma);
            let eps0 = &eps / rnat(stl);
            let sf = stages_factor(&nu, &a);

            if eps0 > best_eps0_for_a {
                best_eps0_for_a = eps0.clone();
                best_for_a = format!(
                    "A={a_int} γ={gc}/{}={:.5} stl={stl} sf={sf} ε≈{:.8} ν≈{:.6} → ε₀≈{:.8}",
                    a_int*a_int, rat_to_f64(&gamma), rat_to_f64(&eps), rat_to_f64(&nu),
                    rat_to_f64(&eps0)
                );
            }
            if eps0 > global_max_eps0 {
                global_max_eps0 = eps0.clone();
                global_max_desc = best_for_a.clone();
            }
        }
        if !best_for_a.is_empty() {
            println!("  {best_for_a}");
        }
    }

    println!("\n  GLOBAL MAX ε₀: {}", global_max_desc);
    println!("  ε₀ ≈ {:.10}", rat_to_f64(&global_max_eps0));

    println!("\n=== Lever 2: How tight can we make β? ===\n");

    // The proved bound is spectralGap(mgg n) ≤ 5√2/8.
    // 5√2/8 ≈ 0.883883...
    // We need a rational β with (5√2/8)² ≤ β² (so β ≥ 5√2/8).
    // (5√2/8)² = 50/64 = 25/32 = 0.78125
    // Current: (89/100)² = 7921/10000 = 0.7921
    //
    // Best rational β: smallest β with β² ≥ 25/32.
    // β = ⌈√(25/32) * D⌉ / D for denominator D.

    println!("  (5√2/8)² = 25/32 = 0.78125");
    println!("  Current β = 89/100, β² = 7921/10000 = 0.7921");
    println!();

    // Try various denominators
    println!("  Candidate β values (β² ≥ 25/32):");
    let target_sq = rat(25, 32);  // (5√2/8)²
    let mut best_betas: Vec<(R, f64)> = Vec::new();
    for d in 1..=10000i64 {
        // Find smallest n with (n/d)² ≥ 25/32
        // n² ≥ 25d²/32, n ≥ ceil(d√(25/32)) = ceil(5d√2/8)
        // Approximate: 5*d*1.41422/8
        let approx = 5.0 * d as f64 * std::f64::consts::SQRT_2 / 8.0;
        let n = approx.ceil() as i64;
        let beta = rat(n, d);
        if beta.clone().pow(2u32) >= target_sq && beta < rat(89, 100) {
            best_betas.push((beta.clone(), n as f64 / d as f64));
        }
    }
    best_betas.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
    best_betas.dedup_by(|a, b| a.0 == b.0);

    // Show top 10 tightest
    println!("  {:>10} {:>12} {:>12}", "β", "β²", "β^32");
    for (beta, _) in best_betas.iter().take(15) {
        let beta_sq = beta.clone().pow(2u32);
        let beta_32 = iter_sq(beta, 5);  // β^(2^5) = β^32
        println!("  {:>10} {:>12.8} {:>12.8}", beta, rat_to_f64(&beta_sq), rat_to_f64(&beta_32));
    }

    println!("\n=== Can we achieve p=5? ===\n");

    // For p=5: need ε₀ ≥ β^32.
    // Best ε₀ ≈ {}, need β^32 ≤ this.
    let max_eps0_f = rat_to_f64(&global_max_eps0);
    println!("  Max achievable ε₀ ≈ {:.10}", max_eps0_f);
    println!();

    // Check each β candidate
    println!("  {:>10} {:>12} {:>10}", "β", "β^32", "feasible?");
    for (beta, _) in best_betas.iter().take(15) {
        let beta_32 = iter_sq(beta, 5);
        let beta_32_f = rat_to_f64(&beta_32);
        let feasible = beta_32 <= global_max_eps0;
        println!("  {:>10} {:>12.8} {:>10}",
                 beta, beta_32_f, if feasible { "YES ✓" } else { "no" });
    }

    // Find the threshold β where β^32 = max_eps0
    // β = max_eps0^(1/32)
    let beta_threshold = max_eps0_f.powf(1.0/32.0);
    println!("\n  Need β ≤ {:.6} for p=5", beta_threshold);
    println!("  But proved bound gives β ≥ 5√2/8 ≈ {:.6}", 5.0 * std::f64::consts::SQRT_2 / 8.0);
    println!("  Gap: {:.6} vs {:.6}", beta_threshold, 5.0 * std::f64::consts::SQRT_2 / 8.0);

    println!("\n=== What if we used a higher-degree MGG? ===\n");
    // MGG with more generators would have higher degree but potentially better gap.
    // But the gap/degree tradeoff matters: depth ∝ degree after squaring.
    //
    // Key metric: log(degree) / log(1/β) — this is invariant under squaring.
    // For MGG-8: log(8)/log(1/0.884) = 2.079/0.1233 = 16.86
    // For Ramanujan-8: log(8)/log(8/(2√7)) = 2.079/0.4144 = 5.02
    //
    // The depth is proportional to degree^(log(1/ε₀)/log(1/β)) which equals
    // ε₀^(-log(d)/log(1/β)).
    // So better ratio = less depth. Ramanujan would give 3.4× less in the exponent!

    let mgg_beta = 5.0 * std::f64::consts::SQRT_2 / 8.0;
    let mgg_ratio = 8.0f64.ln() / (1.0/mgg_beta).ln();
    println!("  MGG-8: β = 5√2/8 ≈ {:.4}, ratio = log(8)/log(1/β) = {:.2}", mgg_beta, mgg_ratio);

    let ram_beta = 2.0 * 7.0f64.sqrt() / 8.0;
    let ram_ratio = 8.0f64.ln() / (1.0/ram_beta).ln();
    println!("  Ramanujan-8: β = 2√7/8 ≈ {:.4}, ratio = {:.2}", ram_beta, ram_ratio);

    println!("\n  With ε₀ = 0.01:");
    let log_inv_eps0 = (1.0/0.01f64).ln();
    let mgg_log_depth = log_inv_eps0 * mgg_ratio;
    let ram_log_depth = log_inv_eps0 * ram_ratio;
    println!("  MGG depth ∝ 8^({:.1}) ≈ 2^{:.0}", log_inv_eps0/mgg_beta.recip().ln(), mgg_log_depth);
    println!("  Ramanujan depth ∝ 8^({:.1}) ≈ 2^{:.0}", log_inv_eps0/ram_beta.recip().ln(), ram_log_depth);

    // Now: what about the p=6 optimization from the first search?
    println!("\n=== Best p=6 improvement (cofactor optimization) ===\n");
    // A=8, γ=1/64 gave cofactor 1,615,978 vs current 2,240,595 (1.39× better).
    // Let's compute exact Params.depth for both.

    let eight_64: BigInt = BigInt::from(8u64).pow(64u32);
    let current_depth: BigInt = BigInt::from(7u64) * BigInt::from(15u64)
        * &eight_64 * BigInt::from(21339u64) + BigInt::from(9u64);
    println!("  Current (A=10): sf=7 × sm=15 × 8^64 × df=21339 + 9");
    println!("    cofactor = {}", 7u64 * 15 * 21339);
    println!("    depth bits = {}", current_depth.bits());

    // For best candidate, we need to compute Q₀ with β = (89/100)^64
    let beta6_89 = iter_sq(&rat(89, 100), 6);
    println!("\n  For A=8, γ=1/64:");
    {
        let a = rnat(8);
        let gamma = rat(1, 64);
        let (eps, nu) = max_eps(&a, &gamma).unwrap();
        let stl = sep_total_layers(&gamma);
        let nsl = num_sep_levels(&gamma);
        let sf = stages_factor(&nu, &a);
        let sm = 2 * (nsl + 1) + 1;
        let eps0 = &eps / rnat(stl);
        let q0 = mgg_q0_with_beta(&eps0, &beta6_89);
        let df = 7 * q0 + 10;
        let cofactor = sf * sm * df;
        let depth: BigInt = BigInt::from(sf) * BigInt::from(sm)
            * &eight_64 * BigInt::from(df) + BigInt::from(9u64);
        println!("    sf={sf} sm={sm} q0={q0} df={df}");
        println!("    ε≈{:.10} ν≈{:.10} stl={stl}", rat_to_f64(&eps), rat_to_f64(&nu));
        println!("    cofactor = {cofactor}");
        println!("    depth bits = {}", depth.bits());
        println!("    improvement: {:.2}×", (7 * 15 * 21339) as f64 / cofactor as f64);
    }

    // Also try with tighter β for the Q₀ computation (doesn't change p, but changes Q₀)
    println!("\n  With tighter β = 884/1000:");
    let beta6_884 = iter_sq(&rat(884, 1000), 6);
    {
        let a = rnat(8);
        let gamma = rat(1, 64);
        let (eps, nu) = max_eps(&a, &gamma).unwrap();
        let stl = sep_total_layers(&gamma);
        let nsl = num_sep_levels(&gamma);
        let sf = stages_factor(&nu, &a);
        let sm = 2 * (nsl + 1) + 1;
        let eps0 = &eps / rnat(stl);
        let q0 = mgg_q0_with_beta(&eps0, &beta6_884);
        let df = 7 * q0 + 10;
        let cofactor = sf * sm * df;
        println!("    sf={sf} sm={sm} q0={q0} df={df}");
        println!("    cofactor = {cofactor}");
        println!("    improvement over current: {:.2}×", (7 * 15 * 21339) as f64 / cofactor as f64);
    }
}
