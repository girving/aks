#!/usr/bin/env -S cargo +nightly -Zscript
---
[dependencies]
num = "0.4"
---

//! Focused evaluation of specific promising (A, γ) candidates at p=6.
//!
//! The comprehensive search (tune-depth.rs) showed all feasible parameters give p=6
//! (i.e., 6 graph squarings, degree 8^64). This script minimizes the cofactor
//!   cofactor = sf × sm × df
//! where sf = stagesFactor, sm = 2·(numSepLevels+1)+1, df = 7·Q₀+10.
//!
//! Best found: A=8, γ=1/64 gives cofactor ~1.6M vs current A=10, γ=1/100 at ~2.2M
//! (improvement ~1.39×). This saves ~0.5 bits in the overall depth exponent.
//!
//! Run: CARGO_HOME=/tmp/cargo CARGO_TARGET_DIR=/tmp/cargo-target cargo +nightly -Zscript rust/tune-depth2.rs

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

fn find_best_eps(a: &R, gamma: &R, eps_hi: &R) -> Option<(R, R)> {
    let check = |eps: &R| -> bool {
        let c3 = rat(4, 1) * gamma * a + rat(5, 1) / (rat(2, 1) * a);
        let c4 = rat(2, 1) * a * eps + R::one() / a;
        let nu = if &c3 > &c4 { c3 } else { c4 };
        if nu >= R::one() { return false; }
        check_all(gamma, eps, &nu, a)
    };
    let eps_lo = rat(1, 10000);
    if !check(&eps_lo) { return None; }
    let mut lo = eps_lo; let mut hi = eps_hi.clone();
    for _ in 0..80 { let mid = (&lo + &hi) / rat(2, 1); if check(&mid) { lo = mid; } else { hi = mid; } }
    let eps = lo;
    let c3 = rat(4, 1) * gamma * a + rat(5, 1) / (rat(2, 1) * a);
    let c4 = rat(2, 1) * a * &eps + R::one() / a;
    let nu = if &c3 > &c4 { c3 } else { c4 };
    Some((eps, nu))
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
    let beta6 = { let mut c = rat(89, 100); for _ in 0..6 { c = &c * &c; } c }; // (89/100)^64

    println!("{:<8} {:<12} {:<5} {:<5} {:<5} {:<8} {:<8} {:<8} {:<10} {:<10}",
             "A", "γ", "sf", "nsl", "stl", "ε_max", "q0", "df", "cofactor", "depth_bits");
    println!("{}", "-".repeat(90));

    let mut best_cofactor = u64::MAX;
    let mut best_desc = String::new();

    // Candidates from initial search: A from 7 to 11 were best
    // γ = c/A² for c = 1, 2, 3, ...
    for a_num in [70, 75, 80, 85, 90, 95, 100, 105, 110, 120, 130, 140, 150] {
        let a = rat(a_num, 10);
        let a_sq = a.clone().pow(2u32);
        let eps_max = R::one() / (rat(2, 1) * &a);

        let max_gc = ceil_nat(&(&a_sq / rat(2, 1))).min(30) as i64;
        for gc in 1..=max_gc {
            let gamma = rat(gc, 1) / &a_sq;
            if gamma > rat(1, 2) { continue; }

            let (eps, nu) = match find_best_eps(&a, &gamma, &eps_max) {
                Some(x) => x, None => continue
            };

            let stl = sep_total_layers(&gamma);
            let nsl = num_sep_levels(&gamma);
            let sm = 2 * (nsl + 1) + 1;
            let sf = stages_factor(&nu, &a);

            let eps0 = &eps / rnat(stl);
            // Verify p=6
            if !(beta6 <= eps0) { continue; }
            let q0 = mgg_q0_with_beta(&eps0, &beta6);
            if q0 == u64::MAX { continue; }
            let df = 7 * q0 + 10;
            let cofactor = sf * sm * (df as u64);

            println!("{:<8} {:<12} {:<5} {:<5} {:<5} {:<8.6} {:<8} {:<8} {:<10} {:<10.2}",
                     format!("{a_num}/10"), format!("{gc}/{}", a_num*a_num/100),
                     sf, nsl, stl, rat_to_f64(&eps), q0, df, cofactor,
                     192.0 + (cofactor as f64).log2());

            if cofactor < best_cofactor {
                best_cofactor = cofactor;
                best_desc = format!(
                    "γ={}, ε≈{:.10}, ν≈{:.10}, A={}/10\n  sf={} nsl={} stl={} p=6 q0={} df={} sm={}\n  cofactor = {} ≈ 2^{:.2}\n  depth ≈ 2^{:.2}",
                    gamma, rat_to_f64(&eps), rat_to_f64(&nu), a_num,
                    sf, nsl, stl, q0, df, sm,
                    cofactor, (cofactor as f64).log2(),
                    192.0 + (cofactor as f64).log2()
                );
            }
        }
    }

    println!("\n=============================");
    println!("BEST:\n{best_desc}");
    println!("\nFor comparison, current seiferasParams:");
    println!("  cofactor = 7 * 15 * 21339 = {}", 7u64 * 15 * 21339);
    println!("  depth ≈ 2^{:.2}", 192.0 + (7.0 * 15.0 * 21339.0f64).log2());
    println!("=============================");

    // Compute actual Params.depth for the current and best
    let current_depth: BigInt = BigInt::from(7u64) * BigInt::from(15u64)
        * BigInt::from(8u64).pow(64u32) * BigInt::from(21339u64) + BigInt::from(9u64);
    println!("\nCurrent Params.depth has {} bits", current_depth.bits());

    if best_cofactor < u64::MAX {
        // Parse best: sf * sm * 8^64 * df + 9
        // We already have sf, sm, df from the loop... let's just show ratio
        println!("Best cofactor = {}, current = {}", best_cofactor, 7u64 * 15 * 21339);
        println!("Improvement ratio: {:.2}x", (7.0 * 15.0 * 21339.0) / best_cofactor as f64);
    }
}
