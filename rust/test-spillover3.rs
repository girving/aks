#!/usr/bin/env -S cargo +nightly -Zscript
//! Check: when parent_card is odd, is (deficit - half_D) ≤ cap/(8A³-2A)?

const GAMMA: f64 = 1.0 / 100.0;
const NU: f64 = 13.0 / 20.0;
const A: f64 = 10.0;

fn capacity(k: usize, t: usize, l: usize) -> f64 {
    (1u64 << k) as f64 * NU.powi(t as i32) * A.powi(l as i32)
}
fn fringe(k: usize, t: usize, l: usize, sz: usize) -> usize {
    if l == 0 { 0 } else { ((GAMMA * capacity(k, t, l)).floor() as usize).min(sz / 2) }
}
fn bag_card(k: usize, t: usize) -> Vec<usize> {
    let mut bc = vec![0usize; k + 1];
    if t == 0 { bc[0] = 1 << k; return bc; }
    let prev = bag_card(k, t - 1);
    for l in 0..=k {
        let fc = if l + 1 <= k { 2 * ((prev[l+1] - fringe(k,t-1,l+1,prev[l+1])) / 2) } else { 0 };
        let fp = if l == 0 { (prev[0] - fringe(k,t-1,0,prev[0])) / 2 }
                 else { (prev[l-1] + fringe(k,t-1,l-1,prev[l-1])) / 2 };
        bc[l] = fc + fp;
    }
    bc
}
fn num_stages(k: usize) -> usize {
    for t in 0..1000 { if capacity(k, t, k-2) < A { return t.saturating_sub(1); } }
    999
}

fn main() {
    let denom = 8.0 * A.powi(3) - 2.0 * A;
    let mut violations = 0u64;
    let mut odd_count = 0u64;

    for k in 10..=16 {
        let ns = num_stages(k);
        for t in 0..=ns {
            let bc = bag_card(k, t);
            for l in 1..=k {
                if (t + l - 1) % 2 != 0 { continue; }
                let parent_card = bc[l - 1];
                if parent_card % 2 != 1 { continue; }
                odd_count += 1;

                let half_d = parent_card / 2;
                let mut subregs_card: usize = 0;
                for d in 0..=(k - l) {
                    subregs_card += (1usize << d) * bc[l + d];
                }
                let bag_size = (1usize << k) / (1usize << l);
                if subregs_card > bag_size {
                    println!("k={k} t={t} l={l}: subregs > bag_size!");
                    continue;
                }
                let deficit = bag_size - subregs_card;
                let cap = capacity(k, t, l);
                let bound = cap / denom;

                // deficit and half_d are natural numbers
                // deficit >= half_d should hold since deficit = parent_card/2 (ℚ) + rest (nonneg)
                // = half_d + 1/2 + rest, so deficit (integer) >= half_d + 1
                if deficit < half_d {
                    println!("UNEXPECTED: deficit < half_d: k={k} t={t} l={l} def={deficit} hd={half_d} pc={parent_card}");
                    continue;
                }
                let diff = deficit - half_d;
                if diff as f64 > bound + 1e-9 {
                    violations += 1;
                    println!("VIOLATION: k={k} t={t} l={l} diff={diff} bound={bound:.6} pc={parent_card}");
                }
            }
        }
    }
    println!("\nOdd parent count: {odd_count}, Violations: {violations}");
}
