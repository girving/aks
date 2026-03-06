#!/usr/bin/env -S cargo +nightly -Zscript
//! Check: is cap/(4A³-A) ≥ 1 whenever parent is odd and deficit > half_D?

const GAMMA: f64 = 1.0 / 100.0;
const NU: f64 = 13.0 / 20.0;
const A: f64 = 10.0;

fn capacity(k: usize, t: usize, l: usize) -> f64 {
    (1u64 << k) as f64 * NU.powi(t as i32) * A.powi(l as i32)
}
fn fringe(k: usize, t: usize, level: usize, s: usize) -> usize {
    if level == 0 { 0 }
    else if k <= level + 1 { s / 2 }
    else { (GAMMA * capacity(k, t, level)).floor() as usize }
}
fn split_parent_card(s: usize, f: usize) -> usize {
    let half = s / 2;
    if f >= half { s } else { s - 2 * (half - f) }
}
fn split_child_card(s: usize, f: usize) -> usize {
    let half = s / 2;
    if f >= half { 0 } else { half - f }
}
fn bag_card(k: usize, t: usize) -> Vec<usize> {
    let mut bc = vec![0usize; k + 1];
    if t == 0 { bc[0] = 1 << k; return bc; }
    let prev = bag_card(k, t - 1);
    for l in 0..=k {
        let f_fn = |lp: usize| fringe(k, t - 1, lp, prev[lp]);
        let fc = if l + 1 <= k { 2 * split_parent_card(prev[l+1], f_fn(l+1)) } else { 0 };
        let fp = if l == 0 { split_parent_card(prev[0], f_fn(0)) }
                 else { split_child_card(prev[l-1], f_fn(l-1)) };
        bc[l] = fc + fp;
    }
    bc
}
fn num_stages(k: usize) -> usize {
    for t in 0..1000 { if capacity(k, t, k-2) < A { return t.saturating_sub(1); } }
    999
}

fn main() {
    let denom_new = 4.0 * A * A * A - A; // 3990
    let mut violations = 0u64;
    let mut checks = 0u64;

    for k in 10..=18 {
        let ns = num_stages(k);
        for t in 0..=ns {
            let bc = bag_card(k, t);
            for l in 1..=k {
                if (t + l - 1) % 2 != 0 { continue; }
                let parent_card = bc[l - 1];
                let half_d = parent_card / 2;

                let subregs_card: usize = (0..=(k - l)).map(|d| (1 << d) * bc[l + d]).sum();
                let bag_size = (1usize << k) / (1usize << l);
                if subregs_card > bag_size { continue; }
                let deficit = bag_size - subregs_card;

                let cap = capacity(k, t, l);
                let rhs = half_d as f64 + cap / denom_new;

                checks += 1;
                if deficit as f64 > rhs + 1e-9 {
                    violations += 1;
                    if violations <= 20 {
                        println!(
                            "VIOLATION: k={k} t={t} l={l} deficit={deficit} half_D={half_d} \
                             cap/(4A³-A)={:.6} pc={parent_card} pc_odd={}",
                            cap / denom_new, parent_card % 2 == 1
                        );
                    }
                }
            }
        }
    }
    println!("\nChecks: {checks}, Violations: {violations}");

    // Also check: what's the min cap when parent is odd and deficit > half_D?
    let mut min_cap = f64::MAX;
    for k in 10..=18 {
        let ns = num_stages(k);
        for t in 0..=ns {
            let bc = bag_card(k, t);
            for l in 1..=k {
                if (t + l - 1) % 2 != 0 { continue; }
                let parent_card = bc[l - 1];
                if parent_card % 2 == 0 { continue; }
                let half_d = parent_card / 2;
                let subregs_card: usize = (0..=(k - l)).map(|d| (1 << d) * bc[l + d]).sum();
                let bag_size = (1usize << k) / (1usize << l);
                if subregs_card > bag_size { continue; }
                let deficit = bag_size - subregs_card;
                if deficit > half_d {
                    let cap = capacity(k, t, l);
                    if cap < min_cap {
                        min_cap = cap;
                        println!("New min cap: k={k} t={t} l={l} cap={cap:.1} cap/(4A³-A)={:.6}", cap/denom_new);
                    }
                }
            }
        }
    }
    println!("Min cap when parent odd & deficit > half_D: {min_cap:.1}");
}
