#!/usr/bin/env -S cargo +nightly -Zscript
//! Test spillover_bound with CORRECT definitions matching Lean.

const GAMMA: f64 = 1.0 / 100.0;
const NU: f64 = 13.0 / 20.0;
const A: f64 = 10.0;

fn capacity(k: usize, t: usize, l: usize) -> f64 {
    (1u64 << k) as f64 * NU.powi(t as i32) * A.powi(l as i32)
}

fn fringe(p_gamma: f64, k: usize, t: usize, level: usize, s: usize) -> usize {
    if level == 0 { 0 }
    else if k <= level + 1 { s / 2 }
    else { (p_gamma * capacity(k, t, level)).floor() as usize }
}

fn split_parent_card(s: usize, f: usize) -> usize {
    // s - 2 * (s/2 - f), but careful with underflow
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
        let f_fn = |lp: usize| fringe(GAMMA, k, t - 1, lp, prev[lp]);
        let fc = if l + 1 <= k {
            2 * split_parent_card(prev[l+1], f_fn(l+1))
        } else { 0 };
        let fp = if l == 0 {
            split_parent_card(prev[0], f_fn(0))
        } else {
            split_child_card(prev[l-1], f_fn(l-1))
        };
        bc[l] = fc + fp;
    }
    bc
}

fn num_stages(k: usize) -> usize {
    for t in 0..1000 { if capacity(k, t, k - 2) < A { return t.saturating_sub(1); } }
    999
}

fn main() {
    // First check conservation
    let mut conservation_ok = true;
    for k in 10..=14 {
        for t in 0..=80 {
            let bc = bag_card(k, t);
            let sum: usize = (0..=k).map(|l| (1 << l) * bc[l]).sum();
            if sum != 1 << k {
                println!("CONSERVATION FAIL: k={k} t={t} sum={sum} target={}", 1usize << k);
                conservation_ok = false;
                break;
            }
        }
    }
    if conservation_ok {
        println!("Conservation OK for all tested (k, t).");
    }

    // Now test spillover_bound
    let denom_val = 8.0 * A * A * A - 2.0 * A;
    let mut violations = 0u64;
    let mut checks = 0u64;
    let mut max_ratio = 0.0f64;

    for k in 10..=16 {
        let ns = num_stages(k);
        for t in 0..=ns {
            let bc = bag_card(k, t);
            for l in 1..=k {
                if (t + l - 1) % 2 != 0 { continue; }

                let parent_card = bc[l - 1];
                let half_d = parent_card / 2;

                // subregs_card = Σ_{d=0}^{k-l} 2^d * bc[l+d]
                let subregs_card: usize = (0..=(k - l)).map(|d| (1 << d) * bc[l + d]).sum();
                let bag_size = (1usize << k) / (1usize << l);

                // deficit = bag_size - subregs_card (should be ≥ 0 by conservation)
                if subregs_card > bag_size {
                    println!("SUBREGS > BAGSIZE: k={k} t={t} l={l} sub={subregs_card} size={bag_size}");
                    continue;
                }
                let deficit = bag_size - subregs_card;

                let cap = capacity(k, t, l);
                let rhs = half_d as f64 + cap / denom_val;

                checks += 1;
                if deficit as f64 > rhs + 1e-9 {
                    violations += 1;
                    println!(
                        "VIOLATION: k={k} t={t} l={l} deficit={deficit} half_D={half_d} \
                         parent_card={parent_card} cap/(8A³-2A)={:.6} rhs={rhs:.6} \
                         parent_odd={}",
                        cap / denom_val, parent_card % 2 == 1
                    );
                }

                if rhs > 0.0 {
                    let ratio = deficit as f64 / rhs;
                    if ratio > max_ratio { max_ratio = ratio; }
                }
            }
        }
    }
    println!("\nChecks: {checks}, Violations: {violations}, Max ratio: {max_ratio:.6}");

    // Odd parent analysis
    let mut odd_count = 0u64;
    let mut odd_violations = 0u64;
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
                let subregs_card: usize = (0..=(k - l)).map(|d| (1 << d) * bc[l + d]).sum();
                let bag_size = (1usize << k) / (1usize << l);
                if subregs_card > bag_size { continue; }
                let deficit = bag_size - subregs_card;
                let diff = if deficit >= half_d { deficit - half_d } else { 0 };
                let cap = capacity(k, t, l);
                let bound = cap / denom_val;
                if diff as f64 > bound + 1e-9 {
                    odd_violations += 1;
                    println!(
                        "ODD VIOLATION: k={k} t={t} l={l} diff={diff} bound={bound:.6} pc={parent_card}"
                    );
                }
            }
        }
    }
    println!("Odd parent count: {odd_count}, Odd violations: {odd_violations}");
}
