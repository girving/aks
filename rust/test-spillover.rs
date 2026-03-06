#!/usr/bin/env -S cargo +nightly -Zscript
//! Test whether spillover_bound holds:
//! deficit ≤ ↑(parent_card / 2) + cap/(8A³-2A)
//! where deficit = b.size - subregs(b).card
//!
//! We simulate the Seiferas bag construction with concrete parameters
//! and check the bound at every stage, bag, and level.

use std::collections::HashMap;

// Seiferas parameters
const GAMMA: f64 = 1.0 / 100.0;
const EPS: f64 = 1.0 / 100.0;
const NU: f64 = 13.0 / 20.0;
const A: f64 = 10.0;

fn capacity(k: usize, t: usize, l: usize) -> f64 {
    (1u64 << k) as f64 * NU.powi(t as i32) * A.powi(l as i32)
}

fn fringe(k: usize, t: usize, l: usize, sz: usize) -> usize {
    if l == 0 {
        0
    } else {
        let cap = capacity(k, t, l);
        let f = (GAMMA * cap).floor() as usize;
        f.min(sz / 2)
    }
}

fn bag_card(k: usize, t: usize) -> Vec<usize> {
    // bagCard for each level 0..=k
    let mut bc = vec![0usize; k + 1];
    if t == 0 {
        bc[0] = 1 << k;
        return bc;
    }
    let prev = bag_card(k, t - 1);
    // rebag
    for l in 0..=k {
        let from_children = if l + 1 <= k {
            let parent_sz = prev[l + 1];
            let f = fringe(k, t - 1, l + 1, parent_sz);
            2 * split_parent_card(parent_sz, f)
        } else {
            0
        };
        let from_parent = if l == 0 {
            let root_sz = prev[0];
            let f = fringe(k, t - 1, 0, root_sz);
            split_parent_card(root_sz, f)
        } else {
            let par_sz = prev[l - 1];
            let f = fringe(k, t - 1, l - 1, par_sz);
            split_child_card(par_sz, f)
        };
        bc[l] = from_children + from_parent;
    }
    bc
}

fn split_parent_card(sz: usize, f: usize) -> usize {
    (sz - f) / 2
}

fn split_child_card(sz: usize, f: usize) -> usize {
    (sz + f) / 2
}

fn num_stages(k: usize) -> usize {
    // Smallest t such that capacity(k, t, k-2) < A
    for t in 0..1000 {
        if capacity(k, t, k - 2) < A {
            return t.saturating_sub(1);
        }
    }
    999
}

fn main() {
    let mut violations = 0u64;
    let mut checks = 0u64;
    let mut max_ratio = 0.0f64;

    for k in 10..=16 {
        let ns = num_stages(k);
        for t in 0..=ns {
            let bc = bag_card(k, t);

            // For each bag level l with l >= 1
            for l in 1..=k {
                // Check parity: (t + (l-1)) % 2 == 0
                if (t + l - 1) % 2 != 0 {
                    continue;
                }

                // parent_card = bc[l-1]
                let parent_card = bc[l - 1];
                let half_d = parent_card / 2; // integer division

                // Compute subregs card = sum_{d=0}^{k-l} 2^d * bc[l+d]
                let mut subregs_card: usize = 0;
                for d in 0..=(k - l) {
                    subregs_card += (1usize << d) * bc[l + d];
                }

                let bag_size = (1usize << k) / (1usize << l);

                // deficit
                let deficit = bag_size.saturating_sub(subregs_card);

                let cap = capacity(k, t, l);
                let denom = 8.0 * A.powi(3) - 2.0 * A;
                let rhs = half_d as f64 + cap / denom;

                checks += 1;

                if deficit as f64 > rhs + 1e-9 {
                    violations += 1;
                    println!(
                        "VIOLATION: k={k} t={t} l={l} deficit={deficit} half_D={half_d} \
                         parent_card={parent_card} cap/(8A³-2A)={:.6} rhs={rhs:.6} \
                         parent_odd={}",
                        cap / denom,
                        parent_card % 2 == 1
                    );
                }

                if rhs > 0.0 {
                    let ratio = deficit as f64 / rhs;
                    if ratio > max_ratio {
                        max_ratio = ratio;
                    }
                }
            }
        }
    }

    println!("\nChecks: {checks}, Violations: {violations}, Max ratio: {max_ratio:.6}");

    // Also check: when parent_card is odd, what's the situation?
    let mut odd_parent_count = 0u64;
    let mut odd_tight_count = 0u64;
    for k in 10..=16 {
        let ns = num_stages(k);
        for t in 0..=ns {
            let bc = bag_card(k, t);
            for l in 1..=k {
                if (t + l - 1) % 2 != 0 { continue; }
                let parent_card = bc[l - 1];
                if parent_card % 2 == 1 {
                    odd_parent_count += 1;
                    let half_d = parent_card / 2;
                    let mut subregs_card: usize = 0;
                    for d in 0..=(k - l) {
                        subregs_card += (1usize << d) * bc[l + d];
                    }
                    let bag_size = (1usize << k) / (1usize << l);
                    let deficit = bag_size.saturating_sub(subregs_card);
                    let cap = capacity(k, t, l);
                    let denom = 8.0 * A.powi(3) - 2.0 * A;
                    if deficit as f64 > half_d as f64 + cap / denom - 0.01 {
                        odd_tight_count += 1;
                        println!(
                            "TIGHT+ODD: k={k} t={t} l={l} deficit={deficit} half_D={half_d} \
                             parent_card={parent_card} cap/(8A³-2A)={:.6}",
                            cap / denom
                        );
                    }
                }
            }
        }
    }
    println!("Odd parent: {odd_parent_count}, Tight+odd: {odd_tight_count}");
}
