#!/usr/bin/env -S cargo +nightly -Zscript
//! Detailed spillover diagnostics: when parent_card is odd, what's cap/(8A³-2A)?

const GAMMA: f64 = 1.0 / 100.0;
const NU: f64 = 13.0 / 20.0;
const A: f64 = 10.0;

fn capacity(k: usize, t: usize, l: usize) -> f64 {
    (1u64 << k) as f64 * NU.powi(t as i32) * A.powi(l as i32)
}

fn fringe(_k: usize, t: usize, l: usize, sz: usize) -> usize {
    if l == 0 { 0 }
    else {
        let cap = capacity(_k, t, l);
        let f = (GAMMA * cap).floor() as usize;
        f.min(sz / 2)
    }
}

fn bag_card(k: usize, t: usize) -> Vec<usize> {
    let mut bc = vec![0usize; k + 1];
    if t == 0 { bc[0] = 1 << k; return bc; }
    let prev = bag_card(k, t - 1);
    for l in 0..=k {
        let fc = if l + 1 <= k {
            2 * split_parent_card(prev[l + 1], fringe(k, t - 1, l + 1, prev[l + 1]))
        } else { 0 };
        let fp = if l == 0 {
            split_parent_card(prev[0], fringe(k, t - 1, 0, prev[0]))
        } else {
            split_child_card(prev[l - 1], fringe(k, t - 1, l - 1, prev[l - 1]))
        };
        bc[l] = fc + fp;
    }
    bc
}

fn split_parent_card(sz: usize, f: usize) -> usize { (sz - f) / 2 }
fn split_child_card(sz: usize, f: usize) -> usize { (sz + f) / 2 }

fn num_stages(k: usize) -> usize {
    for t in 0..1000 {
        if capacity(k, t, k - 2) < A { return t.saturating_sub(1); }
    }
    999
}

fn main() {
    let mut min_cap_over_denom = f64::MAX;
    let denom = 8.0 * A.powi(3) - 2.0 * A;

    for k in 10..=18 {
        let ns = num_stages(k);
        for t in 0..=ns {
            let bc = bag_card(k, t);
            for l in 1..=k {
                if (t + l - 1) % 2 != 0 { continue; }
                let parent_card = bc[l - 1];
                if parent_card % 2 == 1 {
                    let cap = capacity(k, t, l);
                    let ratio = cap / denom;
                    if ratio < min_cap_over_denom {
                        min_cap_over_denom = ratio;
                        println!("New min cap/(8A³-2A): k={k} t={t} l={l} parent_card={parent_card} ratio={ratio:.6}");
                    }
                }
            }
        }
    }
    println!("\nMinimum cap/(8A³-2A) when parent is odd: {min_cap_over_denom:.6}");

    // Also: check deficit - half_D vs cap/(8A³-2A) when parent is odd
    println!("\n--- Checking deficit - half_D vs cap/(8A³-2A) when parent is odd ---");
    let mut max_diff_ratio = 0.0f64;
    for k in 10..=18 {
        let ns = num_stages(k);
        for t in 0..=ns {
            let bc = bag_card(k, t);
            for l in 1..=k {
                if (t + l - 1) % 2 != 0 { continue; }
                let parent_card = bc[l - 1];
                if parent_card % 2 != 1 { continue; }
                let half_d = parent_card / 2;
                let mut subregs_card: usize = 0;
                for d in 0..=(k - l) {
                    subregs_card += (1usize << d) * bc[l + d];
                }
                let bag_size = (1usize << k) / (1usize << l);
                let deficit = bag_size.saturating_sub(subregs_card);
                let diff = deficit - half_d; // should be a natural number
                let cap = capacity(k, t, l);
                let bound = cap / denom;
                let r = diff as f64 / bound;
                if r > max_diff_ratio {
                    max_diff_ratio = r;
                    println!("k={k} t={t} l={l} deficit={deficit} half_D={half_d} diff={diff} bound={bound:.4} ratio={r:.6}");
                }
            }
        }
    }
    println!("Max (deficit - half_D) / (cap/(8A³-2A)) when parent odd: {max_diff_ratio:.6}");
}
