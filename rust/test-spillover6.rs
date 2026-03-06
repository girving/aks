#!/usr/bin/env -S cargo +nightly -Zscript
//! Check: is parent_card always even when hpar_active holds?

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
    let mut odd_count = 0u64;
    for k in 10..=16 {
        let ns = num_stages(k);
        for t in 0..=ns {
            let bc = bag_card(k, t);
            for l in 1..=k {
                if (t + l - 1) % 2 != 0 { continue; }
                let parent_card = bc[l - 1];
                if parent_card % 2 != 0 {
                    odd_count += 1;
                    if odd_count <= 20 {
                        println!("ODD parent: k={k} t={t} l={l} parent_l={} parent_card={parent_card}", l-1);
                        // Print ancestors
                        for l2 in 0..l-1 {
                            if bc[l2] > 0 {
                                println!("  bc[{l2}] = {} (active={})", bc[l2], (t+l2)%2 == 0);
                            }
                        }
                    }
                }
            }
        }
    }
    println!("Total odd parent cases: {odd_count}");
}
