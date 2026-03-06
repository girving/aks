#!/usr/bin/env -S cargo +nightly -Zscript
//! Verify bagCard conservation: Σ 2^l * bagCard(l) = 2^k

const GAMMA: f64 = 1.0 / 100.0;
const NU: f64 = 13.0 / 20.0;
const A: f64 = 10.0;

fn capacity(k: usize, t: usize, l: usize) -> f64 {
    (1u64 << k) as f64 * NU.powi(t as i32) * A.powi(l as i32)
}
fn fringe(k: usize, t: usize, l: usize, sz: usize) -> usize {
    if l == 0 { 0 } else { ((GAMMA * capacity(k, t, l)).floor() as usize).min(sz / 2) }
}
fn split_parent(sz: usize, f: usize) -> usize { (sz - f) / 2 }
fn split_child(sz: usize, f: usize) -> usize { (sz + f) / 2 }

fn bag_card(k: usize, t: usize) -> Vec<usize> {
    let mut bc = vec![0usize; k + 1];
    if t == 0 { bc[0] = 1 << k; return bc; }
    let prev = bag_card(k, t - 1);
    for l in 0..=k {
        let fc = if l + 1 <= k {
            2 * split_parent(prev[l+1], fringe(k, t-1, l+1, prev[l+1]))
        } else { 0 };
        let fp = if l == 0 {
            split_parent(prev[0], fringe(k, t-1, 0, prev[0]))
        } else {
            split_child(prev[l-1], fringe(k, t-1, l-1, prev[l-1]))
        };
        bc[l] = fc + fp;
    }
    bc
}

fn main() {
    for k in 10..=14 {
        let target = 1usize << k;
        for t in 0..=80 {
            let bc = bag_card(k, t);
            let sum: usize = (0..=k).map(|l| (1 << l) * bc[l]).sum();
            if sum != target {
                println!("CONSERVATION FAIL: k={k} t={t} sum={sum} target={target}");
                for l in 0..=k {
                    if bc[l] > 0 {
                        println!("  bc[{l}] = {}", bc[l]);
                    }
                }
            }
        }
    }
    println!("Done checking conservation.");

    // For early stages, print bc vector
    let k = 10;
    let tgt = 1usize << k;
    for t in 0..=5 {
        let bc = bag_card(k, t);
        let active: Vec<_> = (0..=k).filter(|&l| bc[l] > 0).map(|l| format!("bc[{l}]={}", bc[l])).collect();
        println!("k={k} t={t}: {}", active.join(", "));

        // Check: for each level l >= 1 with (t+l-1)%2==0
        for l in 1..=k {
            if (t + l - 1) % 2 != 0 { continue; }
            let subregs_sum: usize = (0..=(k-l)).map(|d| (1 << d) * bc[l+d]).sum();
            let bag_size = tgt / (1 << l);
            if subregs_sum > bag_size {
                // Deficit is negative = ancestors have TOO MANY items
                let ancestor_sum: usize = (0..l).map(|lp| (1 << lp) * bc[lp]).sum();
                println!("  l={l}: subregs_sum={subregs_sum} > bag_size={bag_size}, ancestor_sum={ancestor_sum}");
            }
        }
    }
}
