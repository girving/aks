#!/usr/bin/env -S cargo +nightly -Zscript
//! Detailed check of spillover violations: what is 'rest' exactly?

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
    let denom_val = 8.0 * A * A * A - 2.0 * A;

    for k in 10..=16 {
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

                // deficit (integer) = parent_card/2 (rational) + rest
                // = half_D + 1/2 + rest
                // So rest = deficit - half_D - 1/2
                let m = deficit as f64 - half_d as f64; // should be an integer
                let rest = m - 0.5; // rest = Σ_{l'<l-1,active} bc[l'] / 2^(l-l')

                // Compute rest from ancestor terms
                let mut rest_actual = 0.0f64;
                for lp in 0..l-1 {
                    if (t + lp) % 2 != 0 { continue; } // inactive
                    rest_actual += bc[lp] as f64 / (1u64 << (l - lp)) as f64;
                }

                let cap = capacity(k, t, l);
                let bound = cap / denom_val;

                if m > bound + 1e-9 {
                    println!("k={k} t={t} l={l}: pc={parent_card} deficit={deficit} hD={half_d} m={m:.0} rest={rest:.6} rest_actual={rest_actual:.6} bound={bound:.6}");
                    // Also: bound via bagCard_le_capacity
                    let mut geom_rest = 0.0f64;
                    for lp in 0..l-1 {
                        if (t + lp) % 2 != 0 { continue; }
                        let cap_lp = capacity(k, t, lp);
                        geom_rest += cap_lp / (1u64 << (l - lp)) as f64;
                    }
                    println!("  geom_bound_on_rest={geom_rest:.6} (should be ≤ {bound:.6})");
                }
            }
        }
    }
}
