#!/usr/bin/env -S cargo +nightly -Zscript
//! Test the FINAL stranger_bound theorem (the one that matters).
//! stranger_bound says: strangers_j ≤ γ · ε^(j-1) · cap.
//! Even if spillover_bound is wrong, the final theorem might still hold.

const GAMMA: f64 = 1.0 / 100.0;
const EPS: f64 = 1.0 / 100.0;
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

    // Test the actual parent_stranger_eq1_le bound:
    // source3 ≤ (budget_coefficient) * cap
    // where budget includes TWO 1/(8A³-2A) terms.
    // The entire parent_stranger_eq1_le uses spillover ONCE.
    //
    // What if we change spillover to use:
    //   deficit ≤ ↑(parent_card / 2) + 1 / (8A³ - 2A) * cap + ↑(parent_card % 2) / 2
    // This adds at most 1/2.
    //
    // Check: is the SECOND 1/(8A³-2A) term big enough to absorb 1/2?

    for k in 10..=16 {
        let ns = num_stages(k);
        for t in 0..=ns {
            let bc = bag_card(k, t);
            for l in 1..=k {
                if (t + l - 1) % 2 != 0 { continue; }
                let parent_card = bc[l - 1];
                if parent_card % 2 == 0 { continue; }

                let cap = capacity(k, t, l);
                let second_term = cap / denom_val;

                // The second 1/(8A³-2A) is supposed to absorb the
                // parity correction from a DIFFERENT spillover (the
                // one for the b.l-1 level in the final assembly).
                // But actually both spillovers are for the same
                // parent. So both get the same 1/2 correction.

                if second_term < 0.5 + 1e-9 {
                    println!("k={k} t={t} l={l}: cap/(8A³-2A) = {second_term:.6} < 0.5, pc={parent_card}");
                }
            }
        }
    }

    println!("\n--- Alternative: use 1/(4A³-A) instead of 1/(8A³-2A) ---");
    // 1/(4A³-A) = 2/(8A³-2A) = twice the current coefficient.
    // This absorbs the 1/2 parity issue since 1/(4A³-A)*cap ≥ 1/2 + 1/(8A³-2A)*cap
    // iff cap * (1/(4A³-A) - 1/(8A³-2A)) ≥ 1/2
    // iff cap / (8A³-2A) ≥ 1/2
    // This doesn't hold for small cap!

    // Actually, the issue is simpler. Just change hC4_eq1 to:
    // ... + 1/(4A³-A) + ... (instead of + 1/(8A³-2A) + ...)
    // But this changes the Params constraint. Let me check if seiferasParams still satisfies it.

    let new_coeff = 1.0 / (4.0 * A * A * A - A);
    let old_coeff = 1.0 / (8.0 * A * A * A - 2.0 * A);
    println!("Old coeff: {old_coeff:.8}");
    println!("New coeff: {new_coeff:.8}");
    println!("Difference: {:.8}", new_coeff - old_coeff);

    // Check hC4_eq1 with new coefficient:
    let budget = 2.0*GAMMA*EPS*A
        + EPS*GAMMA/A + EPS/(2.0*A)
        + 2.0*GAMMA*EPS*A / (1.0 - (2.0*EPS*A).powi(2))
        + new_coeff  // was old_coeff
        + GAMMA/A
        + new_coeff; // was old_coeff
    let rhs = GAMMA * NU;
    println!("Budget with 1/(4A³-A): {budget:.10}");
    println!("γν: {rhs:.10}");
    println!("Slack: {:.10}", rhs - budget);

    // With ONE changed and one unchanged:
    let budget2 = 2.0*GAMMA*EPS*A
        + EPS*GAMMA/A + EPS/(2.0*A)
        + 2.0*GAMMA*EPS*A / (1.0 - (2.0*EPS*A).powi(2))
        + new_coeff  // spillover: changed
        + GAMMA/A
        + old_coeff; // other: unchanged
    println!("\nBudget with ONE changed: {budget2:.10}");
    println!("Slack: {:.10}", rhs - budget2);
}
