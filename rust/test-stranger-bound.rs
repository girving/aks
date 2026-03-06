#!/usr/bin/env -S cargo +nightly -Zscript
//! Test the stranger bound induction step from AKS/Bags/Strange.lean
//!
//! V3: Clearer before/after logic for separator tests

use std::collections::{HashMap, HashSet};

// ============================================================================
// Parameters
// ============================================================================

#[derive(Clone, Copy, Debug)]
struct Params {
    gamma: f64,
    eps: f64,
    nu: f64,
    a: f64,
}

impl Params {
    fn new(gamma: f64, eps: f64, a: f64) -> Self {
        let nu = 2.0 * a * eps + 1.0 / a + 0.01;
        Params { gamma, eps, nu, a }
    }

    fn parent_eq1_coeff(&self) -> f64 {
        let term1 = self.eps * self.gamma / self.a;
        let term2 = self.eps / (2.0 * self.a);
        let denom = 1.0 - (2.0 * self.eps * self.a).powi(2);
        let term3 = if denom > 0.0 {
            2.0 * self.gamma * self.eps * self.a / denom
        } else {
            f64::INFINITY
        };
        let term4 = 1.0 / (8.0 * self.a.powi(3) - 2.0 * self.a);
        term1 + term2 + term3 + term4
    }
}

// ============================================================================
// Bag Structure
// ============================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Bag {
    k: usize,
    l: usize,
    x: usize,
}

impl Bag {
    fn new(k: usize, l: usize, x: usize) -> Self {
        Bag { k, l, x }
    }

    fn lo(&self) -> usize {
        self.x * (1 << (self.k - self.l))
    }

    fn hi(&self) -> usize {
        (self.x + 1) * (1 << (self.k - self.l))
    }

    fn parent(&self) -> Option<Bag> {
        if self.l == 0 { None }
        else { Some(Bag::new(self.k, self.l - 1, self.x / 2)) }
    }

    fn ancestor(&self, j: usize) -> Bag {
        if j > self.l { Bag::new(self.k, 0, 0) }
        else { Bag::new(self.k, self.l - j, self.x / (1 << j)) }
    }

    fn is_native(&self, value: usize) -> bool {
        self.lo() <= value && value < self.hi()
    }

    fn is_j_stranger(&self, j: usize, value: usize) -> bool {
        if j == 0 { false }
        else { !self.ancestor(j - 1).is_native(value) }
    }
}

// ============================================================================
// Capacity
// ============================================================================

fn capacity(p: &Params, k: usize, t: usize, l: usize) -> f64 {
    p.a.powi(l as i32) * p.nu.powi(t as i32) * (1 << k) as f64
}

fn fringe(p: &Params, l: usize, s: usize) -> usize {
    if l == 0 { 0 } else { (p.gamma * s as f64).floor() as usize }
}

// ============================================================================
// Separator Simulation
// ============================================================================

/// Apply (γ, ε)-separator: approximately sort, but allow ε fraction of violations
fn apply_separator(
    values: &mut [usize],
    positions: &[usize],
    gamma: f64,
    eps: f64,
) {
    if positions.len() < 2 { return; }
    let s = positions.len();

    // Get (position, value) pairs
    let mut items: Vec<(usize, usize)> = positions.iter()
        .map(|&p| (p, values[p]))
        .collect();

    // Sort by value
    items.sort_by_key(|&(_, v)| v);

    // Sorted positions
    let mut sorted_pos: Vec<usize> = positions.to_vec();
    sorted_pos.sort();

    // First, assign perfectly sorted
    for (i, &pos) in sorted_pos.iter().enumerate() {
        values[pos] = items[i].1;
    }

    // Now introduce adversarial violations up to ε bound
    // For SepInitial: items with value rank < boundary at positions ≥ boundary
    let boundary = (gamma * s as f64).floor() as usize;
    if boundary == 0 || boundary >= s { return; }

    // Violation budget: count ≤ ε * threshold means count ≤ floor(ε * threshold)
    // Since count is a natural number
    let low_budget = (eps * boundary as f64).floor() as usize;
    let high_budget = (eps * boundary as f64).floor() as usize;

    // Swap some low-value items to high positions (violate SepInitial maximally)
    for i in 0..low_budget.min(boundary).min(s - boundary) {
        let low_pos = sorted_pos[i];
        let high_pos = sorted_pos[boundary + i];
        values.swap(low_pos, high_pos);
    }

    // Also swap some high-value items to low positions (violate SepFinal maximally)
    // High values are at positions [s-boundary, s), swap some to [0, boundary)
    for i in 0..high_budget.min(boundary).min(s - boundary) {
        // Swap position s-boundary+i (high value) with position boundary-1-i (low position)
        // But we already swapped some, so need to be careful
        // Actually, let's swap from the other end
        if boundary > low_budget + i {
            let high_val_pos = sorted_pos[s - 1 - i];  // position with high-ranked value
            let low_pos = sorted_pos[boundary - 1 - i];  // position just below boundary
            values.swap(high_val_pos, low_pos);
        }
    }
}

// ============================================================================
// Split Logic
// ============================================================================

struct Split {
    to_parent: Vec<usize>,
    to_left: Vec<usize>,
    to_right: Vec<usize>,
}

fn split_positions(positions: &[usize], f: usize) -> Split {
    let s = positions.len();
    if s == 0 || f == 0 {
        return Split {
            to_parent: vec![],
            to_left: positions[..s/2].to_vec(),
            to_right: positions[s/2..].to_vec(),
        };
    }

    let mut sorted: Vec<usize> = positions.to_vec();
    sorted.sort();

    // toParent: first f and last f positions (or first 2f if overlapping)
    let parent_size = (2 * f).min(s);
    let to_parent: Vec<usize> = sorted[..f.min(s)].iter()
        .chain(sorted[s.saturating_sub(f)..].iter())
        .copied()
        .collect::<HashSet<_>>()
        .into_iter()
        .collect();

    // Middle: everything else, split between left and right
    let middle: Vec<usize> = sorted.iter()
        .filter(|p| !to_parent.contains(p))
        .copied()
        .collect();

    let mid = middle.len() / 2;
    let to_left = middle[..mid].to_vec();
    let to_right = middle[mid..].to_vec();

    Split { to_parent, to_left, to_right }
}

// ============================================================================
// Test: separator_middle_stranger_le
// ============================================================================

/// Test: after separator, strangers in middle ≤ various bounds
fn test_separator_middle(
    values: &[usize],  // values BEFORE separator
    positions: &[usize],
    bag: &Bag,
    j: usize,
    p: &Params,
) -> Option<SeparatorResult> {
    if positions.len() < 4 { return None; }

    let s = positions.len();
    let f = fringe(p, bag.l, s);
    let threshold = (p.gamma * s as f64).floor() as usize;
    let anc = bag.ancestor(if j > 0 { j - 1 } else { 0 });

    // Count strangers by type BEFORE separator
    let low_strangers: usize = positions.iter()
        .filter(|&&pos| values[pos] < anc.lo())
        .count();
    let high_strangers: usize = positions.iter()
        .filter(|&&pos| values[pos] >= anc.hi())
        .count();
    let total_before = low_strangers + high_strangers;

    if total_before == 0 {
        return Some(SeparatorResult {
            ratio_eps_T: 0.0,
            ratio_2eps_thresh: 0.0,
            ratio_refined: 0.0,
            middle_strangers: 0,
            total_strangers: 0,
            threshold,
            low: low_strangers,
            high: high_strangers,
        });
    }

    // Apply separator
    let mut new_values = values.to_vec();
    apply_separator(&mut new_values, positions, p.gamma, p.eps);

    // Split to get middle
    let split = split_positions(positions, f);
    let middle: Vec<usize> = split.to_left.iter()
        .chain(split.to_right.iter())
        .copied()
        .collect();

    // Count strangers in middle AFTER separator
    let middle_strangers: usize = middle.iter()
        .filter(|&&pos| {
            let v = new_values[pos];
            v < anc.lo() || v >= anc.hi()
        })
        .count();

    // Bound 1: ε × T (the claimed bound)
    let bound1 = p.eps * total_before as f64;
    let ratio1 = if bound1 > 0.0 { middle_strangers as f64 / bound1 } else { 0.0 };

    // Bound 2: 2·ε·threshold
    let bound2 = 2.0 * p.eps * threshold as f64;
    let ratio2 = if bound2 > 0.0 { middle_strangers as f64 / bound2 } else { 0.0 };

    // Bound 3: The CORRECT bound from SepInitial + SepFinal:
    // - SepInitial constrains ranks < threshold, so low strangers with rank ≥ threshold are unconstrained
    // - SepFinal constrains ranks ≥ s-threshold, so high strangers with rank < s-threshold are unconstrained
    //
    // Low strangers in middle ≤ min(L, floor(ε·thresh)) + max(0, L - threshold)
    // High strangers in middle ≤ min(H, floor(ε·thresh)) + max(0, H - threshold)
    //
    // But actually, if L > threshold, then:
    //   - Ranks 0..threshold-1 have ≤ floor(ε·thresh) at positions ≥ threshold
    //   - Ranks threshold..L-1 can be anywhere; after sorting they're at positions threshold..L-1
    //   - Positions threshold..L-1 ⊆ middle (since L-1 < s - threshold when L ≤ s/2)
    //   So (L - threshold) of them are in the middle
    let eps_thresh = (p.eps * threshold as f64).floor() as usize;
    let low_in_middle = low_strangers.min(eps_thresh) + low_strangers.saturating_sub(threshold);
    let high_in_middle = high_strangers.min(eps_thresh) + high_strangers.saturating_sub(threshold);
    let bound3 = (low_in_middle + high_in_middle) as f64;
    let ratio3 = if bound3 > 0.0 { middle_strangers as f64 / bound3 } else if middle_strangers == 0 { 0.0 } else { f64::INFINITY };

    Some(SeparatorResult {
        ratio_eps_T: ratio1,
        ratio_2eps_thresh: ratio2,
        ratio_refined: ratio3,
        middle_strangers,
        total_strangers: total_before,
        threshold,
        low: low_strangers,
        high: high_strangers,
    })
}

struct SeparatorResult {
    ratio_eps_T: f64,
    ratio_2eps_thresh: f64,
    ratio_refined: f64,  // min(L, eps·thresh) + min(H, eps·thresh)
    middle_strangers: usize,
    total_strangers: usize,
    threshold: usize,
    low: usize,
    high: usize,
}

// ============================================================================
// Test: parent_stranger_eq1_le
// ============================================================================

/// Test: 1-strangers from parent's middle ≤ coeff × capacity
fn test_parent_eq1(
    values: &[usize],  // values at parent (after parent's separator)
    parent_positions: &[usize],
    child: &Bag,
    p: &Params,
    t: usize,
) -> Option<(f64, usize, f64)> {  // (ratio, strangers, bound)
    if child.l == 0 { return None; }
    if parent_positions.len() < 4 { return None; }

    let s = parent_positions.len();
    let f = fringe(p, child.l - 1, s);  // parent's level

    // Split parent's registers
    let split = split_positions(parent_positions, f);

    // Child gets toLeft (if even x) or toRight (if odd x)
    let child_items = if child.x % 2 == 0 { &split.to_left } else { &split.to_right };
    if child_items.is_empty() { return None; }

    // Count 1-strangers at child level
    // 1-stranger at child = value outside child.ancestor(0) = child's own interval
    let strangers: usize = child_items.iter()
        .filter(|&&pos| !child.is_native(values[pos]))
        .count();

    // Bound: coeff × capacity(t, child.l)
    let coeff = p.parent_eq1_coeff();
    let bound = coeff * capacity(p, child.k, t, child.l);

    let ratio = if bound > 0.0 { strangers as f64 / bound } else { 0.0 };
    Some((ratio, strangers, bound))
}

// ============================================================================
// Adversarial Configuration: Create strangers deliberately
// ============================================================================

/// Create a configuration where bag has many strangers (up to IH bound)
fn create_adversarial_bag_config(
    k: usize,
    bag: &Bag,
    num_registers: usize,
    stranger_fraction: f64,  // fraction that should be strangers
) -> (Vec<usize>, Vec<usize>) {  // (values, positions)
    let n = 1 << k;
    let mut values: Vec<usize> = (0..n).collect();
    let positions: Vec<usize> = (0..num_registers).collect();

    // Make stranger_fraction of items be strangers (j=1)
    // A 1-stranger has value outside bag's interval [lo, hi)
    let num_strangers = (stranger_fraction * num_registers as f64).ceil() as usize;
    let num_native = num_registers - num_strangers;

    // Native values: in [bag.lo, bag.hi)
    let native_values: Vec<usize> = (bag.lo()..bag.hi()).take(num_native).collect();

    // Stranger values: outside [bag.lo, bag.hi)
    let stranger_values: Vec<usize> = (0..n)
        .filter(|&v| v < bag.lo() || v >= bag.hi())
        .take(num_strangers)
        .collect();

    // Assign values to positions
    for (i, &pos) in positions.iter().enumerate() {
        if i < native_values.len() {
            values[pos] = native_values[i];
        } else if i - native_values.len() < stranger_values.len() {
            values[pos] = stranger_values[i - native_values.len()];
        }
    }

    (values, positions)
}

// ============================================================================
// IH-Constrained Tests
// ============================================================================

/// Create a configuration where strangers satisfy IH: T ≤ γ·ε^(j-1)·cap
fn create_ih_constrained_config(
    k: usize,
    bag: &Bag,
    num_registers: usize,
    p: &Params,
    t: usize,
    j: usize,
) -> (Vec<usize>, Vec<usize>) {
    let n = 1 << k;
    let mut values: Vec<usize> = (0..n).collect();
    let positions: Vec<usize> = (0..num_registers).collect();

    // IH bound: T ≤ γ·ε^(j-1)·capacity
    let cap = capacity(p, k, t, bag.l);
    let max_strangers = (p.gamma * p.eps.powi((j - 1) as i32) * cap).floor() as usize;
    let num_strangers = max_strangers.min(num_registers / 2);  // cap at half

    let num_native = num_registers - num_strangers;

    // Native values: in [bag.lo, bag.hi)
    let native_values: Vec<usize> = (bag.lo()..bag.hi()).take(num_native).collect();

    // Stranger values: outside [bag.lo, bag.hi)
    let stranger_values: Vec<usize> = (0..n)
        .filter(|&v| v < bag.lo() || v >= bag.hi())
        .take(num_strangers)
        .collect();

    // Assign values to positions
    for (i, &pos) in positions.iter().enumerate() {
        if i < native_values.len() {
            values[pos] = native_values[i];
        } else if i - native_values.len() < stranger_values.len() {
            values[pos] = stranger_values[i - native_values.len()];
        }
    }

    (values, positions)
}

/// Test separator_middle under IH constraint
fn run_separator_middle_ih_tests(p: &Params, k: usize) {
    println!("\n--- separator_middle_stranger_le (IH-constrained) k={} ---", k);

    let n = 1 << k;
    let mut max_ratio1 = 0.0f64;
    let mut max_ratio2 = 0.0f64;
    let mut max_ratio3 = 0.0f64;
    let mut total_tests = 0;
    let mut violations1 = 0;
    let mut violations2 = 0;
    let mut violations3 = 0;

    for l in 1..=k.min(4) {
        for x in 0..(1 << l).min(4) {
            let bag = Bag::new(k, l, x);

            for &num_regs in &[32, 64, 128, 256] {
                if num_regs > n / 2 { continue; }

                for t in 1..=4 {
                    for j in 1..=3 {
                        let (values, positions) = create_ih_constrained_config(
                            k, &bag, num_regs, p, t, j
                        );

                        if let Some(r) = test_separator_middle(&values, &positions, &bag, j, p) {
                            total_tests += 1;
                            max_ratio1 = max_ratio1.max(r.ratio_eps_T);
                            max_ratio2 = max_ratio2.max(r.ratio_2eps_thresh);
                            max_ratio3 = max_ratio3.max(r.ratio_refined);
                            if r.ratio_eps_T > 1.0 { violations1 += 1; }
                            if r.ratio_2eps_thresh > 1.0 { violations2 += 1; }
                            if r.ratio_refined > 1.0 {
                                violations3 += 1;
                                println!("  IH REFINED FAIL: l={}, x={}, t={}, j={}, mid={}, L={}, H={}, thresh={}",
                                         l, x, t, j, r.middle_strangers, r.low, r.high, r.threshold);
                            }
                        }
                    }
                }
            }
        }
    }

    println!("  Total tests: {}", total_tests);
    println!("  Bound ε·T:                    Max: {:.4}, Violations: {}", max_ratio1, violations1);
    println!("  Bound 2·ε·thresh:             Max: {:.4}, Violations: {}", max_ratio2, violations2);
    println!("  Bound min(L,εt)+min(H,εt):    Max: {:.4}, Violations: {}", max_ratio3, violations3);
}

// ============================================================================
// Main Tests
// ============================================================================

fn run_separator_middle_tests(p: &Params, k: usize) {
    println!("\n--- separator_middle_stranger_le tests (k={}) ---", k);

    let n = 1 << k;
    let mut max_ratio1 = 0.0f64;  // ε·T bound
    let mut max_ratio2 = 0.0f64;  // 2·ε·threshold bound
    let mut max_ratio3 = 0.0f64;  // refined bound
    let mut total_tests = 0;
    let mut violations1 = 0;
    let mut violations2 = 0;
    let mut violations3 = 0;

    // Test for various bags and stranger fractions
    for l in 1..=k.min(4) {
        for x in 0..(1 << l).min(4) {
            let bag = Bag::new(k, l, x);

            // Various register sizes
            for &num_regs in &[16, 32, 64, 128] {
                if num_regs > n / 2 { continue; }

                // Various stranger fractions
                for &stranger_frac in &[0.1, 0.2, 0.3, 0.4, 0.5] {
                    let (values, positions) = create_adversarial_bag_config(
                        k, &bag, num_regs, stranger_frac
                    );

                    for j in 1..=2 {
                        if let Some(r) = test_separator_middle(&values, &positions, &bag, j, p) {
                            total_tests += 1;
                            max_ratio1 = max_ratio1.max(r.ratio_eps_T);
                            max_ratio2 = max_ratio2.max(r.ratio_2eps_thresh);
                            max_ratio3 = max_ratio3.max(r.ratio_refined);
                            if r.ratio_eps_T > 1.0 { violations1 += 1; }
                            if r.ratio_2eps_thresh > 1.0 { violations2 += 1; }
                            if r.ratio_refined > 1.0 {
                                violations3 += 1;
                                println!("  REFINED FAIL: l={}, x={}, j={}, mid={}, L={}, H={}, thresh={}, r3={:.4}",
                                         l, x, j, r.middle_strangers, r.low, r.high, r.threshold, r.ratio_refined);
                            }
                        }
                    }
                }
            }
        }
    }

    println!("  Total tests: {}", total_tests);
    println!("  Bound ε·T:                    Max: {:.4}, Violations: {}", max_ratio1, violations1);
    println!("  Bound 2·ε·thresh:             Max: {:.4}, Violations: {}", max_ratio2, violations2);
    println!("  Bound min(L,εt)+min(H,εt):    Max: {:.4}, Violations: {}", max_ratio3, violations3);
}

fn run_parent_eq1_tests(p: &Params, k: usize, t: usize) {
    println!("\n--- parent_stranger_eq1_le tests (k={}, t={}) ---", k, t);

    let n = 1 << k;
    let mut max_ratio = 0.0f64;
    let mut total_tests = 0;
    let mut violations = 0;

    // Test for various child bags
    for l in 1..=k.min(4) {
        for x in 0..(1 << l).min(4) {
            let child = Bag::new(k, l, x);
            let parent = child.parent().unwrap();

            // Parent's registers
            for &num_parent_regs in &[32, 64, 128, 256] {
                if num_parent_regs > n { continue; }

                // Create adversarial config at parent
                // Parent has strangers at various fractions
                for &parent_stranger_frac in &[0.0, 0.1, 0.2, 0.3] {
                    let (mut values, parent_positions) = create_adversarial_bag_config(
                        k, &parent, num_parent_regs, parent_stranger_frac
                    );

                    // Apply separator to parent
                    apply_separator(&mut values, &parent_positions, p.gamma, p.eps);

                    if let Some((ratio, strangers, bound)) =
                        test_parent_eq1(&values, &parent_positions, &child, p, t)
                    {
                        total_tests += 1;
                        max_ratio = max_ratio.max(ratio);
                        if ratio > 1.0 {
                            violations += 1;
                            println!("  VIOLATION: child=({},{}), ratio={:.4}, str={}, bound={:.2}",
                                     l, x, ratio, strangers, bound);
                        }
                    }
                }
            }
        }
    }

    println!("  Total tests: {}, Max ratio: {:.4}, Violations: {}",
             total_tests, max_ratio, violations);
    println!("  (coeff = {:.6})", p.parent_eq1_coeff());
}

fn main() {
    println!("Stranger Bound Sublemma Tests (V4)");
    println!("==================================\n");

    let params_list = vec![
        (0.25, 0.1, 2.0),
        (0.25, 0.15, 2.0),
        (0.25, 0.2, 2.0),
    ];

    for (gamma, eps, a) in params_list {
        let p = Params::new(gamma, eps, a);
        println!("\n{}", "=".repeat(60));
        println!("Parameters: γ={}, ε={}, A={}", gamma, eps, a);
        println!("  ν={:.4}, coeff={:.6}", p.nu, p.parent_eq1_coeff());

        println!("\n=== UNCONSTRAINED TESTS (adversarial) ===");
        for k in 6..=8 {
            run_separator_middle_tests(&p, k);
        }

        println!("\n=== IH-CONSTRAINED TESTS ===");
        for k in 6..=8 {
            run_separator_middle_ih_tests(&p, k);
        }

        println!("\n=== parent_stranger_eq1_le TESTS ===");
        for k in 6..=8 {
            for t in 1..=3 {
                run_parent_eq1_tests(&p, k, t);
            }
        }
    }

    println!("\nDone.");
}
