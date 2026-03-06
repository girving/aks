#!/usr/bin/env -S cargo +nightly -Zscript
//! Test that stages_regs_contiguous holds: wire indices in each bag
//! lie within the bag's native interval [lo, hi).
//!
//! This mirrors the Lean construction in AKS/Bags/Network.lean.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

fn bag_size(k: usize, level: usize) -> usize {
    (1 << k) / (1 << level)
}

fn bag_lo(k: usize, level: usize, x: usize) -> usize {
    x * bag_size(k, level)
}

fn bag_hi(k: usize, level: usize, x: usize) -> usize {
    (x + 1) * bag_size(k, level)
}

/// A bag identified by (level, x)
type Bag = (usize, usize);

/// Placement: maps each bag to its set of wire indices
type Placement = BTreeMap<Bag, BTreeSet<usize>>;

fn fringe(gamma: f64, k: usize, t: usize, level: usize, s: usize, a: f64, nu: f64) -> usize {
    if level == 0 {
        0
    } else if k <= level + 1 {
        s / 2
    } else {
        let cap = (1u64 << k) as f64 * nu.powi(t as i32) * a.powi(level as i32);
        (gamma * cap).floor().max(0.0) as usize
    }
}

/// Split a sorted set of wires by position and fringe size
fn split(regs: &BTreeSet<usize>, f: usize) -> (BTreeSet<usize>, BTreeSet<usize>, BTreeSet<usize>) {
    let sorted: Vec<usize> = regs.iter().copied().collect(); // already sorted (BTreeSet)
    let s = sorted.len();
    let h = s / 2 - f.min(s / 2);

    let mut to_parent = BTreeSet::new();
    let mut to_left = BTreeSet::new();
    let mut to_right = BTreeSet::new();

    for (j, &wire) in sorted.iter().enumerate() {
        if j < f || j >= f + 2 * h {
            to_parent.insert(wire);
        } else if j < f + h {
            to_left.insert(wire);
        } else {
            to_right.insert(wire);
        }
    }

    (to_parent, to_left, to_right)
}

fn start(k: usize) -> Placement {
    let mut pl = BTreeMap::new();
    let n = 1 << k;
    let root: Bag = (0, 0);
    pl.insert(root, (0..n).collect());
    pl
}

/// One stage: split all bags, then rebag via stageRegs
fn stage(pl: &Placement, k: usize, t: usize, gamma: f64, a: f64, nu: f64) -> Placement {
    // First, compute splits for all bags
    let mut splits: BTreeMap<Bag, (BTreeSet<usize>, BTreeSet<usize>, BTreeSet<usize>)> = BTreeMap::new();

    // Collect all bags that exist (have wires or might receive wires)
    // We need splits for all bags at all levels
    for level in 0..=k {
        for x in 0..(1 << level) {
            let bag: Bag = (level, x);
            let regs = pl.get(&bag).cloned().unwrap_or_default();
            let s = regs.len();
            let f = fringe(gamma, k, t, level, s, a, nu);
            splits.insert(bag, split(&regs, f));
        }
    }

    // Now rebag via stageRegs
    let mut new_pl: Placement = BTreeMap::new();

    for level in 0..=k {
        for x in 0..(1usize << level) {
            let bag: Bag = (level, x);
            let mut wires = BTreeSet::new();

            // fromChildren: left and right children's toParent
            if level < k {
                let left: Bag = (level + 1, 2 * x);
                let right: Bag = (level + 1, 2 * x + 1);
                if let Some((tp, _, _)) = splits.get(&left) {
                    wires.extend(tp);
                }
                if let Some((tp, _, _)) = splits.get(&right) {
                    wires.extend(tp);
                }
            }

            // fromParent
            if level == 0 {
                // Root keeps its own toParent
                if let Some((tp, _, _)) = splits.get(&bag) {
                    wires.extend(tp);
                }
            } else {
                let parent: Bag = (level - 1, x / 2);
                if x % 2 == 0 {
                    // Left child: gets toLeft from parent
                    if let Some((_, tl, _)) = splits.get(&parent) {
                        wires.extend(tl);
                    }
                } else {
                    // Right child: gets toRight from parent
                    if let Some((_, _, tr)) = splits.get(&parent) {
                        wires.extend(tr);
                    }
                }
            }

            if !wires.is_empty() {
                new_pl.insert(bag, wires);
            }
        }
    }

    new_pl
}

/// Check containment: all wires in bag (level, x) are in [lo, hi)
fn check_containment(pl: &Placement, k: usize, stage_num: usize) -> bool {
    let mut ok = true;
    for (&(level, x), wires) in pl.iter() {
        let lo = bag_lo(k, level, x);
        let hi = bag_hi(k, level, x);
        for &wire in wires {
            if wire < lo || wire >= hi {
                eprintln!(
                    "VIOLATION at stage {}: wire {} in bag (level={}, x={}) but interval [{}, {})",
                    stage_num, wire, level, x, lo, hi
                );
                ok = false;
            }
        }
    }
    ok
}

/// Also check the balance property: for non-leaf bags, count wires in each child's interval
fn check_balance(pl: &Placement, k: usize, stage_num: usize) {
    for (&(level, x), wires) in pl.iter() {
        if level >= k { continue; } // leaf
        let mid = bag_lo(k, level, x) + bag_size(k, level + 1); // = left child's hi
        let left_count = wires.iter().filter(|&&w| w < mid).count();
        let right_count = wires.iter().filter(|&&w| w >= mid).count();
        let s = wires.len();
        if left_count != s / 2 && right_count != s / 2 {
            eprintln!(
                "IMBALANCE at stage {}: bag (level={}, x={}) has {} wires, left_count={}, right_count={}, s/2={}",
                stage_num, level, x, s, left_count, right_count, s / 2
            );
        }
    }
}

/// Collect all wires in the subtree rooted at bag (level, x)
fn subregs(pl: &Placement, k: usize, level: usize, x: usize) -> BTreeSet<usize> {
    let bag: Bag = (level, x);
    let mut result = pl.get(&bag).cloned().unwrap_or_default();
    if level < k {
        let left = subregs(pl, k, level + 1, 2 * x);
        let right = subregs(pl, k, level + 1, 2 * x + 1);
        result.extend(left);
        result.extend(right);
    }
    result
}

/// Check subtree containment: all wires in subregs(b) are in [b.lo, b.hi)
fn check_subtree_containment(pl: &Placement, k: usize, stage_num: usize) -> bool {
    let mut ok = true;
    for level in 0..=k {
        for x in 0..(1 << level) {
            let lo = bag_lo(k, level, x);
            let hi = bag_hi(k, level, x);
            let sub = subregs(pl, k, level, x);
            for &wire in &sub {
                if wire < lo || wire >= hi {
                    eprintln!(
                        "SUBTREE VIOLATION at stage {}: wire {} in subregs(l={}, x={}) but interval [{}, {})",
                        stage_num, wire, level, x, lo, hi
                    );
                    ok = false;
                }
            }
        }
    }
    ok
}

fn main() {
    let params: Vec<(f64, f64, f64)> = vec![
        // (gamma, a, nu)
        (0.25, 2.0, 0.8),
        (0.5, 2.0, 0.8),
        (0.1, 3.0, 0.9),
        (0.3, 1.5, 0.7),
    ];

    let mut violations = 0;
    let mut first_violation_shown = false;

    for k in 2..=10 {
        for &(gamma, a, nu) in &params {
            let num_stages = (2 * k).min(20);
            let mut pl = start(k);

            for t in 0..=num_stages {
                if !check_containment(&pl, k, t) {
                    violations += 1;
                    if !first_violation_shown {
                        println!("FIRST VIOLATION: k={}, gamma={}, a={}, nu={}, stage={}", k, gamma, a, nu, t);
                        // Print all wires in violating bags
                        for (&(level, x), wires) in pl.iter() {
                            let lo = bag_lo(k, level, x);
                            let hi = bag_hi(k, level, x);
                            let bad: Vec<_> = wires.iter().filter(|&&w| w < lo || w >= hi).collect();
                            if !bad.is_empty() {
                                println!("  bag(l={},x={}): wires={:?}, interval=[{},{}), bad={:?}",
                                    level, x, wires, lo, hi, bad);
                            }
                        }
                        first_violation_shown = true;
                    }
                }
                if t < num_stages {
                    pl = stage(&pl, k, t, gamma, a, nu);
                }
            }
        }
    }

    if violations == 0 {
        println!("ALL TESTS PASSED: stages_regs_contiguous holds for k=2..10, {} parameter sets", params.len());
    } else {
        println!("FAILED: {} stage-violations found for per-bag containment", violations);
    }

    // Show details of a specific violation
    {
        let k = 5;
        let gamma = 0.3;
        let a = 1.5;
        let nu = 0.7;
        let mut pl = start(k);
        for t in 0..7 {
            pl = stage(&pl, k, t, gamma, a, nu);
        }
        println!("\nDetailed state at k=5, stage=7 (gamma=0.3, a=1.5, nu=0.7):");
        for level in 0..=k {
            for x in 0..(1usize << level) {
                let bag: Bag = (level, x);
                if let Some(wires) = pl.get(&bag) {
                    if !wires.is_empty() {
                        let lo = bag_lo(k, level, x);
                        let hi = bag_hi(k, level, x);
                        let bad: Vec<_> = wires.iter().filter(|&&w| w < lo || w >= hi).copied().collect();
                        let tag = if bad.is_empty() { "" } else { " *** BAD ***" };
                        println!("  l={} x={}: {:?} interval=[{},{}){}",
                            level, x, wires, lo, hi, tag);
                    }
                }
            }
        }
    }

    // Test: does containment hold at stages where ancestors ARE empty?
    println!("\n--- Testing containment when ancestor bags are empty ---");
    let mut empty_viol = 0;
    for k in 3..=10 {
        let finish_level = if k >= 2 { k - 2 } else { k };
        for &(gamma, a, nu) in &params {
            let num_stages = (3 * k).min(30);
            let mut pl = start(k);

            for t in 0..num_stages {
                pl = stage(&pl, k, t, gamma, a, nu);

                // Check if all ancestor bags (level < finish_level) are empty
                let mut ancestors_empty = true;
                for level in 0..finish_level {
                    for x in 0..(1usize << level) {
                        let bag: Bag = (level, x);
                        if let Some(wires) = pl.get(&bag) {
                            if !wires.is_empty() {
                                ancestors_empty = false;
                            }
                        }
                    }
                }

                if ancestors_empty {
                    // Check subtree containment at finish_level
                    let mut ok = true;
                    for x in 0..(1usize << finish_level) {
                        let lo = bag_lo(k, finish_level, x);
                        let hi = bag_hi(k, finish_level, x);
                        let sub = subregs(&pl, k, finish_level, x);
                        for &wire in &sub {
                            if wire < lo || wire >= hi {
                                if empty_viol < 5 {
                                    println!("VIOLATION when ancestors empty: k={}, t={}, gamma={}, a={}, nu={}",
                                        k, t+1, gamma, a, nu);
                                    println!("  wire {} in subregs(l={}, x={}) but interval [{}, {})",
                                        wire, finish_level, x, lo, hi);
                                }
                                ok = false;
                            }
                        }
                        // Also check subregs covers all wires
                    }
                    if !ok {
                        empty_viol += 1;
                    }
                    break; // Found the convergence stage, move on
                }
            }
        }
    }
    if empty_viol == 0 {
        println!("ALL TESTS PASSED: subtree containment holds when ancestors are empty");
    } else {
        println!("FAILED: {} violations when ancestors are empty", empty_viol);
    }
}
