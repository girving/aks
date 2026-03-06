#!/usr/bin/env -S cargo +nightly -Zscript
//! Test stages_subregs_contiguous with EXACT rational arithmetic.
//!
//! The original test-containment.rs uses f64, which can differ from Lean's
//! ℚ-based computation in floor() for fringe sizes. This test uses exact
//! rationals to match the Lean definitions precisely.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

/// Exact rational number (p/q with q > 0)
#[derive(Clone, Debug)]
struct Rat {
    p: i128,
    q: i128, // always > 0
}

impl Rat {
    fn new(p: i128, q: i128) -> Rat {
        assert!(q > 0);
        let g = gcd(p.unsigned_abs(), q.unsigned_abs()) as i128;
        Rat { p: p / g, q: q / g }
    }

    fn from_int(n: i128) -> Rat {
        Rat { p: n, q: 1 }
    }

    fn mul(&self, other: &Rat) -> Rat {
        Rat::new(self.p * other.p, self.q * other.q)
    }

    fn pow(&self, n: usize) -> Rat {
        let mut result = Rat::from_int(1);
        for _ in 0..n {
            result = result.mul(self);
        }
        result
    }

    /// Natural floor: max(0, floor(p/q))
    fn nat_floor(&self) -> usize {
        if self.p <= 0 {
            0
        } else {
            (self.p / self.q) as usize
        }
    }
}

fn gcd(a: u128, b: u128) -> u128 {
    if b == 0 { a } else { gcd(b, a % b) }
}

fn bag_size(k: usize, level: usize) -> usize {
    (1 << k) / (1 << level)
}

fn bag_lo(k: usize, level: usize, x: usize) -> usize {
    x * bag_size(k, level)
}

fn bag_hi(k: usize, level: usize, x: usize) -> usize {
    (x + 1) * bag_size(k, level)
}

type Bag = (usize, usize);
type Placement = BTreeMap<Bag, BTreeSet<usize>>;

fn capacity(k: usize, t: usize, level: usize, nu: &Rat, a: &Rat) -> Rat {
    let base = Rat::from_int(1i128 << k);
    base.mul(&nu.pow(t)).mul(&a.pow(level))
}

fn fringe(gamma: &Rat, k: usize, t: usize, level: usize, s: usize, a: &Rat, nu: &Rat) -> usize {
    if level == 0 {
        0
    } else if k <= level + 1 {
        s / 2
    } else {
        let cap = capacity(k, t, level, nu, a);
        gamma.mul(&cap).nat_floor()
    }
}

fn split(regs: &BTreeSet<usize>, f: usize) -> (BTreeSet<usize>, BTreeSet<usize>, BTreeSet<usize>) {
    let sorted: Vec<usize> = regs.iter().copied().collect();
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
    pl.insert((0, 0), (0..n).collect());
    pl
}

fn stage(pl: &Placement, k: usize, t: usize, gamma: &Rat, a: &Rat, nu: &Rat) -> Placement {
    let mut splits: BTreeMap<Bag, (BTreeSet<usize>, BTreeSet<usize>, BTreeSet<usize>)> = BTreeMap::new();

    for level in 0..=k {
        for x in 0..(1 << level) {
            let bag: Bag = (level, x);
            let regs = pl.get(&bag).cloned().unwrap_or_default();
            let s = regs.len();
            let f = fringe(gamma, k, t, level, s, a, nu);
            splits.insert(bag, split(&regs, f));
        }
    }

    let mut new_pl: Placement = BTreeMap::new();

    for level in 0..=k {
        for x in 0..(1usize << level) {
            let bag: Bag = (level, x);
            let mut wires = BTreeSet::new();

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

            if level == 0 {
                if let Some((tp, _, _)) = splits.get(&bag) {
                    wires.extend(tp);
                }
            } else {
                let parent: Bag = (level - 1, x / 2);
                if x % 2 == 0 {
                    if let Some((_, tl, _)) = splits.get(&parent) {
                        wires.extend(tl);
                    }
                } else {
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

fn main() {
    // Use exact rationals matching the Lean ℚ parameters
    let params: Vec<(Rat, Rat, Rat)> = vec![
        (Rat::new(1, 4), Rat::new(2, 1), Rat::new(4, 5)),   // 0.25, 2.0, 0.8
        (Rat::new(1, 2), Rat::new(2, 1), Rat::new(4, 5)),   // 0.5, 2.0, 0.8
        (Rat::new(1, 10), Rat::new(3, 1), Rat::new(9, 10)), // 0.1, 3.0, 0.9
        (Rat::new(3, 10), Rat::new(3, 2), Rat::new(7, 10)), // 0.3, 1.5, 0.7
    ];

    println!("--- Testing subtree containment when ancestor bags are empty (exact ℚ) ---");
    let mut empty_viol = 0;
    for k in 3..=10 {
        let finish_level = if k >= 2 { k - 2 } else { k };
        for (pi, (gamma, a, nu)) in params.iter().enumerate() {
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
                    let mut ok = true;
                    for x in 0..(1usize << finish_level) {
                        let lo = bag_lo(k, finish_level, x);
                        let hi = bag_hi(k, finish_level, x);
                        let sub = subregs(&pl, k, finish_level, x);
                        for &wire in &sub {
                            if wire < lo || wire >= hi {
                                if empty_viol < 10 {
                                    println!("VIOLATION: k={}, t={}, param_set={}", k, t+1, pi);
                                    println!("  wire {} in subregs(l={}, x={}) but interval [{}, {})",
                                        wire, finish_level, x, lo, hi);
                                }
                                ok = false;
                            }
                        }
                    }
                    if !ok {
                        empty_viol += 1;
                    }
                    break;
                }
            }
        }
    }
    if empty_viol == 0 {
        println!("ALL TESTS PASSED: subtree containment holds when ancestors are empty (exact ℚ)");
    } else {
        println!("FAILED: {} violations when ancestors are empty", empty_viol);
    }
}
