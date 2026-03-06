#!/usr/bin/env -S cargo +nightly -Zscript
//! Test: when alternating emptiness holds (as bagCard proves),
//! is the ordering property preserved within finish-level subtrees?
//!
//! Key insight: bagCard_odd_eq_zero proves that bags at wrong-parity
//! levels have 0 registers. So at any stage t, level l is empty if
//! (t + l) % 2 ≠ 0. Within a subtree rooted at the finish level,
//! this means every other level is empty.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

#[derive(Clone, Debug)]
struct Rat { p: i128, q: i128 }
impl Rat {
    fn new(p: i128, q: i128) -> Rat {
        assert!(q > 0);
        let g = gcd(p.unsigned_abs(), q.unsigned_abs()) as i128;
        Rat { p: p / g, q: q / g }
    }
    fn from_int(n: i128) -> Rat { Rat { p: n, q: 1 } }
    fn mul(&self, other: &Rat) -> Rat { Rat::new(self.p * other.p, self.q * other.q) }
    fn add(&self, other: &Rat) -> Rat { Rat::new(self.p * other.q + other.p * self.q, self.q * other.q) }
    fn pow(&self, n: usize) -> Rat {
        let mut r = Rat::from_int(1);
        for _ in 0..n { r = r.mul(self); }
        r
    }
    fn nat_floor(&self) -> usize {
        if self.p <= 0 { 0 } else { (self.p / self.q) as usize }
    }
    fn gt(&self, other: &Rat) -> bool { self.p * other.q > other.p * self.q }
    fn ge(&self, other: &Rat) -> bool { self.p * other.q >= other.p * self.q }
    fn lt_one(&self) -> bool { self.p < self.q }
    fn to_f64(&self) -> f64 { self.p as f64 / self.q as f64 }
}
fn gcd(a: u128, b: u128) -> u128 { if b == 0 { a } else { gcd(b, a % b) } }

type Bag = (usize, usize);
type Placement = BTreeMap<Bag, BTreeSet<usize>>;

fn capacity(k: usize, t: usize, level: usize, nu: &Rat, a: &Rat) -> Rat {
    Rat::from_int(1i128 << k).mul(&nu.pow(t)).mul(&a.pow(level))
}

fn fringe(gamma: &Rat, k: usize, t: usize, level: usize, s: usize, a: &Rat, nu: &Rat) -> usize {
    if level == 0 { 0 }
    else if k <= level + 1 { s / 2 }
    else { gamma.mul(&capacity(k, t, level, nu, a)).nat_floor() }
}

fn split(regs: &BTreeSet<usize>, f: usize) -> (BTreeSet<usize>, BTreeSet<usize>, BTreeSet<usize>) {
    let sorted: Vec<usize> = regs.iter().copied().collect();
    let s = sorted.len();
    let h = s / 2 - f.min(s / 2);
    let (mut tp, mut tl, mut tr) = (BTreeSet::new(), BTreeSet::new(), BTreeSet::new());
    for (j, &wire) in sorted.iter().enumerate() {
        if j < f || j >= f + 2 * h { tp.insert(wire); }
        else if j < f + h { tl.insert(wire); }
        else { tr.insert(wire); }
    }
    (tp, tl, tr)
}

fn start(k: usize) -> Placement {
    let mut pl = BTreeMap::new();
    pl.insert((0, 0), (0..(1 << k)).collect());
    pl
}

fn stage(pl: &Placement, k: usize, t: usize, gamma: &Rat, a: &Rat, nu: &Rat) -> Placement {
    let mut splits: BTreeMap<Bag, (BTreeSet<usize>, BTreeSet<usize>, BTreeSet<usize>)> = BTreeMap::new();
    for level in 0..=k {
        for x in 0..(1 << level) {
            let regs = pl.get(&(level, x)).cloned().unwrap_or_default();
            let s = regs.len();
            let f = fringe(gamma, k, t, level, s, a, nu);
            splits.insert((level, x), split(&regs, f));
        }
    }
    let mut new_pl: Placement = BTreeMap::new();
    for level in 0..=k {
        for x in 0..(1usize << level) {
            let mut wires = BTreeSet::new();
            if level < k {
                if let Some((tp, _, _)) = splits.get(&(level + 1, 2 * x)) { wires.extend(tp); }
                if let Some((tp, _, _)) = splits.get(&(level + 1, 2 * x + 1)) { wires.extend(tp); }
            }
            if level == 0 {
                if let Some((tp, _, _)) = splits.get(&(level, x)) { wires.extend(tp); }
            } else {
                let parent = (level - 1, x / 2);
                if x % 2 == 0 {
                    if let Some((_, tl, _)) = splits.get(&parent) { wires.extend(tl); }
                } else {
                    if let Some((_, _, tr)) = splits.get(&parent) { wires.extend(tr); }
                }
            }
            if !wires.is_empty() { new_pl.insert((level, x), wires); }
        }
    }
    new_pl
}

fn subregs(pl: &Placement, k: usize, level: usize, x: usize) -> BTreeSet<usize> {
    let mut result = pl.get(&(level, x)).cloned().unwrap_or_default();
    if level < k {
        result.extend(subregs(pl, k, level + 1, 2 * x));
        result.extend(subregs(pl, k, level + 1, 2 * x + 1));
    }
    result
}

/// Check alternating emptiness: bags at level l with (t+l)%2 != 0 should be empty
fn check_alternating_empty(pl: &Placement, k: usize, t: usize) -> bool {
    for level in 0..=k {
        if (t + 1 + level) % 2 != 0 {  // t+1 because we check AFTER stage t (0-indexed)
            for x in 0..(1usize << level) {
                let regs = pl.get(&(level, x)).cloned().unwrap_or_default();
                if !regs.is_empty() {
                    return false;
                }
            }
        }
    }
    true
}

/// Check ordering: for sibling bags, max(left subregs) < min(right subregs)
fn check_ordering(pl: &Placement, k: usize) -> bool {
    for level in 0..k {
        for x in 0..(1usize << level) {
            let left = subregs(pl, k, level + 1, 2 * x);
            let right = subregs(pl, k, level + 1, 2 * x + 1);
            if !left.is_empty() && !right.is_empty() {
                let max_left = *left.iter().next_back().unwrap();
                let min_right = *right.iter().next().unwrap();
                if max_left >= min_right {
                    return false;
                }
            }
        }
    }
    true
}

/// Check contiguity at finish level
fn check_contiguous(pl: &Placement, k: usize, finish_level: usize) -> bool {
    for x in 0..(1usize << finish_level) {
        let lo = x * ((1 << k) / (1 << finish_level));
        let hi = (x + 1) * ((1 << k) / (1 << finish_level));
        let sub = subregs(pl, k, finish_level, x);
        for &wire in &sub {
            if wire < lo || wire >= hi {
                return false;
            }
        }
    }
    true
}

fn main() {
    // Focus: does ordering hold at the exact moment ancestors become empty?
    // This is what stages_subregs_ordered claims (with hempty hypothesis).
    let params: Vec<(&str, Rat, Rat, Rat)> = vec![
        // Focus on the case that previously showed ordering violations
        ("A=3/2,g=3/10,v=7/10", Rat::new(3, 10), Rat::new(3, 2), Rat::new(7, 10)),
        ("A=2,g=1/4,v=4/5", Rat::new(1, 4), Rat::new(2, 1), Rat::new(4, 5)),
        ("A=2,g=1/2,v=4/5", Rat::new(1, 2), Rat::new(2, 1), Rat::new(4, 5)),
    ];

    println!("=== Does ordering hold when ancestors are empty? ===\n");

    for (name, gamma, a, nu) in &params {
        println!("--- {} ---", name);
        for k in 3..=9 {
            let finish_level = if k >= 2 { k - 2 } else { k };
            let num_stages = (5 * k).min(60);
            let mut pl = start(k);

            let mut found = false;
            for t in 0..num_stages {
                pl = stage(&pl, k, t, gamma, a, nu);

                // Check if ancestors are empty
                let mut ae = true;
                for level in 0..finish_level {
                    for x in 0..(1usize << level) {
                        if let Some(wires) = pl.get(&(level, x)) {
                            if !wires.is_empty() { ae = false; }
                        }
                    }
                }

                if ae {
                    let ordered = check_ordering(&pl, k);
                    let contiguous = check_contiguous(&pl, k, finish_level);
                    if ordered && contiguous {
                        println!("  k={} t={}: hempty holds, ordered=OK, contiguous=OK", k, t+1);
                    } else {
                        println!("  k={} t={}: hempty holds, ordered={}, contiguous={}",
                            k, t+1, ordered, contiguous);
                    }
                    found = true;
                    break;
                }
            }
            if !found {
                println!("  k={}: ancestors never empty in {} stages", k, num_stages);
            }
        }
        println!();
    }
}
