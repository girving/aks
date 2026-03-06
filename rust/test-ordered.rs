#!/usr/bin/env -S cargo +nightly -Zscript
//! Test whether subregs are ORDERED (left < right) even when not contiguous.
//! Uses exact rational arithmetic to match Lean's ℚ-based computation.

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
    fn pow(&self, n: usize) -> Rat {
        let mut r = Rat::from_int(1);
        for _ in 0..n { r = r.mul(self); }
        r
    }
    fn nat_floor(&self) -> usize {
        if self.p <= 0 { 0 } else { (self.p / self.q) as usize }
    }
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

/// Check: for every internal bag, max(left subregs) < min(right subregs)
fn check_ordered(pl: &Placement, k: usize, check_level: usize) -> bool {
    let mut ok = true;
    // Check at all levels from check_level down to k-1
    for level in check_level..k {
        for x in 0..(1usize << level) {
            let left = subregs(pl, k, level + 1, 2 * x);
            let right = subregs(pl, k, level + 1, 2 * x + 1);
            if !left.is_empty() && !right.is_empty() {
                let max_left = *left.iter().next_back().unwrap();
                let min_right = *right.iter().next().unwrap();
                if max_left >= min_right {
                    eprintln!(
                        "ORDER VIOLATION: bag(l={},x={}): max(left subregs)={} >= min(right subregs)={}",
                        level, x, max_left, min_right
                    );
                    ok = false;
                }
            }
        }
    }
    ok
}

/// Also check: at the finish level, bags ordered by x have ordered subregs
fn check_finish_ordered(pl: &Placement, k: usize, finish_level: usize) -> bool {
    let mut ok = true;
    let num_bags = 1usize << finish_level;
    for x in 0..num_bags - 1 {
        let s1 = subregs(pl, k, finish_level, x);
        let s2 = subregs(pl, k, finish_level, x + 1);
        if !s1.is_empty() && !s2.is_empty() {
            let max1 = *s1.iter().next_back().unwrap();
            let min2 = *s2.iter().next().unwrap();
            if max1 >= min2 {
                eprintln!(
                    "FINISH ORDER VIOLATION: subregs(l={},x={}) max={} >= subregs(l={},x={}) min={}",
                    finish_level, x, max1, finish_level, x + 1, min2
                );
                ok = false;
            }
        }
    }
    ok
}

fn main() {
    let params: Vec<(Rat, Rat, Rat)> = vec![
        (Rat::new(1, 4), Rat::new(2, 1), Rat::new(4, 5)),
        (Rat::new(1, 2), Rat::new(2, 1), Rat::new(4, 5)),
        (Rat::new(1, 10), Rat::new(3, 1), Rat::new(9, 10)),
        (Rat::new(3, 10), Rat::new(3, 2), Rat::new(7, 10)),
    ];

    println!("--- Testing left/right ordering when ancestors empty (exact ℚ) ---");
    let mut viol_count = 0;
    for k in 3..=10 {
        let finish_level = if k >= 2 { k - 2 } else { k };
        for (pi, (gamma, a, nu)) in params.iter().enumerate() {
            let num_stages = (3 * k).min(30);
            let mut pl = start(k);
            for t in 0..num_stages {
                pl = stage(&pl, k, t, gamma, a, nu);
                // Check ancestors empty
                let mut ancestors_empty = true;
                for level in 0..finish_level {
                    for x in 0..(1usize << level) {
                        if let Some(wires) = pl.get(&(level, x)) {
                            if !wires.is_empty() { ancestors_empty = false; }
                        }
                    }
                }
                if ancestors_empty {
                    if !check_ordered(&pl, k, finish_level) {
                        eprintln!("  at k={}, t={}, param_set={}", k, t + 1, pi);
                        viol_count += 1;
                    }
                    if !check_finish_ordered(&pl, k, finish_level) {
                        eprintln!("  FINISH at k={}, t={}, param_set={}", k, t + 1, pi);
                        viol_count += 1;
                    }
                    break;
                }
            }
        }
    }
    if viol_count == 0 {
        println!("ALL TESTS PASSED: left/right ordering holds when ancestors empty");
    } else {
        println!("FAILED: {} violations", viol_count);
    }

    // Also test ordering at ALL stages (not just when ancestors empty)
    println!("\n--- Testing left/right ordering at ALL stages ---");
    let mut all_viol = 0;
    for k in 3..=8 {
        let finish_level = if k >= 2 { k - 2 } else { k };
        for (pi, (gamma, a, nu)) in params.iter().enumerate() {
            let num_stages = (3 * k).min(20);
            let mut pl = start(k);
            for t in 0..num_stages {
                pl = stage(&pl, k, t, gamma, a, nu);
                // Check ordering at ALL levels (0..k)
                for level in 0..k {
                    for x in 0..(1usize << level) {
                        let left = subregs(&pl, k, level + 1, 2 * x);
                        let right = subregs(&pl, k, level + 1, 2 * x + 1);
                        if !left.is_empty() && !right.is_empty() {
                            let max_left = *left.iter().next_back().unwrap();
                            let min_right = *right.iter().next().unwrap();
                            if max_left >= min_right {
                                if all_viol < 5 {
                                    eprintln!(
                                        "ALL-STAGES VIOLATION: k={}, t={}, p={}: bag(l={},x={}): max(L)={} >= min(R)={}",
                                        k, t + 1, pi, level, x, max_left, min_right
                                    );
                                }
                                all_viol += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    if all_viol == 0 {
        println!("ALL TESTS PASSED: left/right ordering holds at all stages, all levels");
    } else {
        println!("FAILED: {} violations at various stages", all_viol);
    }
}
