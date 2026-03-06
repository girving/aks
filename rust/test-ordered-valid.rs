#!/usr/bin/env -S cargo +nightly -Zscript
//! Test ordering with parameters satisfying seiferasNetwork_sorts constraints.
//! hA2: gamma*A^2 > 1, hC3: nu >= 4*gamma*A + 5/(2A), hgamma <= 1/2, nu < 1, A > 1

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
                eprintln!("  ORDER VIOLATION: subregs(x={}) max={} >= subregs(x={}) min={}",
                    x, max1, x + 1, min2);
                ok = false;
            }
        }
    }
    ok
}

fn check_contiguous(pl: &Placement, k: usize, finish_level: usize) -> bool {
    let mut ok = true;
    for x in 0..(1usize << finish_level) {
        let lo = x * ((1 << k) / (1 << finish_level));
        let hi = (x + 1) * ((1 << k) / (1 << finish_level));
        let sub = subregs(pl, k, finish_level, x);
        for &wire in &sub {
            if wire < lo || wire >= hi {
                ok = false;
            }
        }
    }
    ok
}

fn main() {
    // Valid parameter sets satisfying hA2 and hC3
    // A=8: gamma=9/512, nu=113/128 (=0.8828125)
    // A=10: gamma=11/1000, nu=7/10
    // A=15: gamma=71/15000, nu=46/100
    // Also test some with larger gamma (closer to limit)
    let valid_params: Vec<(&str, Rat, Rat, Rat)> = vec![
        ("A=8,g=9/512,v=113/128", Rat::new(9, 512), Rat::new(8, 1), Rat::new(113, 128)),
        ("A=10,g=11/1000,v=7/10", Rat::new(11, 1000), Rat::new(10, 1), Rat::new(7, 10)),
        ("A=10,g=12/1000,v=73/100", Rat::new(12, 1000), Rat::new(10, 1), Rat::new(73, 100)),
        ("A=15,g=5/1000,v=5/10", Rat::new(5, 1000), Rat::new(15, 1), Rat::new(5, 10)),
        ("A=20,g=3/1000,v=4/10", Rat::new(3, 1000), Rat::new(20, 1), Rat::new(4, 10)),
        // Also test the previously-passing sets
        ("A=2,g=1/4,v=4/5", Rat::new(1, 4), Rat::new(2, 1), Rat::new(4, 5)),
        ("A=2,g=1/2,v=4/5", Rat::new(1, 2), Rat::new(2, 1), Rat::new(4, 5)),
        ("A=3,g=1/10,v=9/10", Rat::new(1, 10), Rat::new(3, 1), Rat::new(9, 10)),
        // The failing set for reference
        ("A=3/2,g=3/10,v=7/10 [FAILS]", Rat::new(3, 10), Rat::new(3, 2), Rat::new(7, 10)),
    ];

    for (name, gamma, a, nu) in &valid_params {
        let ga2 = gamma.mul(&a.pow(2));
        let rhs = Rat::from_int(4).mul(gamma).mul(a).add(&Rat::new(5, 1).mul(&Rat::new(1, 2 * a.p)));
        let hA2_ok = ga2.gt(&Rat::from_int(1));
        let hC3_ok = nu.ge(&rhs);
        let valid = hA2_ok && hC3_ok && nu.lt_one();

        println!("\n{} [hA2={}, hC3={}, valid={}]", name, hA2_ok, hC3_ok, valid);
        println!("  gamma*A^2={:.4}, hC3_rhs={:.4}", ga2.to_f64(), rhs.to_f64());

        for k in 3..=12 {
            let finish_level = if k >= 2 { k - 2 } else { k };
            let num_stages = (3 * k).min(40);
            let mut pl = start(k);
            let mut found = false;
            for t in 0..num_stages {
                pl = stage(&pl, k, t, gamma, a, nu);
                let mut ancestors_empty = true;
                for level in 0..finish_level {
                    for x in 0..(1usize << level) {
                        if let Some(wires) = pl.get(&(level, x)) {
                            if !wires.is_empty() { ancestors_empty = false; }
                        }
                    }
                }
                if ancestors_empty {
                    let ordered = check_finish_ordered(&pl, k, finish_level);
                    let contiguous = check_contiguous(&pl, k, finish_level);
                    if !ordered || !contiguous {
                        println!("  k={}: t={} ordered={} contiguous={}", k, t+1, ordered, contiguous);
                    }
                    found = true;
                    break;
                }
            }
            if !found {
                println!("  k={}: ancestors never empty in {} stages", k, num_stages);
            }
        }
    }
}
