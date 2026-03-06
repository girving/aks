#!/usr/bin/env -S cargo +nightly -Zscript
//! Test ordering with actual Seiferas parameters (lambda=epsilon=1/99, A=10, nu=0.65).
//! Uses big integers to avoid overflow with A^level for large levels.
//! Focus: check ordering within subtrees at small k where we can still compute.

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
    fn try_mul(&self, other: &Rat) -> Option<Rat> {
        let p = self.p.checked_mul(other.p)?;
        let q = self.q.checked_mul(other.q)?;
        Some(Rat::new(p, q))
    }
    fn mul(&self, other: &Rat) -> Rat { self.try_mul(other).expect("overflow") }
    fn pow(&self, n: usize) -> Rat {
        let mut r = Rat::from_int(1);
        for _ in 0..n { r = r.mul(self); }
        r
    }
    fn try_pow(&self, n: usize) -> Option<Rat> {
        let mut r = Rat::from_int(1);
        for _ in 0..n { r = r.try_mul(self)?; }
        Some(r)
    }
    fn nat_floor(&self) -> usize {
        if self.p <= 0 { 0 } else { (self.p / self.q) as usize }
    }
    fn to_f64(&self) -> f64 { self.p as f64 / self.q as f64 }
}
fn gcd(a: u128, b: u128) -> u128 { if b == 0 { a } else { gcd(b, a % b) } }

type Bag = (usize, usize);
type Placement = BTreeMap<Bag, BTreeSet<usize>>;

fn capacity(k: usize, t: usize, level: usize, nu: &Rat, a: &Rat) -> Option<Rat> {
    let base = Rat::from_int(1i128 << k);
    let nu_t = nu.try_pow(t)?;
    let a_l = a.try_pow(level)?;
    base.try_mul(&nu_t)?.try_mul(&a_l)
}

fn fringe(gamma: &Rat, k: usize, t: usize, level: usize, s: usize, a: &Rat, nu: &Rat) -> usize {
    if level == 0 { 0 }
    else if k <= level + 1 { s / 2 }
    else {
        match capacity(k, t, level, nu, a) {
            Some(cap) => match gamma.try_mul(&cap) {
                Some(gc) => gc.nat_floor(),
                None => s  // overflow in gamma*cap → fringe = s (all go to parent)
            },
            None => s  // overflow → fringe = s
        }
    }
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

fn total_wires(pl: &Placement) -> usize {
    pl.values().map(|s| s.len()).sum()
}

fn main() {
    // Seiferas parameters: lambda = epsilon = 1/99, A = 10, nu = 0.65 = 13/20
    let gamma = Rat::new(1, 99);
    let a = Rat::new(10, 1);
    let nu = Rat::new(13, 20);

    println!("=== Seiferas parameters: gamma=1/99, A=10, nu=13/20 ===");
    println!("gamma*A^2 = {:.4}", gamma.mul(&a.pow(2)).to_f64());
    println!("gamma*A = {:.4}\n", gamma.mul(&a).to_f64());

    for k in 3..=10 {
        let finish_level = k - 2;
        let num_stages = (5 * k).min(80);
        let mut pl = start(k);
        let n = 1 << k;

        let mut ordering_ok = true;
        let mut ancestors_empty_at = None;
        let mut first_ord_fail = None;

        for t in 0..num_stages {
            pl = stage(&pl, k, t, &gamma, &a, &nu);

            // Total wires should always be n
            let tw = total_wires(&pl);
            if tw != n {
                println!("  BUG: k={} t={} total_wires={} != {}", k, t+1, tw, n);
                break;
            }

            if !check_ordering(&pl, k) {
                ordering_ok = false;
                if first_ord_fail.is_none() {
                    first_ord_fail = Some(t + 1);
                }
            }

            if ancestors_empty_at.is_none() {
                let mut ae = true;
                for level in 0..finish_level {
                    for x in 0..(1usize << level) {
                        if let Some(wires) = pl.get(&(level, x)) {
                            if !wires.is_empty() { ae = false; }
                        }
                    }
                }
                if ae { ancestors_empty_at = Some(t + 1); }
            }
        }

        // Show bag sizes at last stage
        let mut level_sizes: Vec<usize> = Vec::new();
        for level in 0..=k {
            let total: usize = (0..(1usize << level))
                .map(|x| pl.get(&(level, x)).map_or(0, |s| s.len()))
                .sum();
            level_sizes.push(total);
        }

        let ord_str = if ordering_ok { "OK".to_string() } else { format!("FAIL@t={}", first_ord_fail.unwrap()) };
        let ae_str = ancestors_empty_at.map_or("never".to_string(), |t| format!("t={}", t));
        println!("k={}: ord={}, ancestors_empty={}, level_sizes={:?}",
            k, ord_str, ae_str, level_sizes);
    }
}
