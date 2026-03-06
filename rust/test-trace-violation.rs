#!/usr/bin/env -S cargo +nightly -Zscript
//! Trace the exact mechanism of ordering violation.
//! Find the first violation and show the state before/after.

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

fn bag_size(k: usize, level: usize) -> usize { (1 << k) / (1 << level) }
fn bag_lo(k: usize, level: usize, x: usize) -> usize { x * bag_size(k, level) }
fn bag_hi(k: usize, level: usize, x: usize) -> usize { (x + 1) * bag_size(k, level) }

fn capacity(k: usize, t: usize, level: usize, nu: &Rat, a: &Rat) -> Rat {
    Rat::from_int(1i128 << k).mul(&nu.pow(t)).mul(&a.pow(level))
}

fn fringe_val(gamma: &Rat, k: usize, t: usize, level: usize, s: usize, a: &Rat, nu: &Rat) -> usize {
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

/// One stage, returning the splits for diagnostics
fn stage_with_splits(pl: &Placement, k: usize, t: usize, gamma: &Rat, a: &Rat, nu: &Rat)
    -> (Placement, BTreeMap<Bag, (BTreeSet<usize>, BTreeSet<usize>, BTreeSet<usize>)>)
{
    let mut splits: BTreeMap<Bag, (BTreeSet<usize>, BTreeSet<usize>, BTreeSet<usize>)> = BTreeMap::new();
    for level in 0..=k {
        for x in 0..(1 << level) {
            let regs = pl.get(&(level, x)).cloned().unwrap_or_default();
            let s = regs.len();
            let f = fringe_val(gamma, k, t, level, s, a, nu);
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
    (new_pl, splits)
}

fn subregs(pl: &Placement, k: usize, level: usize, x: usize) -> BTreeSet<usize> {
    let mut result = pl.get(&(level, x)).cloned().unwrap_or_default();
    if level < k {
        result.extend(subregs(pl, k, level + 1, 2 * x));
        result.extend(subregs(pl, k, level + 1, 2 * x + 1));
    }
    result
}

fn find_first_violation(pl: &Placement, k: usize) -> Option<(usize, usize)> {
    for level in 0..k {
        for x in 0..(1usize << level) {
            let left = subregs(pl, k, level + 1, 2 * x);
            let right = subregs(pl, k, level + 1, 2 * x + 1);
            if !left.is_empty() && !right.is_empty() {
                let max_left = *left.iter().next_back().unwrap();
                let min_right = *right.iter().next().unwrap();
                if max_left >= min_right {
                    return Some((level, x));
                }
            }
        }
    }
    None
}

fn print_subtree(pl: &Placement, k: usize, level: usize, x: usize, indent: usize) {
    let regs = pl.get(&(level, x)).cloned().unwrap_or_default();
    let sub = subregs(pl, k, level, x);
    let lo = bag_lo(k, level, x);
    let hi = bag_hi(k, level, x);
    let pad: String = " ".repeat(indent);
    if !sub.is_empty() {
        println!("{}bag({},{}) [{},{}) regs={:?} subregs={:?}",
            pad, level, x, lo, hi,
            regs.iter().collect::<Vec<_>>(),
            sub.iter().collect::<Vec<_>>());
    }
    if level < k {
        print_subtree(pl, k, level + 1, 2 * x, indent + 2);
        print_subtree(pl, k, level + 1, 2 * x + 1, indent + 2);
    }
}

fn main() {
    let gamma = Rat::new(3, 10);
    let a = Rat::new(3, 2);
    let nu = Rat::new(7, 10);

    // Try increasing k until we find a violation
    for k in 3..=7 {
        println!("\n========== k={} ==========", k);
        let mut pl = start(k);
        let mut prev_pl = pl.clone();

        for t in 0..30 {
            let (new_pl, splits) = stage_with_splits(&pl, k, t, &gamma, &a, &nu);

            if let Some((viol_level, viol_x)) = find_first_violation(&new_pl, k) {
                println!("\nFIRST VIOLATION at stage {} (after {} stages):", t + 1, t + 1);
                println!("bag({},{}) left/right ordering broken", viol_level, viol_x);

                let left = subregs(&new_pl, k, viol_level + 1, 2 * viol_x);
                let right = subregs(&new_pl, k, viol_level + 1, 2 * viol_x + 1);
                println!("  left subregs: {:?}", left.iter().collect::<Vec<_>>());
                println!("  right subregs: {:?}", right.iter().collect::<Vec<_>>());
                println!("  max(left)={}, min(right)={}",
                    left.iter().next_back().unwrap(), right.iter().next().unwrap());

                // Show the parent bag and its split
                let parent = (viol_level, viol_x);
                let parent_regs = pl.get(&parent).cloned().unwrap_or_default();
                let f = fringe_val(&gamma, k, t, viol_level, parent_regs.len(), &a, &nu);
                println!("\n  Parent bag({},{}) BEFORE split: {:?}",
                    viol_level, viol_x, parent_regs.iter().collect::<Vec<_>>());
                println!("  fringe={}, h={}", f, parent_regs.len() / 2 - f.min(parent_regs.len() / 2));

                if let Some((tp, tl, tr)) = splits.get(&parent) {
                    println!("  split → toParent={:?} toLeft={:?} toRight={:?}",
                        tp.iter().collect::<Vec<_>>(),
                        tl.iter().collect::<Vec<_>>(),
                        tr.iter().collect::<Vec<_>>());
                }

                // Show the subtree state before and after
                println!("\n  === BEFORE stage {} (subtree at ({},{})) ===", t + 1, viol_level, viol_x);
                print_subtree(&pl, k, viol_level, viol_x, 4);

                println!("\n  === AFTER stage {} (subtree at ({},{})) ===", t + 1, viol_level, viol_x);
                print_subtree(&new_pl, k, viol_level, viol_x, 4);

                // Show the grandparent's split too
                if viol_level > 0 {
                    let gp = (viol_level - 1, viol_x / 2);
                    let gp_regs = pl.get(&gp).cloned().unwrap_or_default();
                    let gp_f = fringe_val(&gamma, k, t, gp.0, gp_regs.len(), &a, &nu);
                    println!("\n  Grandparent bag({},{}) BEFORE split: {:?}",
                        gp.0, gp.1, gp_regs.iter().collect::<Vec<_>>());
                    println!("  fringe={}", gp_f);
                    if let Some((tp, tl, tr)) = splits.get(&gp) {
                        println!("  split → toParent={:?} toLeft={:?} toRight={:?}",
                            tp.iter().collect::<Vec<_>>(),
                            tl.iter().collect::<Vec<_>>(),
                            tr.iter().collect::<Vec<_>>());
                    }
                }

                break;
            }
            prev_pl = pl.clone();
            pl = new_pl;
        }
    }
}
