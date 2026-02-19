#!/usr/bin/env -S cargo +nightly -Zscript
//! Diagnostic: check whether f_c + t_c ≤ hs always holds for reachable states
//! (where f_c = foreign-below values in chunk, t_c = top-target values < k in chunk,
//!  hs = half-chunk size).
//! If this holds, error_set_bound has a clean per-chunk proof.
//! If not, a more sophisticated argument is needed.

#[derive(Clone, Copy)]
struct Comparator { i: usize, j: usize }
struct ComparatorNetwork { n: usize, comparators: Vec<Comparator> }
impl ComparatorNetwork {
    fn exec(&self, v: &mut [usize]) {
        for c in &self.comparators { if v[c.i] > v[c.j] { v.swap(c.i, c.j); } }
    }
}

fn halver_at_level(n: usize, halver_fn: &dyn Fn(usize) -> ComparatorNetwork, level: usize) -> ComparatorNetwork {
    let cs = n / (1 << level);
    let hs = cs / 2;
    let nc = 1 << level;
    let mut comps = Vec::new();
    for k in 0..nc {
        let off = k * cs;
        if off + 2 * hs <= n {
            let h = halver_fn(hs);
            for c in &h.comparators { comps.push(Comparator { i: off + c.i, j: off + c.j }); }
        }
    }
    ComparatorNetwork { n, comparators: comps }
}

fn halver_network(n: usize, hf: &dyn Fn(usize) -> ComparatorNetwork, depth: usize) -> ComparatorNetwork {
    let mut comps = Vec::new();
    for l in 0..depth { comps.extend(halver_at_level(n, hf, l).comparators); }
    ComparatorNetwork { n, comparators: comps }
}

fn synthetic_halver(m: usize, d: usize, seed: u64) -> ComparatorNetwork {
    if m == 0 { return ComparatorNetwork { n: 0, comparators: vec![] }; }
    let mut rng = seed;
    let mut rn = || -> usize { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; rng as usize };
    let mut comps = Vec::with_capacity(m * d);
    for _p in 0..d {
        let mut perm: Vec<usize> = (0..m).collect();
        for i in (1..m).rev() { let j = rn() % (i + 1); perm.swap(i, j); }
        for v in 0..m { comps.push(Comparator { i: v, j: m + perm[v] }); }
    }
    ComparatorNetwork { n: 2 * m, comparators: comps }
}

struct Rng(u64);
impl Rng {
    fn new(s: u64) -> Self { Rng(s) }
    fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 }
    fn perm(&mut self, n: usize) -> Vec<usize> {
        let mut p: Vec<usize> = (0..n).collect();
        for i in (1..n).rev() { let j = (self.next() as usize) % (i + 1); p.swap(i, j); }
        p
    }
}

fn invert(out: &[usize]) -> Vec<usize> {
    let mut inv = vec![0; out.len()];
    for (p, &v) in out.iter().enumerate() { inv[v] = p; }
    inv
}

fn main() {
    let configs = vec![(64, 6), (128, 6), (256, 8), (512, 8)];
    let trials = 2000;

    for &(n, deg) in &configs {
        let hf = |hm: usize| -> ComparatorNetwork {
            synthetic_halver(hm, deg, 42 + hm as u64 * 1000 + deg as u64)
        };
        let mut rng = Rng::new(12345 + n as u64);
        let mut max_overflow = 0i64; // max(f_c + t_c - hs) across all chunks/levels/inputs
        let mut overflow_count = 0u64;
        let mut total_chunks = 0u64;

        for depth in 1..=8 {
            if n % (1 << depth) != 0 { continue; }
            for _ in 0..trials {
                let input = rng.perm(n);
                for l in 0..depth {
                    if n % (1 << (l + 1)) != 0 { continue; }
                    let out_l = {
                        let net = halver_network(n, &hf, l);
                        let mut o = input.clone(); net.exec(&mut o); o
                    };
                    let inv_l = invert(&out_l);
                    let cs = n / (1 << l);
                    let hs = cs / 2;
                    if hs == 0 { continue; }
                    let num_chunks = 1 << l;

                    for k_frac in &[0.1, 0.25, 0.5, 0.75, 1.0] {
                        let k = ((*k_frac) * n as f64).round() as usize;
                        if k == 0 || k > n { continue; }

                        for c in 0..num_chunks {
                            let chunk_start = c * cs;
                            // f_c = foreign-below values in chunk c: val < chunk_start, pos in chunk c
                            // t_c = top-target values < k in chunk c: chunk_start ≤ val < chunk_start + hs, val < k, pos in chunk c
                            let mut f_c = 0usize;
                            let mut t_c = 0usize;
                            for a in 0..k {
                                let pos = inv_l[a];
                                if pos / cs != c { continue; } // not in this chunk
                                if a < chunk_start {
                                    f_c += 1;
                                } else if a < chunk_start + hs {
                                    t_c += 1;
                                }
                                // values in [chunk_start + hs, k) are bottom-target, not counted
                            }
                            total_chunks += 1;
                            let overflow = (f_c + t_c) as i64 - hs as i64;
                            if overflow > 0 {
                                overflow_count += 1;
                            }
                            if overflow > max_overflow {
                                max_overflow = overflow;
                                if overflow_count <= 5 {
                                    println!("  OVERFLOW: n={n}, depth={depth}, l={l}, c={c}, k={k}, f_c={f_c}, t_c={t_c}, hs={hs}, overflow={overflow}");
                                }
                            }
                        }
                    }
                }
            }
        }
        println!("n={n}: overflow_count={overflow_count}/{total_chunks}, max_overflow={max_overflow}");
    }
}
