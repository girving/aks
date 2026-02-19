#!/usr/bin/env -S cargo +nightly -Zscript
//! Diagnostic 2: Per-chunk error analysis for error_set_bound proof.
//! For each chunk c at level l, computes:
//!   error_c = actual error count (top-target val<k going to bottom sub-half)
//!   j_c = top-target values with val < k in chunk
//!   f_c = foreign-below values with val < k in chunk
//!   k_c = all values < k in chunk
//! Checks which per-chunk bound holds: ε*j_c, ε*(f_c+j_c), ε*k_c, ε*hs

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
    let configs = vec![(64, 6), (128, 6), (256, 8)];
    let trials = 3000;

    for &(n, deg) in &configs {
        let hf = |hm: usize| -> ComparatorNetwork {
            synthetic_halver(hm, deg, 42 + hm as u64 * 1000 + deg as u64)
        };
        // Compute ε for this halver family
        let mut max_eps = 0.0f64;
        let mut test_rng = Rng::new(99999 + n as u64);
        for m in [4usize, 8, 16, 32, 64, 128, 256] {
            if 2 * m > n { break; }
            let halver = synthetic_halver(m, deg, 42 + m as u64 * 1000 + deg as u64);
            for _ in 0..500 {
                let perm = test_rng.perm(2 * m);
                let mut out = perm.clone();
                halver.exec(&mut out);
                let inv_out = invert(&out);
                for j in 1..=m {
                    let count = (0..2*m).filter(|&pos| pos >= m && inv_out[out[pos]] >= m && {
                        // rank of out[pos] among all 2m values = out[pos] since input is perm of 0..2m
                        // Wait, rank in Fin(2m) = value itself for a perm of 0..2m-1
                        out[pos] < j
                    }).count();
                    // Actually for perm input: rank(out[pos]) = out[pos] for Fin
                    // EIH: |{pos >= m : rank(out[pos]) < j}| <= eps * j
                    let count2 = (m..2*m).filter(|&pos| out[pos] < j).count();
                    let ratio = count2 as f64 / j as f64;
                    if ratio > max_eps { max_eps = ratio; }
                }
            }
        }
        let eps = max_eps;
        println!("n={n}, deg={deg}, ε={eps:.4}");

        let mut rng = Rng::new(12345 + n as u64);

        // Track violations of various per-chunk bounds
        let mut viol_eps_jc = 0u64;      // error_c > ε * j_c
        let mut viol_eps_fc_jc = 0u64;   // error_c > ε * (f_c + j_c)
        let mut viol_eps_kc = 0u64;      // error_c > ε * k_c
        let mut viol_eps_hs = 0u64;      // error_c > ε * hs
        let mut total_active = 0u64;
        let mut overflow_active = 0u64;  // chunks with f_c + j_c > hs AND error_c > 0
        let mut worst_ratio_jc = 0.0f64;
        let mut worst_ratio_fc_jc = 0.0f64;

        for depth in 1..=6 {
            if n % (1 << depth) != 0 { continue; }
            for _ in 0..trials {
                let input = rng.perm(n);
                for l in 0..depth {
                    if n % (1 << (l + 1)) != 0 { continue; }
                    let cs = n / (1 << l);
                    let hs = cs / 2;
                    if hs == 0 { continue; }
                    let num_chunks = 1 << l;

                    // Compute w_l and w_{l+1}
                    let out_l = {
                        let net = halver_network(n, &hf, l);
                        let mut o = input.clone(); net.exec(&mut o); o
                    };
                    let out_l1 = {
                        let net = halver_network(n, &hf, l + 1);
                        let mut o = input.clone(); net.exec(&mut o); o
                    };
                    let inv_l = invert(&out_l);
                    let inv_l1 = invert(&out_l1);

                    for k_frac in &[0.1, 0.25, 0.5, 0.75, 0.9] {
                        let k = ((*k_frac) * n as f64).round() as usize;
                        if k == 0 || k > n { continue; }

                        for c in 0..num_chunks {
                            let chunk_start = c * cs;
                            if chunk_start >= k { continue; } // no top-target with val < k

                            // Compute f_c, j_c, k_c, error_c
                            let mut f_c = 0usize;  // foreign-below with val < k
                            let mut j_c = 0usize;  // top-target with val < k
                            let mut k_c = 0usize;  // all values < k in chunk
                            let mut error_c = 0usize;

                            for a in 0..k {
                                let pos_l = inv_l[a];
                                if pos_l / cs != c { continue; }
                                k_c += 1;
                                if a < chunk_start {
                                    f_c += 1;
                                } else if a < chunk_start + hs {
                                    j_c += 1;
                                    // Check if this value goes to bottom sub-half
                                    let pos_l1 = inv_l1[a];
                                    let hs_l1 = hs; // cs_{l+1} = hs, half of that = hs/2
                                    // sub-chunk at level l+1: pos / (n/2^{l+1})
                                    // = pos / hs
                                    // target sub-chunk: a / hs
                                    // Error if pos_l1 / hs > a / hs
                                    if pos_l1 / hs > a / hs {
                                        error_c += 1;
                                    }
                                }
                            }

                            if j_c == 0 { continue; }
                            total_active += 1;

                            let fc_jc = f_c + j_c;
                            if fc_jc > hs && error_c > 0 {
                                overflow_active += 1;
                            }

                            // Check bounds
                            let bound_jc = eps * j_c as f64;
                            let bound_fc_jc = eps * fc_jc as f64;
                            let bound_kc = eps * k_c as f64;
                            let bound_hs = eps * hs as f64;

                            if error_c as f64 > bound_jc { viol_eps_jc += 1; }
                            if error_c as f64 > bound_fc_jc { viol_eps_fc_jc += 1; }
                            if error_c as f64 > bound_kc { viol_eps_kc += 1; }
                            if error_c as f64 > bound_hs { viol_eps_hs += 1; }

                            if j_c > 0 {
                                let ratio = error_c as f64 / j_c as f64;
                                if ratio > worst_ratio_jc { worst_ratio_jc = ratio; }
                            }
                            if fc_jc > 0 {
                                let ratio = error_c as f64 / fc_jc as f64;
                                if ratio > worst_ratio_fc_jc { worst_ratio_fc_jc = ratio; }
                            }
                        }
                    }
                }
            }
        }
        println!("  total_active={total_active}, overflow_active={overflow_active}");
        println!("  viol ε*j_c:     {viol_eps_jc}/{total_active}");
        println!("  viol ε*(f+j):   {viol_eps_fc_jc}/{total_active}");
        println!("  viol ε*k_c:     {viol_eps_kc}/{total_active}");
        println!("  viol ε*hs:      {viol_eps_hs}/{total_active}");
        println!("  worst error/j_c:     {worst_ratio_jc:.4} (ε={eps:.4})");
        println!("  worst error/(f+j):   {worst_ratio_fc_jc:.4} (ε={eps:.4})");
        println!();
    }
}
