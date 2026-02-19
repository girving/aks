#!/usr/bin/env -S cargo +nightly -Zscript
//! Diagnostic 3: Check if total error ≤ ε * Σ min(f_c+j_c, hs) always holds,
//! and whether the rank ≥ hs error elements are bounded by something useful.

#[derive(Clone, Copy)]
struct Comparator { i: usize, j: usize }
struct ComparatorNetwork { comparators: Vec<Comparator> }
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
    ComparatorNetwork { comparators: comps }
}

fn halver_network(n: usize, hf: &dyn Fn(usize) -> ComparatorNetwork, depth: usize) -> ComparatorNetwork {
    let mut comps = Vec::new();
    for l in 0..depth { comps.extend(halver_at_level(n, hf, l).comparators); }
    ComparatorNetwork { comparators: comps }
}

fn synthetic_halver(m: usize, d: usize, seed: u64) -> ComparatorNetwork {
    if m == 0 { return ComparatorNetwork { comparators: vec![] }; }
    let mut rng = seed;
    let mut rn = || -> usize { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; rng as usize };
    let mut comps = Vec::with_capacity(m * d);
    for _p in 0..d {
        let mut perm: Vec<usize> = (0..m).collect();
        for i in (1..m).rev() { let j = rn() % (i + 1); perm.swap(i, j); }
        for v in 0..m { comps.push(Comparator { i: v, j: m + perm[v] }); }
    }
    ComparatorNetwork { comparators: comps }
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
        // Compute ε
        let mut max_eps = 0.0f64;
        let mut test_rng = Rng::new(99999 + n as u64);
        for m in [4usize, 8, 16, 32, 64, 128, 256] {
            if 2 * m > n { break; }
            let halver = synthetic_halver(m, deg, 42 + m as u64 * 1000 + deg as u64);
            for _ in 0..500 {
                let perm = test_rng.perm(2 * m);
                let mut out = perm.clone();
                halver.exec(&mut out);
                for j in 1..=m {
                    let count = (m..2*m).filter(|&pos| out[pos] < j).count();
                    let ratio = count as f64 / j as f64;
                    if ratio > max_eps { max_eps = ratio; }
                }
            }
        }
        let eps = max_eps;
        println!("n={n}, deg={deg}, ε={eps:.4}");

        let mut rng = Rng::new(12345 + n as u64);
        let mut viol_sum = 0u64;
        let mut total_tests = 0u64;
        let mut max_excess = 0.0f64; // max(total_error - ε * Σ min(f+j, hs))

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

                    for k_frac in &[0.05, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0] {
                        let k = ((*k_frac) * n as f64).round() as usize;
                        if k == 0 || k > n { continue; }
                        total_tests += 1;

                        let mut total_error = 0usize;
                        let mut sum_min_fc_jc_hs = 0usize;
                        let mut sum_fc_jc = 0usize;
                        let mut rank_ge_hs_errors = 0usize;

                        for c in 0..num_chunks {
                            let chunk_start = c * cs;
                            let mut f_c = 0usize;
                            let mut j_c = 0usize;
                            let mut error_c = 0usize;
                            let mut rank_ge_hs_err_c = 0usize;

                            // Collect all values in chunk c at level l
                            let chunk_vals: Vec<usize> = (chunk_start..chunk_start+cs)
                                .filter(|&pos| pos < n)
                                .map(|pos| out_l[pos])
                                .collect();

                            for a in 0..k {
                                let pos_l = inv_l[a];
                                if pos_l / cs != c { continue; }
                                if a < chunk_start {
                                    f_c += 1;
                                } else if a < chunk_start + hs {
                                    j_c += 1;
                                    // Check error
                                    let pos_l1 = inv_l1[a];
                                    if pos_l1 / hs > a / hs {
                                        error_c += 1;
                                        // Compute local rank of value a
                                        let local_rank = chunk_vals.iter()
                                            .filter(|&&v| v < a).count();
                                        if local_rank >= hs {
                                            rank_ge_hs_err_c += 1;
                                        }
                                    }
                                }
                            }

                            total_error += error_c;
                            rank_ge_hs_errors += rank_ge_hs_err_c;
                            let fc_jc = f_c + j_c;
                            sum_fc_jc += fc_jc;
                            sum_min_fc_jc_hs += fc_jc.min(hs);
                        }

                        let bound1 = eps * sum_min_fc_jc_hs as f64;
                        let bound2 = eps * k as f64;
                        let excess = total_error as f64 - bound1;

                        if excess > max_excess {
                            max_excess = excess;
                        }
                        if total_error as f64 > bound2 + 0.001 {
                            viol_sum += 1;
                            if viol_sum <= 3 {
                                println!("  VIOLATION: l={l}, k={k}, error={total_error}, ε*k={:.2}, sum_fc_jc={sum_fc_jc}", bound2);
                            }
                        }

                        // Check: total_error ≤ ε * sum_fc_jc (when all fc+jc ≤ hs)
                        // More importantly: total rank≥hs errors
                        if rank_ge_hs_errors > 0 && total_tests % 50000 == 0 {
                            println!("  sample: l={l}, k={k}, error={total_error}, rank≥hs_err={rank_ge_hs_errors}, ε*k={:.1}, sum_min={sum_min_fc_jc_hs}, sum_fj={sum_fc_jc}", bound2);
                        }
                    }
                }
            }
        }
        println!("  violations of ε*k: {viol_sum}/{total_tests}");
        println!("  max(error - ε*Σmin(f+j,hs)): {max_excess:.2}");
        println!();
    }
}
