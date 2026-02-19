#!/usr/bin/env -S cargo +nightly -Zscript
//! Test nearsort sorry's: error_set_bound, farSmallCount_depth_bound,
//! halverNetwork_initialNearsorted, halverNetwork_finalNearsorted
//!
//! Tests the sorry'd lemmas in AKS/Nearsort/Correctness.lean:
//! 1. error_set_bound: |E_l| ≤ ε * k (per-level error set bound)
//! 2. error_set_bound_dual: |E_l_dual| ≤ ε * k
//! 3. farSmallCount_depth_bound: farSmallCount ≤ ε * depth * k (aggregate)
//! 4. halverNetwork_initialNearsorted: InitialNearsorted property
//! 5. halverNetwork_finalNearsorted: FinalNearsorted property
//!
//! Usage: cargo +nightly -Zscript rust/test-nearsort.rs

// ──────────────────────────────────────────────────────────
// Core types (same as test-separator.rs)
// ──────────────────────────────────────────────────────────

#[derive(Clone, Copy)]
struct Comparator {
    i: usize,
    j: usize,
}

struct ComparatorNetwork {
    n: usize,
    comparators: Vec<Comparator>,
}

impl ComparatorNetwork {
    fn exec(&self, v: &mut [usize]) {
        for c in &self.comparators {
            if v[c.i] > v[c.j] {
                v.swap(c.i, c.j);
            }
        }
    }
}

// ──────────────────────────────────────────────────────────
// halverAtLevel and halverNetwork
// Matches AKS/Nearsort/Construction.lean exactly
// ──────────────────────────────────────────────────────────

fn halver_at_level(
    n: usize,
    halver_fn: &dyn Fn(usize) -> ComparatorNetwork,
    level: usize,
) -> ComparatorNetwork {
    let chunk_size = n / (1 << level);
    let half_chunk = chunk_size / 2;
    let num_chunks = 1 << level;
    let mut comparators = Vec::new();
    for k in 0..num_chunks {
        let offset = k * chunk_size;
        if offset + 2 * half_chunk <= n {
            let halver = halver_fn(half_chunk);
            for c in &halver.comparators {
                comparators.push(Comparator {
                    i: offset + c.i,
                    j: offset + c.j,
                });
            }
        }
    }
    ComparatorNetwork { n, comparators }
}

fn halver_network(
    n: usize,
    halver_fn: &dyn Fn(usize) -> ComparatorNetwork,
    depth: usize,
) -> ComparatorNetwork {
    let mut comparators = Vec::new();
    for l in 0..depth {
        let level_net = halver_at_level(n, halver_fn, l);
        comparators.extend(level_net.comparators);
    }
    ComparatorNetwork { n, comparators }
}

/// Partial halver network: levels 0..depth (not including depth).
/// This is halverNetwork(n, halvers, depth).exec(v).
fn halver_network_output(
    n: usize,
    halver_fn: &dyn Fn(usize) -> ComparatorNetwork,
    depth: usize,
    input: &[usize],
) -> Vec<usize> {
    let net = halver_network(n, halver_fn, depth);
    let mut out = input.to_vec();
    net.exec(&mut out);
    out
}

// ──────────────────────────────────────────────────────────
// Synthetic halver (random d-regular bipartite graph)
// Same as test-separator.rs
// ──────────────────────────────────────────────────────────

fn synthetic_halver(m: usize, d: usize, seed: u64) -> ComparatorNetwork {
    if m == 0 {
        return ComparatorNetwork {
            n: 0,
            comparators: vec![],
        };
    }
    let mut rng = seed;
    let mut rand_next = || -> usize {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng as usize
    };

    let mut comparators = Vec::with_capacity(m * d);
    for p in 0..d {
        // Random perfect matching
        let mut perm: Vec<usize> = (0..m).collect();
        for i in (1..m).rev() {
            let j = rand_next() % (i + 1);
            perm.swap(i, j);
        }
        for v in 0..m {
            comparators.push(Comparator {
                i: v,
                j: m + perm[v],
            });
        }
    }
    ComparatorNetwork {
        n: 2 * m,
        comparators,
    }
}

/// Measure empirical ε of a halver
fn measure_epsilon(net: &ComparatorNetwork, num_trials: usize, seed: u64) -> f64 {
    let n = net.n;
    let m = n / 2;
    if m == 0 {
        return 0.0;
    }
    let mut rng = seed;
    let mut rand_next = || -> u64 {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };
    let mut max_ratio = 0.0f64;
    for _ in 0..num_trials {
        let mut perm: Vec<usize> = (0..n).collect();
        for i in (1..n).rev() {
            let j = (rand_next() as usize) % (i + 1);
            perm.swap(i, j);
        }
        net.exec(&mut perm);
        // EpsilonInitialHalved: for each k ≤ m, count {pos ≥ m : output[pos] < k}
        for k in 1..=m {
            let count = (m..n).filter(|&pos| perm[pos] < k).count();
            let ratio = count as f64 / k as f64;
            max_ratio = max_ratio.max(ratio);
        }
        // EpsilonFinalHalved: for each k ≤ m, count {pos < m : output[pos] ≥ n-k}
        for k in 1..=m {
            let count = (0..m).filter(|&pos| perm[pos] >= n - k).count();
            let ratio = count as f64 / k as f64;
            max_ratio = max_ratio.max(ratio);
        }
    }
    max_ratio
}

// ──────────────────────────────────────────────────────────
// Random permutation utility
// ──────────────────────────────────────────────────────────

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed)
    }
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn random_perm(&mut self, n: usize) -> Vec<usize> {
        let mut perm: Vec<usize> = (0..n).collect();
        for i in (1..n).rev() {
            let j = (self.next() as usize) % (i + 1);
            perm.swap(i, j);
        }
        perm
    }
}

// ──────────────────────────────────────────────────────────
// Invert a permutation: given output[pos] = val, find pos for each val
// ──────────────────────────────────────────────────────────

fn invert(output: &[usize]) -> Vec<usize> {
    let n = output.len();
    let mut inv = vec![0usize; n];
    for (pos, &val) in output.iter().enumerate() {
        inv[val] = pos;
    }
    inv
}

// ──────────────────────────────────────────────────────────
// hasGoodRadius: matches Correctness.lean definition
// pos(a)/cs ≤ a/cs where pos(a) = w^{-1}(a)
// ──────────────────────────────────────────────────────────

fn has_good_radius(inv: &[usize], a: usize, level: usize, n: usize) -> bool {
    let cs = n / (1 << level);
    if cs == 0 {
        return true; // degenerate: everything is "good"
    }
    let pos = inv[a];
    pos / cs <= a / cs
}

fn has_good_radius_dual(inv: &[usize], a: usize, level: usize, n: usize) -> bool {
    let cs = n / (1 << level);
    if cs == 0 {
        return true;
    }
    let pos = inv[a];
    a / cs <= pos / cs
}

// ──────────────────────────────────────────────────────────
// errorSetAtLevel: matches Correctness.lean
// ──────────────────────────────────────────────────────────

/// Compute |errorSetAtLevel(halvers, v, k, l)| for a given input permutation.
/// E_l = {a : a < k, hasGoodRadius(w_l, a, l), ¬hasGoodRadius(w_{l+1}, a, l+1)}
fn error_set_at_level(
    n: usize,
    halver_fn: &dyn Fn(usize) -> ComparatorNetwork,
    input: &[usize],
    k: usize,
    l: usize,
) -> Vec<usize> {
    let out_l = halver_network_output(n, halver_fn, l, input);
    let out_l1 = halver_network_output(n, halver_fn, l + 1, input);
    let inv_l = invert(&out_l);
    let inv_l1 = invert(&out_l1);

    let mut error_set = Vec::new();
    for a in 0..n {
        if a < k
            && has_good_radius(&inv_l, a, l, n)
            && !has_good_radius(&inv_l1, a, l + 1, n)
        {
            error_set.push(a);
        }
    }
    error_set
}

/// Dual error set
fn error_set_at_level_dual(
    n: usize,
    halver_fn: &dyn Fn(usize) -> ComparatorNetwork,
    input: &[usize],
    k: usize,
    l: usize,
) -> Vec<usize> {
    let out_l = halver_network_output(n, halver_fn, l, input);
    let out_l1 = halver_network_output(n, halver_fn, l + 1, input);
    let inv_l = invert(&out_l);
    let inv_l1 = invert(&out_l1);

    let mut error_set = Vec::new();
    for a in 0..n {
        if n <= a + k // a.val ≥ n - k
            && has_good_radius_dual(&inv_l, a, l, n)
            && !has_good_radius_dual(&inv_l1, a, l + 1, n)
        {
            error_set.push(a);
        }
    }
    error_set
}

// ──────────────────────────────────────────────────────────
// farSmallCount and farLargeCount: matches Correctness.lean
// ──────────────────────────────────────────────────────────

fn far_small_count(output: &[usize], k: usize, r: usize) -> usize {
    let n = output.len();
    (0..n)
        .filter(|&pos| k + r <= pos && output[pos] < k)
        .count()
}

fn far_large_count(output: &[usize], k: usize, r: usize) -> usize {
    let n = output.len();
    (0..n)
        .filter(|&pos| pos + k + r < n && output[pos] + k >= n)
        .count()
}

// ──────────────────────────────────────────────────────────
// InitialNearsorted / FinalNearsorted check
// ──────────────────────────────────────────────────────────

/// Check InitialNearsorted(w, δ) for all k.
/// For Fin n, rank(a) = a. So S = {a < k}, Sε = {a < k + R}, R = floor(δ*n).
/// |S \ w(Sε)| ≤ δ * k
fn check_initial_nearsorted(output: &[usize], n: usize, delta: f64) -> Option<(usize, usize, f64)> {
    let r = (delta * n as f64).floor().max(0.0) as usize;
    let mut worst: Option<(usize, usize, f64)> = None;
    for k in 0..=n {
        // S = {a : a < k}
        // Sε = {a : a < k + R}
        // w(Sε) = {output[pos] : pos < k + R} (image of Sε under w)
        // Wait — w maps positions to values. The image of Sε under w:
        // Sε.image w = {w(a) : a ∈ Sε} where a is a value...
        // Actually in Lean: w : Fin n → Fin n, Sε = {a | rank a < k+R} = {a | a < k+R}
        // Sε.image w = {w(a) : a < k+R}
        // S \ Sε.image w = {a < k : a ∉ {w(b) : b < k+R}}

        // Equivalently: values a < k that are NOT in the output of any position b < k+R
        // Wait, w is the network output function: w(pos) = output[pos]
        // So w(a) means: the value at position a.
        // image of Sε under w = {output[pos] : pos has rank < k+R} = {output[pos] : pos < k+R}

        // Actually let me re-read Lean:
        // S = univ.filter (fun a ↦ rank a < k) = {a : a.val < k}
        // Sε = univ.filter (fun a ↦ rank a < k + R) = {a : a.val < k+R}
        // Sε.image w = {w(a) : a.val < k+R}
        // But w is applied to *values* a, not positions!
        // w : Fin n → Fin n is the network output. w(a) = network evaluated at position a.

        // So Sε.image w = {w(a) : a < k+R} = {output[a] : a < k+R}
        // (treating a as a position index since Fin n → Fin n)

        // S \ Sε.image w = {a < k : a ∉ {output[pos] : pos < k+R}}
        // = values a < k that don't appear in output[0..k+R)

        let k_plus_r = (k + r).min(n);
        // Collect values that appear in output[0..k+R)
        let mut in_image = vec![false; n];
        for pos in 0..k_plus_r {
            in_image[output[pos]] = true;
        }
        // Count values a < k not in the image
        let sdiff_count = (0..k).filter(|&a| !in_image[a]).count();
        let bound = delta * k as f64;
        if sdiff_count as f64 > bound + 1e-9 {
            let excess = sdiff_count as f64 - bound;
            if worst.is_none() || excess > worst.unwrap().2 {
                worst = Some((k, sdiff_count, excess));
            }
        }
    }
    worst
}

/// Check FinalNearsorted(w, δ) for all k.
/// In the order dual: rank_od(a) = n - 1 - a.
/// S = {a : rank_od(a) < k} = {a : n-1-a < k} = {a : a ≥ n-k} = {a : a+k ≥ n}
/// Sε = {a : rank_od(a) < k+R} = {a : a+k+R ≥ n}
/// Sε.image w = {w(a) : a+k+R ≥ n} = {output[a] : a ≥ n-k-R}
/// S \ Sε.image w = {a : a+k ≥ n, a ∉ {output[b] : b+k+R ≥ n}}
fn check_final_nearsorted(output: &[usize], n: usize, delta: f64) -> Option<(usize, usize, f64)> {
    let r = (delta * n as f64).floor().max(0.0) as usize;
    let mut worst: Option<(usize, usize, f64)> = None;
    for k in 0..=n {
        // S = {a ≥ n-k} (i.e., last k values)
        // Sε = {a ≥ n-k-R} (last k+R values)
        let s_start = if n >= k { n - k } else { 0 };
        let se_start = if n >= k + r { n - k - r } else { 0 };

        // Sε.image w = {output[a] : a ≥ se_start}
        let mut in_image = vec![false; n];
        for a in se_start..n {
            in_image[output[a]] = true;
        }
        // S \ Sε.image w = {a ≥ s_start : a ∉ image}
        let sdiff_count = (s_start..n).filter(|&a| !in_image[a]).count();
        let bound = delta * k as f64;
        if sdiff_count as f64 > bound + 1e-9 {
            let excess = sdiff_count as f64 - bound;
            if worst.is_none() || excess > worst.unwrap().2 {
                worst = Some((k, sdiff_count, excess));
            }
        }
    }
    worst
}

// ──────────────────────────────────────────────────────────
// Overflow diagnostic: check if f_c + t_c > hs ever occurs
// ──────────────────────────────────────────────────────────

/// For each chunk c at level l, compute f_c (foreign-below count) and t_c (home-top-small count).
/// Returns (max_overflow, total_overflow_chunks) where overflow = max(0, f_c + t_c - hs).
fn check_overflow(
    n: usize,
    halver_fn: &dyn Fn(usize) -> ComparatorNetwork,
    input: &[usize],
    k: usize,
    l: usize,
) -> (usize, usize) {
    let out_l = halver_network_output(n, halver_fn, l, input);
    let inv_l = invert(&out_l);
    let cs = n / (1 << l);
    if cs == 0 { return (0, 0); }
    let hs = cs / 2;
    if hs == 0 { return (0, 0); }
    let num_chunks = 1 << l;

    let mut max_overflow = 0usize;
    let mut overflow_chunks = 0usize;

    for c in 0..num_chunks {
        // Only relevant chunks (c*cs <= k)
        if c * cs > k { continue; }

        // f_c: number of values in chunk c with val < c*cs
        // (ALL such values, not just val < k)
        let mut f_c = 0usize;
        // t_c: home-top-small values: val in [c*cs, c*cs+hs) with val < k, positioned in chunk c
        let mut t_c = 0usize;

        for pos in (c * cs)..((c + 1) * cs).min(n) {
            let val = out_l[pos];
            if val < c * cs {
                f_c += 1;
            } else if val >= c * cs && val < c * cs + hs && val < k {
                t_c += 1;
            }
        }

        if f_c + t_c > hs {
            let surplus = f_c + t_c - hs;
            overflow_chunks += 1;
            max_overflow = max_overflow.max(surplus);
        }
    }
    (max_overflow, overflow_chunks)
}

// ──────────────────────────────────────────────────────────
// Main tests
// ──────────────────────────────────────────────────────────

fn main() {
    println!("══════════════════════════════════════════════════════");
    println!("Test nearsort sorry's from Correctness.lean");
    println!("══════════════════════════════════════════════════════\n");

    // Test configurations: (n, halver_degree, depths_to_test)
    let configs: Vec<(usize, usize, Vec<usize>)> = vec![
        (64, 6, vec![1, 2, 3, 4, 5]),
        (128, 6, vec![1, 2, 3, 4, 5, 6]),
        (256, 8, vec![1, 2, 3, 4, 5, 6, 7]),
        (512, 8, vec![1, 2, 3, 4, 5, 6, 7, 8]),
    ];

    let trials = 500;

    for (n, deg, depths) in &configs {
        let n = *n;
        let deg = *deg;

        println!("═══ n={n}, halver degree={deg} ═══\n");

        // Build halver family: synthetic random bipartite halvers at all sub-sizes
        let halver_fn = |half_m: usize| -> ComparatorNetwork {
            synthetic_halver(half_m, deg, 42 + half_m as u64 * 1000 + deg as u64)
        };

        // Measure ε across all sub-sizes
        let mut max_eps = 0.0f64;
        {
            let mut sub_m = n / 2;
            while sub_m >= 4 {
                let sub_halver = halver_fn(sub_m);
                let sub_eps = measure_epsilon(&sub_halver, 2000, 88888 + sub_m as u64);
                println!("  ε at m={sub_m} (d={deg}): {sub_eps:.4}");
                max_eps = max_eps.max(sub_eps);
                sub_m /= 2;
            }
        }
        let eps = max_eps;
        println!("  Family max ε = {eps:.4}\n");

        // ──────────────────────────────────────────────────
        // Test 1: error_set_bound — |E_l| ≤ ε * k
        // ──────────────────────────────────────────────────
        println!("  --- Test 1: error_set_bound |E_l| ≤ ε * k ---");
        let mut rng = Rng::new(123456789);
        let mut max_violation_primal = 0.0f64;
        let mut violation_count_primal = 0usize;
        let mut total_tests_primal = 0usize;

        for &depth in depths {
            for _ in 0..trials {
                let input = rng.random_perm(n);
                for l in 0..depth {
                    // Test for various k values
                    for k_frac in &[0.1, 0.25, 0.5, 0.75, 0.9, 1.0] {
                        let k = ((*k_frac) * n as f64).round() as usize;
                        if k == 0 || k > n {
                            continue;
                        }
                        // Check divisibility: 2^(l+1) | n
                        if n % (1 << (l + 1)) != 0 {
                            continue;
                        }
                        total_tests_primal += 1;
                        let eset = error_set_at_level(n, &halver_fn, &input, k, l);
                        let bound = eps * k as f64;
                        if eset.len() as f64 > bound + 1e-9 {
                            let excess = eset.len() as f64 - bound;
                            violation_count_primal += 1;
                            if excess > max_violation_primal {
                                max_violation_primal = excess;
                                if violation_count_primal <= 3 {
                                    println!(
                                        "    VIOLATION: depth={depth}, l={l}, k={k}: |E_l|={}, bound={bound:.2}, excess={excess:.2}",
                                        eset.len()
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
        if violation_count_primal > 0 {
            println!(
                "    error_set_bound: {violation_count_primal}/{total_tests_primal} violations, max excess = {max_violation_primal:.2} FAIL"
            );
        } else {
            println!("    error_set_bound: 0/{total_tests_primal} violations OK");
        }

        // ──────────────────────────────────────────────────
        // Test 1b: error_set_bound_dual — |E_l_dual| ≤ ε * k
        // ──────────────────────────────────────────────────
        println!("\n  --- Test 1b: error_set_bound_dual |E_l_dual| ≤ ε * k ---");
        let mut rng = Rng::new(987654321);
        let mut max_violation_dual = 0.0f64;
        let mut violation_count_dual = 0usize;
        let mut total_tests_dual = 0usize;

        for &depth in depths {
            for _ in 0..trials {
                let input = rng.random_perm(n);
                for l in 0..depth {
                    for k_frac in &[0.1, 0.25, 0.5, 0.75, 0.9, 1.0] {
                        let k = ((*k_frac) * n as f64).round() as usize;
                        if k == 0 || k > n {
                            continue;
                        }
                        if n % (1 << (l + 1)) != 0 {
                            continue;
                        }
                        total_tests_dual += 1;
                        let eset = error_set_at_level_dual(n, &halver_fn, &input, k, l);
                        let bound = eps * k as f64;
                        if eset.len() as f64 > bound + 1e-9 {
                            let excess = eset.len() as f64 - bound;
                            violation_count_dual += 1;
                            if excess > max_violation_dual {
                                max_violation_dual = excess;
                                if violation_count_dual <= 3 {
                                    println!(
                                        "    VIOLATION: depth={depth}, l={l}, k={k}: |E_l_dual|={}, bound={bound:.2}, excess={excess:.2}",
                                        eset.len()
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
        if violation_count_dual > 0 {
            println!(
                "    error_set_bound_dual: {violation_count_dual}/{total_tests_dual} violations, max excess = {max_violation_dual:.2} FAIL"
            );
        } else {
            println!("    error_set_bound_dual: 0/{total_tests_dual} violations OK");
        }

        // ──────────────────────────────────────────────────
        // Test 2: farSmallCount_depth_bound — farSmallCount ≤ ε * depth * k
        // ──────────────────────────────────────────────────
        println!("\n  --- Test 2: farSmallCount_depth_bound ≤ ε * depth * k ---");
        let mut rng = Rng::new(111222333);
        let mut max_violation_fsc = 0.0f64;
        let mut violation_count_fsc = 0usize;
        let mut total_tests_fsc = 0usize;

        for &depth in depths {
            if n % (1 << depth) != 0 {
                continue;
            }
            let r = n / (1 << depth);
            for _ in 0..trials {
                let input = rng.random_perm(n);
                let output = halver_network_output(n, &halver_fn, depth, &input);
                for k_frac in &[0.1, 0.25, 0.5, 0.75, 0.9, 1.0] {
                    let k = ((*k_frac) * n as f64).round() as usize;
                    if k == 0 || k > n {
                        continue;
                    }
                    total_tests_fsc += 1;
                    let fsc = far_small_count(&output, k, r);
                    let bound = eps * depth as f64 * k as f64;
                    if fsc as f64 > bound + 1e-9 {
                        let excess = fsc as f64 - bound;
                        violation_count_fsc += 1;
                        if excess > max_violation_fsc {
                            max_violation_fsc = excess;
                            if violation_count_fsc <= 3 {
                                println!(
                                    "    VIOLATION: depth={depth}, k={k}, R={r}: fsc={fsc}, bound={bound:.2}, excess={excess:.2}"
                                );
                            }
                        }
                    }
                }
            }
        }
        if violation_count_fsc > 0 {
            println!(
                "    farSmallCount: {violation_count_fsc}/{total_tests_fsc} violations, max excess = {max_violation_fsc:.2} FAIL"
            );
        } else {
            println!("    farSmallCount: 0/{total_tests_fsc} violations OK");
        }

        // ──────────────────────────────────────────────────
        // Test 2b: farLargeCount_depth_bound ≤ ε * depth * k
        // ──────────────────────────────────────────────────
        println!("\n  --- Test 2b: farLargeCount_depth_bound ≤ ε * depth * k ---");
        let mut rng = Rng::new(444555666);
        let mut max_violation_flc = 0.0f64;
        let mut violation_count_flc = 0usize;
        let mut total_tests_flc = 0usize;

        for &depth in depths {
            if n % (1 << depth) != 0 {
                continue;
            }
            let r = n / (1 << depth);
            for _ in 0..trials {
                let input = rng.random_perm(n);
                let output = halver_network_output(n, &halver_fn, depth, &input);
                for k_frac in &[0.1, 0.25, 0.5, 0.75, 0.9, 1.0] {
                    let k = ((*k_frac) * n as f64).round() as usize;
                    if k == 0 || k > n {
                        continue;
                    }
                    total_tests_flc += 1;
                    let flc = far_large_count(&output, k, r);
                    let bound = eps * depth as f64 * k as f64;
                    if flc as f64 > bound + 1e-9 {
                        let excess = flc as f64 - bound;
                        violation_count_flc += 1;
                        if excess > max_violation_flc {
                            max_violation_flc = excess;
                            if violation_count_flc <= 3 {
                                println!(
                                    "    VIOLATION: depth={depth}, k={k}, R={r}: flc={flc}, bound={bound:.2}, excess={excess:.2}"
                                );
                            }
                        }
                    }
                }
            }
        }
        if violation_count_flc > 0 {
            println!(
                "    farLargeCount: {violation_count_flc}/{total_tests_flc} violations, max excess = {max_violation_flc:.2} FAIL"
            );
        } else {
            println!("    farLargeCount: 0/{total_tests_flc} violations OK");
        }

        // ──────────────────────────────────────────────────
        // Test 3: InitialNearsorted / FinalNearsorted
        // ──────────────────────────────────────────────────
        println!("\n  --- Test 3: InitialNearsorted / FinalNearsorted ---");
        let mut rng = Rng::new(777888999);

        for &depth in depths {
            if n % (1 << depth) != 0 {
                continue;
            }
            let delta = eps * depth as f64;
            let mut init_violations = 0;
            let mut final_violations = 0;

            for _ in 0..trials {
                let input = rng.random_perm(n);
                let output = halver_network_output(n, &halver_fn, depth, &input);

                if check_initial_nearsorted(&output, n, delta).is_some() {
                    init_violations += 1;
                }
                if check_final_nearsorted(&output, n, delta).is_some() {
                    final_violations += 1;
                }
            }

            let status = if init_violations == 0 && final_violations == 0 {
                "OK"
            } else {
                "FAIL"
            };
            println!(
                "    depth={depth}: δ={delta:.4}, violations: init={init_violations}/{trials}, final={final_violations}/{trials} {status}"
            );
        }

        // ──────────────────────────────────────────────────
        // Test 4: Union bound alternative — Σ|E_l| ≤ ε * depth * k
        // Tests whether the AGGREGATE bound holds even when per-level fails
        // ──────────────────────────────────────────────────
        println!("\n  --- Test 4: Union bound Σ|E_l| ≤ ε * depth * k ---");
        let mut rng = Rng::new(555444333);

        for &depth in depths {
            if n % (1 << depth) != 0 {
                continue;
            }
            let mut max_violation_ub = 0.0f64;
            let mut violation_count_ub = 0usize;
            let mut total_ub = 0usize;

            for _ in 0..trials {
                let input = rng.random_perm(n);
                for k_frac in &[0.1, 0.25, 0.5, 0.75, 0.9, 1.0] {
                    let k = ((*k_frac) * n as f64).round() as usize;
                    if k == 0 || k > n {
                        continue;
                    }
                    total_ub += 1;
                    // Sum |E_l| over all levels
                    let mut total_error: usize = 0;
                    for l in 0..depth {
                        if n % (1 << (l + 1)) != 0 {
                            continue;
                        }
                        let eset = error_set_at_level(n, &halver_fn, &input, k, l);
                        total_error += eset.len();
                    }
                    let bound = eps * depth as f64 * k as f64;
                    if total_error as f64 > bound + 1e-9 {
                        let excess = total_error as f64 - bound;
                        violation_count_ub += 1;
                        max_violation_ub = max_violation_ub.max(excess);
                    }
                }
            }
            if violation_count_ub > 0 {
                println!(
                    "    depth={depth}: {violation_count_ub}/{total_ub} violations, max excess = {max_violation_ub:.2} FAIL"
                );
            } else {
                println!("    depth={depth}: 0/{total_ub} violations OK");
            }
        }

        // ──────────────────────────────────────────────────
        // Test 5: What bound DOES hold per-level?
        // Find the worst ratio |E_l| / k across all tests
        // ──────────────────────────────────────────────────
        println!("\n  --- Test 5: Empirical per-level ratio max(|E_l|/k) ---");
        let mut rng = Rng::new(222333444);
        let mut worst_ratio_per_level: Vec<f64> = vec![0.0; depths.iter().copied().max().unwrap_or(0)];

        for &depth in depths {
            for _ in 0..trials {
                let input = rng.random_perm(n);
                for l in 0..depth {
                    if n % (1 << (l + 1)) != 0 {
                        continue;
                    }
                    for k_frac in &[0.1, 0.25, 0.5, 0.75, 0.9, 1.0] {
                        let k = ((*k_frac) * n as f64).round() as usize;
                        if k == 0 || k > n {
                            continue;
                        }
                        let eset = error_set_at_level(n, &halver_fn, &input, k, l);
                        let ratio = eset.len() as f64 / k as f64;
                        if l < worst_ratio_per_level.len() {
                            worst_ratio_per_level[l] = worst_ratio_per_level[l].max(ratio);
                        }
                    }
                }
            }
        }
        for (l, ratio) in worst_ratio_per_level.iter().enumerate() {
            if *ratio > 0.0 {
                let ok = *ratio <= eps + 1e-9;
                println!(
                    "    level {l}: max |E_l|/k = {ratio:.4} (ε = {eps:.4}) {}",
                    if ok { "OK" } else { "EXCEEDS ε" }
                );
            }
        }

        // ──────────────────────────────────────────────────
        // Test 6: Overflow diagnostic — does f_c + t_c > hs ever occur?
        // ──────────────────────────────────────────────────
        println!("  --- Test 6: Overflow diagnostic (f_c + t_c > hs) ---");
        let mut rng = Rng::new(333222111);
        let mut total_overflow = 0usize;
        let mut max_overflow_val = 0usize;

        for &depth in depths {
            for _ in 0..trials {
                let input = rng.random_perm(n);
                for l in 0..depth {
                    if n % (1 << (l + 1)) != 0 {
                        continue;
                    }
                    for k_frac in &[0.1, 0.25, 0.5, 0.75, 0.9, 1.0] {
                        let k = ((*k_frac) * n as f64).round() as usize;
                        if k == 0 || k > n {
                            continue;
                        }
                        let (max_of, of_chunks) = check_overflow(n, &halver_fn, &input, k, l);
                        total_overflow += of_chunks;
                        max_overflow_val = max_overflow_val.max(max_of);
                        if of_chunks > 0 && total_overflow <= 5 {
                            let cs = n / (1 << l);
                            let hs = cs / 2;
                            println!(
                                "    OVERFLOW: depth={depth}, l={l}, k={k}, hs={hs}: {of_chunks} chunks, max surplus={max_of}"
                            );
                        }
                    }
                }
            }
        }
        if total_overflow > 0 {
            println!("    Total overflow chunks: {total_overflow}, max surplus: {max_overflow_val}");
        } else {
            println!("    No overflow detected (f_c + t_c ≤ hs for all chunks)");
        }

        println!();
    }

    println!("=== All tests complete ===");
}
