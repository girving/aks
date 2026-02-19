#!/usr/bin/env -S cargo +nightly -Zscript
//! Test separator sorry's: depth bounds and separator correctness
//!
//! Tests:
//! 1. halverAtLevel_depth_le: depth of halvers at one tree level ≤ d
//! 2. halverToSeparator_depth_le: depth of iterated halver network ≤ t * d
//! 3. separator_halving_step / halverToSeparator_isSeparator:
//!    iterated halving gives (1/2^t, t*ε)-separation (requires 2^t | n)
//!
//! Usage: cargo +nightly -Zscript rust/test-separator.rs

use std::fs;

// ──────────────────────────────────────────────────────────
// Core types matching Lean definitions exactly
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
    /// Execute network on a permutation (in-place).
    /// Matches `ComparatorNetwork.exec` in Sort/Defs.lean.
    fn exec(&self, v: &mut [usize]) {
        for c in &self.comparators {
            if v[c.i] > v[c.j] {
                v.swap(c.i, c.j);
            }
        }
    }

    /// Greedy critical-path depth.
    /// Matches `ComparatorNetwork.depth` in Sort/Depth.lean.
    fn depth(&self) -> usize {
        let mut wire_times = vec![0usize; self.n];
        let mut max_depth = 0usize;
        for c in &self.comparators {
            let t = wire_times[c.i].max(wire_times[c.j]) + 1;
            wire_times[c.i] = t;
            wire_times[c.j] = t;
            max_depth = max_depth.max(t);
        }
        max_depth
    }

    fn size(&self) -> usize {
        self.comparators.len()
    }
}

// ──────────────────────────────────────────────────────────
// RegularGraph from rotation map data
// ──────────────────────────────────────────────────────────

struct RegularGraph {
    n: usize,
    d: usize,
    /// rot_data[2*(v*d+p)] = neighbor vertex, rot_data[2*(v*d+p)+1] = reverse port
    rot_data: Vec<i32>,
}

impl RegularGraph {
    fn from_binary_file(path: &str, n: usize, d: usize) -> Self {
        let bytes = fs::read(path).unwrap_or_else(|e| panic!("Cannot read {path}: {e}"));
        assert_eq!(bytes.len(), n * d * 2 * 4, "Expected {} bytes", n * d * 2 * 4);
        let rot_data: Vec<i32> = bytes
            .chunks_exact(4)
            .map(|chunk| i32::from_le_bytes(chunk.try_into().unwrap()))
            .collect();
        Self { n, d, rot_data }
    }

    fn neighbor(&self, v: usize, p: usize) -> usize {
        self.rot_data[2 * (v * self.d + p)] as usize
    }
}

// ──────────────────────────────────────────────────────────
// Expander halver construction
// Matches `bipartiteComparators` in Halver/ExpanderToHalver.lean
// ──────────────────────────────────────────────────────────

/// Build the bipartite comparator network from a d-regular graph on m vertices.
/// Network has 2*m wires: top half [0, m), bottom half [m, 2m).
fn expander_halver(g: &RegularGraph) -> ComparatorNetwork {
    let m = g.n;
    let mut comparators = Vec::with_capacity(m * g.d);
    for v in 0..m {
        for p in 0..g.d {
            let u = g.neighbor(v, p);
            // Compare wire v (top) with wire m + u (bottom)
            let i = v;
            let j = m + u;
            // Ensure i < j (always true since i < m ≤ j)
            comparators.push(Comparator { i, j });
        }
    }
    ComparatorNetwork { n: 2 * m, comparators }
}

// ──────────────────────────────────────────────────────────
// halverAtLevel and halverNetwork
// Matches Nearsort/Construction.lean
// ──────────────────────────────────────────────────────────

/// Apply halvers to all sub-intervals at a given tree level.
/// At level l: 2^l chunks of size ⌊n / 2^l⌋, each halved.
fn halver_at_level(
    n: usize,
    halver_fn: &dyn Fn(usize) -> ComparatorNetwork, // m -> halver on 2*m wires
    level: usize,
) -> ComparatorNetwork {
    let chunk_size = n / (1 << level);
    let half_chunk = chunk_size / 2;
    let num_chunks = 1 << level;

    let mut comparators = Vec::new();
    for k in 0..num_chunks {
        let offset = k * chunk_size;
        if offset + 2 * half_chunk <= n {
            // Build halver for this half-chunk and shift to offset
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

/// The full recursive halver network: levels 0..depth-1.
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

// ──────────────────────────────────────────────────────────
// Separator property checking
// Matches Separator/Defs.lean
// ──────────────────────────────────────────────────────────

/// Check SepInitial: for each γ' in test_gammas with γ' ≤ γ,
/// count positions pos where rank(pos) ≥ ⌊γ*n⌋ and rank(w[pos]) < ⌊γ'*n⌋.
/// Returns (γ', count, bound ε*γ'*n) for the worst violation, or None if all pass.
fn check_sep_initial(
    output: &[usize], // output permutation: output[pos] = value at position pos
    n: usize,
    gamma: f64,
    epsilon: f64,
) -> Option<(f64, usize, f64)> {
    // For labeled permutation inputs, rank(pos) = pos and rank(val) = val
    // (since rank of Fin n is just its value)
    let gamma_n = (gamma * n as f64).floor() as usize;

    // Test many values of γ'
    let num_tests = 1000.min(n);
    let mut worst: Option<(f64, usize, f64)> = None;

    for t in 0..=num_tests {
        let gamma_prime = gamma * (t as f64) / (num_tests as f64);
        if gamma_prime < 0.0 {
            continue;
        }
        let k = (gamma_prime * n as f64).floor() as usize;

        // Count positions where rank(pos) >= gamma_n AND rank(output[pos]) < k
        let count = (0..n)
            .filter(|&pos| pos >= gamma_n && output[pos] < k)
            .count();

        let bound = epsilon * gamma_prime * n as f64;
        if (count as f64) > bound + 1e-9 {
            let violation = (gamma_prime, count, bound);
            if worst.is_none()
                || count as f64 - bound > worst.unwrap().1 as f64 - worst.unwrap().2
            {
                worst = Some(violation);
            }
        }
    }
    worst
}

/// Check SepFinal (dual direction): for each γ' ≤ γ,
/// count positions pos where rank_dual(pos) ≥ ⌊γ*n⌋ and rank_dual(w[pos]) < ⌊γ'*n⌋.
/// In the order dual, rank_dual(x) = n - 1 - x.
fn check_sep_final(
    output: &[usize],
    n: usize,
    gamma: f64,
    epsilon: f64,
) -> Option<(f64, usize, f64)> {
    // Transform to dual: rank_od(pos) = n-1-pos, rank_od(val) = n-1-val
    // So condition becomes: n-1-pos >= ⌊γ*n⌋ ∧ n-1-output[pos] < ⌊γ'*n⌋
    // i.e., pos <= n-1-⌊γ*n⌋ ∧ output[pos] > n-1-⌊γ'*n⌋
    // Equivalently: pos < n - ⌊γ*n⌋ ∧ output[pos] >= n - ⌊γ'*n⌋
    let gamma_n = (gamma * n as f64).floor() as usize;
    let cutoff = if n >= gamma_n { n - gamma_n } else { 0 };

    let num_tests = 1000.min(n);
    let mut worst: Option<(f64, usize, f64)> = None;

    for t in 0..=num_tests {
        let gamma_prime = gamma * (t as f64) / (num_tests as f64);
        if gamma_prime < 0.0 {
            continue;
        }
        let k = (gamma_prime * n as f64).floor() as usize;
        let val_cutoff = if n >= k { n - k } else { 0 };

        // Count: pos < cutoff AND output[pos] >= val_cutoff
        let count = (0..cutoff)
            .filter(|&pos| output[pos] >= val_cutoff)
            .count();

        let bound = epsilon * gamma_prime * n as f64;
        if (count as f64) > bound + 1e-9 {
            let violation = (gamma_prime, count, bound);
            if worst.is_none()
                || count as f64 - bound > worst.unwrap().1 as f64 - worst.unwrap().2
            {
                worst = Some(violation);
            }
        }
    }
    worst
}

// ──────────────────────────────────────────────────────────
// Tests
// ──────────────────────────────────────────────────────────

// ──────────────────────────────────────────────────────────
// König's edge coloring for bipartite graphs
// ──────────────────────────────────────────────────────────

/// Given a bipartite graph (comparators between top [0,m) and bottom [m,2m)),
/// find a proper edge coloring using exactly max_degree colors.
/// Returns a vec of colors, one per comparator. Each color is a parallel round.
/// Find a maximum matching in a bipartite graph using augmenting paths.
/// adj[u] = list of (bottom_vertex, edge_index) for top vertex u.
/// Returns match_top[u] = Some(edge_index) for matched top vertices.
fn bipartite_matching(
    m: usize,
    adj: &[Vec<(usize, usize)>],
) -> Vec<Option<usize>> {
    let mut match_top: Vec<Option<usize>> = vec![None; m]; // top -> edge idx
    let mut match_bot: Vec<Option<usize>> = vec![None; m]; // bot -> edge idx
    let mut bot_partner: Vec<Option<usize>> = vec![None; m]; // bot -> top vertex

    for u in 0..m {
        // Try to find an augmenting path from u
        let mut visited = vec![false; m]; // visited bottom vertices
        fn augment(
            u: usize,
            adj: &[Vec<(usize, usize)>],
            match_bot: &mut [Option<usize>],
            bot_partner: &mut [Option<usize>],
            match_top: &mut [Option<usize>],
            visited: &mut [bool],
        ) -> bool {
            for &(v, edge_idx) in &adj[u] {
                if visited[v] {
                    continue;
                }
                visited[v] = true;
                if bot_partner[v].is_none()
                    || augment(
                        bot_partner[v].unwrap(),
                        adj,
                        match_bot,
                        bot_partner,
                        match_top,
                        visited,
                    )
                {
                    match_top[u] = Some(edge_idx);
                    match_bot[v] = Some(edge_idx);
                    bot_partner[v] = Some(u);
                    return true;
                }
            }
            false
        }
        augment(u, adj, &mut match_bot, &mut bot_partner, &mut match_top, &mut visited);
    }
    match_top
}

/// König's edge coloring for d-regular bipartite multigraphs.
/// Repeatedly finds a perfect matching and removes it, assigning one color per round.
fn konig_edge_color(comparators: &[Comparator], m: usize, max_degree: usize) -> Vec<usize> {
    let n_comps = comparators.len();
    let mut colors = vec![0usize; n_comps];
    let mut removed = vec![false; n_comps];

    for color in 0..max_degree {
        // Build adjacency for remaining edges
        let mut adj: Vec<Vec<(usize, usize)>> = vec![vec![]; m];
        for (idx, c) in comparators.iter().enumerate() {
            if !removed[idx] {
                let top = c.i; // 0..m
                let bot = c.j - m; // m..2m -> 0..m
                adj[top].push((bot, idx));
            }
        }

        // Find a maximum matching
        let matching = bipartite_matching(m, &adj);

        // Color matched edges
        for matched_edge in matching.iter().flatten() {
            colors[*matched_edge] = color;
            removed[*matched_edge] = true;
        }
    }

    // Check all edges were colored
    let uncolored = removed.iter().filter(|&&r| !r).count();
    if uncolored > 0 {
        eprintln!("WARNING: {uncolored} edges uncolored after {max_degree} rounds");
    }
    colors
}

/// Reorder comparators by König edge coloring into parallel rounds.
/// Returns a new network with the same comparators but grouped by color.
fn reorder_by_coloring(net: &ComparatorNetwork, m: usize, d: usize) -> ComparatorNetwork {
    let colors = konig_edge_color(&net.comparators, m, d);
    let max_color = colors.iter().copied().max().unwrap_or(0);

    let mut reordered = Vec::with_capacity(net.comparators.len());
    for color in 0..=max_color {
        for (idx, c) in net.comparators.iter().enumerate() {
            if colors[idx] == color {
                reordered.push(*c);
            }
        }
    }
    ComparatorNetwork {
        n: net.n,
        comparators: reordered,
    }
}

// ──────────────────────────────────────────────────────────
// Synthetic ε-halver via random bipartite graphs
// ──────────────────────────────────────────────────────────

/// Build a random d-regular bipartite graph on m vertices (each side).
/// Returns rotation data: rot[v*d+p] = (neighbor, reverse_port).
/// Constructed by concatenating d independent random perfect matchings.
fn random_bipartite_graph(m: usize, d: usize, seed: u64) -> Vec<(usize, usize)> {
    let mut rng = seed;
    let mut rand_next = || -> usize {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng as usize
    };

    // rot[v*d + p] = (neighbor_vertex, reverse_port)
    let mut rot = vec![(0usize, 0usize); m * d];

    for p in 0..d {
        // Generate a random perfect matching (random permutation of 0..m)
        let mut perm: Vec<usize> = (0..m).collect();
        for i in (1..m).rev() {
            let j = rand_next() % (i + 1);
            perm.swap(i, j);
        }
        // perm[v] = u means top vertex v is matched to bottom vertex u
        // For the rotation map: rot(v, p) = (perm[v], reverse_port)
        // We need to find the reverse port for each edge.
        // Build inverse: inv[u] = v where perm[v] = u
        let mut inv = vec![0usize; m];
        for v in 0..m {
            inv[perm[v]] = v;
        }
        // Now the edge (v, perm[v]) at port p needs a reverse port.
        // The reverse port is p (since each matching uses port p).
        // But for a proper rotation map, we need rot(perm[v], reverse_port) = (v, p).
        // Since this is bipartite, the graph is undirected, so:
        //   rot(v, p) = (perm[v], p)  [since matching p maps v -> perm[v]]
        //   rot(perm[v], p) = (inv[perm[v]], p) = (v, p) ✓
        // Wait, that's only true if inv = perm^{-1}, which it is.
        // Actually for a bipartite graph, the "reverse port" on the other side
        // must also be p since we're using matching p on both sides.
        for v in 0..m {
            rot[v * d + p] = (perm[v], p);
        }
    }
    rot
}

/// Build an ε-halver on 2*m wires from a random d-regular bipartite graph.
/// Uses the same bipartite comparator construction as the real expander halver.
/// Lower d → higher ε (worse halver, more interesting for testing).
fn synthetic_halver(m: usize, d: usize, seed: u64) -> ComparatorNetwork {
    if m == 0 {
        return ComparatorNetwork { n: 0, comparators: vec![] };
    }
    let rot = random_bipartite_graph(m, d, seed);
    let mut comparators = Vec::with_capacity(m * d);
    for v in 0..m {
        for p in 0..d {
            let (u, _) = rot[v * d + p];
            comparators.push(Comparator { i: v, j: m + u });
        }
    }
    ComparatorNetwork { n: 2 * m, comparators }
}

/// Empirically measure the ε of a halver network by running many permutations.
fn measure_epsilon(net: &ComparatorNetwork, num_trials: usize, seed: u64) -> f64 {
    let n = net.n;
    let m = n / 2;
    if m == 0 { return 0.0; }

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

        // Check EpsilonInitialHalved: for each k ≤ m, count {pos ≥ m : output[pos] < k}
        for k in 1..=m {
            let count = (m..n).filter(|&pos| perm[pos] < k).count();
            let ratio = count as f64 / k as f64;
            max_ratio = max_ratio.max(ratio);
        }
        // Check EpsilonFinalHalved (dual): for each k ≤ m, count {pos < m : output[pos] ≥ n-k}
        for k in 1..=m {
            let count = (0..m).filter(|&pos| perm[pos] >= n - k).count();
            let ratio = count as f64 / k as f64;
            max_ratio = max_ratio.max(ratio);
        }
    }
    max_ratio
}

fn main() {
    // ══════════════════════════════════════════════════════
    // Part A: Tests with concrete expander graphs
    // ══════════════════════════════════════════════════════
    println!("══════════════════════════════════════════════════════");
    println!("Part A: Concrete expander graph tests");
    println!("══════════════════════════════════════════════════════\n");

    let graphs: Vec<(usize, usize, &str)> = vec![
        (16, 4, "data/16/rot_map.bin"),
        (1728, 12, "data/1728/rot_map.bin"),
    ];

    for &(m, d, path) in &graphs {
        if !std::path::Path::new(path).exists() {
            println!("SKIP {path} (not found)");
            continue;
        }
        let g = RegularGraph::from_binary_file(path, m, d);

        println!("=== Graph m={m}, d={d} ===");

        // Build the single expander halver
        let halver = expander_halver(&g);
        println!(
            "  Halver: {} comparators, depth {}",
            halver.size(),
            halver.depth()
        );

        // Build a halver family: concrete expander at matching size,
        // random d-regular bipartite graph at all other sizes.
        let halver_fn = |half_m: usize| -> ComparatorNetwork {
            if half_m == m {
                expander_halver(&g)
            } else if half_m > 0 {
                synthetic_halver(half_m, d, 77 + half_m as u64 * 1000 + d as u64)
            } else {
                ComparatorNetwork { n: 0, comparators: vec![] }
            }
        };

        // ─── Test 1a: Raw halver greedy depth (expected to exceed d) ───
        println!("\n  --- Test 1a: Raw halver greedy depth (before König coloring) ---");
        let test_n = 2 * m;
        {
            let level_net = halver_at_level(test_n, &halver_fn, 0);
            println!(
                "    Raw depth={}, bound d={} (expected FAIL without König)",
                level_net.depth(),
                d
            );
        }

        // ─── Test 1b: König-colored halver depth ───
        println!("\n  --- Test 1b: König-colored halver depth ---");
        let colored_halver = reorder_by_coloring(&halver, m, d);
        let colored_depth = colored_halver.depth();
        let colors = konig_edge_color(&halver.comparators, m, d);
        let max_color = colors.iter().copied().max().unwrap_or(0);
        println!(
            "    König colors used: {} (max degree d={})",
            max_color + 1,
            d
        );
        println!(
            "    Colored depth={colored_depth} (bound={d}) {}",
            if colored_depth <= d { "OK" } else { "FAIL" }
        );

        // ─── Test 1c: halverAtLevel depth ≤ d (family, all levels active) ───
        println!("\n  --- Test 1c: halverAtLevel depth ≤ d (family) ---");
        // Build König-colored halver family for depth tests
        let colored_halver_fn = |half_m: usize| -> ComparatorNetwork {
            let raw = halver_fn(half_m);
            if half_m > 0 {
                reorder_by_coloring(&raw, half_m, d)
            } else {
                raw
            }
        };
        for level in 0..6 {
            let level_net = halver_at_level(test_n, &colored_halver_fn, level);
            let depth = level_net.depth();
            let ok = depth <= d;
            let chunk_m = test_n / (1 << level) / 2;
            println!(
                "    level={level}: chunk_m={chunk_m}, size={}, depth={depth} (bound={d}) {}",
                level_net.size(),
                if ok { "OK" } else { "FAIL" }
            );
        }

        // ─── Test 2: halverNetwork depth ≤ t*d (König-colored family) ───
        println!("\n  --- Test 2: halverNetwork depth ≤ t*d (family) ---");
        for t in 1..=10 {
            let net = halver_network(test_n, &colored_halver_fn, t);
            let depth = net.depth();
            let bound = t * d;
            let ok = depth <= bound;
            println!(
                "    t={t}: size={}, depth={depth} (bound={bound}) {}",
                net.size(),
                if ok { "OK" } else { "FAIL" }
            );
        }

        // ─── Test 3: separator correctness (family with all sizes) ───
        println!("\n  --- Test 3: separator (1/2^t, 2*t*ε)-correctness (family) ---");

        let n = 2 * m;

        // Measure ε across all sub-sizes used by the family
        let mut family_max_eps = 0.0f64;
        {
            let base_eps = measure_epsilon(&halver_fn(m), 1000, 99999);
            println!("  ε at m={m} (expander): {base_eps:.4}");
            family_max_eps = family_max_eps.max(base_eps);

            let mut sub_m = m / 2;
            while sub_m >= 4 {
                let sub_eps = measure_epsilon(&halver_fn(sub_m), 1000, 88888 + sub_m as u64);
                println!("  ε at m={sub_m} (random d={d}): {sub_eps:.4}");
                family_max_eps = family_max_eps.max(sub_eps);
                sub_m /= 2;
            }
        }
        let eps_bound = family_max_eps * 1.2; // 20% safety margin
        println!("  Using ε_bound = {eps_bound:.4} (max ε × 1.2)");

        // Use a simple RNG (xorshift64)
        let mut rng_state: u64 = 12345678901234567;
        let mut rand_next = || -> u64 {
            rng_state ^= rng_state << 13;
            rng_state ^= rng_state >> 7;
            rng_state ^= rng_state << 17;
            rng_state
        };
        let mut random_perm = |size: usize| -> Vec<usize> {
            let mut perm: Vec<usize> = (0..size).collect();
            for i in (1..size).rev() {
                let j = (rand_next() as usize) % (i + 1);
                perm.swap(i, j);
            }
            perm
        };

        // Test iterated halver networks for separator property
        for t in 1..=6 {
            let net = halver_network(n, &halver_fn, t);
            let gamma = 1.0 / (1u64 << t) as f64;
            let sep_eps = t as f64 * eps_bound;  // t*ε (Seiferas Lemma 1)

            let mut init_violations = 0;
            let mut final_violations = 0;
            let trials = 500;

            for _ in 0..trials {
                let mut perm = random_perm(n);
                net.exec(&mut perm);

                if check_sep_initial(&perm, n, gamma, sep_eps).is_some() {
                    init_violations += 1;
                }
                if check_sep_final(&perm, n, gamma, sep_eps).is_some() {
                    final_violations += 1;
                }
            }

            println!(
                "    t={t}: γ=1/{}, ε_bound={sep_eps:.4}, violations: init={init_violations}/{trials}, final={final_violations}/{trials} {}",
                1u64 << t,
                if init_violations == 0 && final_violations == 0 {
                    "OK"
                } else {
                    "FAIL"
                }
            );
        }
    }

    // ══════════════════════════════════════════════════════
    // Part B: Synthetic halver tests (random bipartite graphs)
    // ══════════════════════════════════════════════════════
    println!("\n══════════════════════════════════════════════════════");
    println!("Part B: Synthetic halver tests (random bipartite graph)");
    println!("══════════════════════════════════════════════════════\n");

    // Test with various sizes and degrees.
    // Lower degree → higher ε → harder test for separator bounds.
    // d=4 gives ε ≈ 0.4-0.6, d=8 gives ε ≈ 0.2-0.3, d=16 gives ε ≈ 0.1-0.2
    for &(base_n, deg) in &[(128, 4), (256, 4), (512, 6), (1024, 8)] {
        let base_m = base_n / 2;
        println!("=== Synthetic halver: n={base_n}, degree={deg} ===");

        // Build synthetic halvers for all needed sub-sizes.
        // Use a consistent seed per sub-size so the same halver is used each time.
        let halver_fn = |half_m: usize| -> ComparatorNetwork {
            synthetic_halver(half_m, deg, 42 + half_m as u64 * 1000 + deg as u64)
        };

        // Measure ε for the base halver and sub-halvers
        let base_halver = halver_fn(base_m);
        let base_eps = measure_epsilon(&base_halver, 1000, 99999);
        println!("  Base halver (m={base_m}, d={deg}): size={}, empirical ε={base_eps:.4}",
            base_halver.size());

        let mut max_eps = base_eps;
        for &sub_m in &[base_m / 2, base_m / 4, base_m / 8] {
            if sub_m >= 4 {
                let sub_halver = halver_fn(sub_m);
                let sub_eps = measure_epsilon(&sub_halver, 1000, 88888 + sub_m as u64);
                println!("  Sub-halver (m={sub_m}, d={deg}): size={}, empirical ε={sub_eps:.4}",
                    sub_halver.size());
                max_eps = max_eps.max(sub_eps);
            }
        }

        // Use the max ε across all sub-sizes with a safety margin
        let eps_bound = max_eps * 1.2; // 20% safety margin for sampling noise
        println!("  Using ε_bound = {eps_bound:.4} (max ε across sizes × 1.2)");

        // Test separator property for t = 1..6
        println!("\n  --- Separator (1/2^t, t*ε)-correctness ---");

        let mut rng_state: u64 = 314159265;
        let mut rand_next = || -> u64 {
            rng_state ^= rng_state << 13;
            rng_state ^= rng_state >> 7;
            rng_state ^= rng_state << 17;
            rng_state
        };
        let mut random_perm = |size: usize| -> Vec<usize> {
            let mut perm: Vec<usize> = (0..size).collect();
            for i in (1..size).rev() {
                let j = (rand_next() as usize) % (i + 1);
                perm.swap(i, j);
            }
            perm
        };

        for t in 1..=6 {
            let net = halver_network(base_n, &halver_fn, t);
            let gamma = 1.0 / (1u64 << t) as f64;
            let sep_eps = t as f64 * eps_bound;  // t*ε (Seiferas Lemma 1)

            let trials = 500;
            let mut init_violations = 0;
            let mut final_violations = 0;
            let mut worst_init_excess = 0.0f64;
            let mut worst_final_excess = 0.0f64;

            for _ in 0..trials {
                let mut perm = random_perm(base_n);
                net.exec(&mut perm);

                if let Some((gp, count, bound)) = check_sep_initial(&perm, base_n, gamma, sep_eps) {
                    init_violations += 1;
                    let excess = count as f64 - bound;
                    worst_init_excess = worst_init_excess.max(excess);
                    if init_violations == 1 {
                        println!("    [debug] t={t} init violation: γ'={gp:.4}, count={count}, bound={bound:.2}");
                    }
                }
                if let Some((gp, count, bound)) = check_sep_final(&perm, base_n, gamma, sep_eps) {
                    final_violations += 1;
                    let excess = count as f64 - bound;
                    worst_final_excess = worst_final_excess.max(excess);
                    if final_violations == 1 {
                        println!("    [debug] t={t} final violation: γ'={gp:.4}, count={count}, bound={bound:.2}");
                    }
                }
            }

            let status = if init_violations == 0 && final_violations == 0 {
                "OK"
            } else {
                "FAIL"
            };
            println!(
                "    t={t}: γ=1/{}, ε_bound={sep_eps:.4}, violations: init={init_violations}/{trials}, final={final_violations}/{trials} {status}",
                1u64 << t
            );
            if init_violations > 0 || final_violations > 0 {
                println!("      worst excess: init={worst_init_excess:.2}, final={worst_final_excess:.2}");
            }
        }
        println!();
    }

    // ══════════════════════════════════════════════════════
    // Part C: Test separator_halving_step individually
    // ══════════════════════════════════════════════════════
    println!("══════════════════════════════════════════════════════");
    println!("Part C: separator_halving_step (per-step test)");
    println!("══════════════════════════════════════════════════════\n");

    // Test the INDIVIDUAL step: given (γ, ε')-sep net, append one level → (γ/2, ε'+?ε₁)-sep?
    // Test both aligned (γ = 1/2^level) and misaligned cases.
    for &(base_n, deg) in &[(256, 4), (512, 6)] {
        let base_m = base_n / 2;
        println!("=== n={base_n}, degree={deg} ===");

        let halver_fn = |half_m: usize| -> ComparatorNetwork {
            synthetic_halver(half_m, deg, 42 + half_m as u64 * 1000 + deg as u64)
        };

        // Measure max ε across all sub-sizes
        let mut max_eps = 0.0f64;
        let mut sub_m = base_m;
        while sub_m >= 4 {
            let eps = measure_epsilon(&halver_fn(sub_m), 2000, 55555 + sub_m as u64);
            max_eps = max_eps.max(eps);
            sub_m /= 2;
        }
        let eps = max_eps * 1.2;
        println!("  ε_bound = {eps:.4}");

        let mut rng_state: u64 = 271828182;
        let mut rand_next = || -> u64 {
            rng_state ^= rng_state << 13;
            rng_state ^= rng_state >> 7;
            rng_state ^= rng_state << 17;
            rng_state
        };
        let mut random_perm = |size: usize| -> Vec<usize> {
            let mut perm: Vec<usize> = (0..size).collect();
            for i in (1..size).rev() {
                let j = (rand_next() as usize) % (i + 1);
                perm.swap(i, j);
            }
            perm
        };

        // Test aligned: γ = 1/2^t, append level t → should give (1/2^(t+1), ε' + c*ε₁)
        println!("\n  --- Aligned: γ = 1/2^t, level = t ---");
        for t in 0..=5 {
            // Build net for t levels (gives (1/2^t, ?)-sep)
            let base_net_comps: Vec<Comparator> = (0..t).flat_map(|l| {
                halver_at_level(base_n, &halver_fn, l).comparators
            }).collect();
            // Append level t
            let level_comps = halver_at_level(base_n, &halver_fn, t).comparators;
            let full_comps: Vec<Comparator> = base_net_comps.iter().chain(level_comps.iter()).copied().collect();
            let full_net = ComparatorNetwork { n: base_n, comparators: full_comps };

            let new_gamma = 1.0 / (1u64 << (t + 1)) as f64;
            let tight_eps = (t as f64 + 1.0) * eps;       // (t+1)*ε — if step adds ε
            let loose_eps = 2.0 * (t as f64 + 1.0) * eps; // 2(t+1)*ε — original claim

            let trials = 1000;
            let mut tight_viol = 0;
            let mut loose_viol = 0;

            for _ in 0..trials {
                let mut perm = random_perm(base_n);
                full_net.exec(&mut perm);
                let tf = check_sep_initial(&perm, base_n, new_gamma, tight_eps).is_some()
                    || check_sep_final(&perm, base_n, new_gamma, tight_eps).is_some();
                let lf = check_sep_initial(&perm, base_n, new_gamma, loose_eps).is_some()
                    || check_sep_final(&perm, base_n, new_gamma, loose_eps).is_some();
                if tf { tight_viol += 1; }
                if lf { loose_viol += 1; }
            }
            println!(
                "    t={t}→{}: γ=1/{:<4}  (t+1)*ε={tight_eps:.4} viol={tight_viol}/{trials}  2(t+1)*ε={loose_eps:.4} viol={loose_viol}/{trials}",
                t + 1, 1u64 << (t + 1)
            );
        }

        // Test MISALIGNED with PERFECT halvers (sorting network, ε = 0)
        println!("\n  --- Misaligned: perfect halvers (ε=0), γ=1/2, various levels ---");
        {
            // Build a perfect halver: odd-even transposition sort on 2*m wires
            let perfect_halver_fn = |half_m: usize| -> ComparatorNetwork {
                if half_m == 0 { return ComparatorNetwork { n: 0, comparators: vec![] }; }
                let nn = 2 * half_m;
                let mut comps = Vec::new();
                for _pass in 0..nn {
                    let mut i = 0;
                    while i + 1 < nn { comps.push(Comparator { i, j: i + 1 }); i += 2; }
                    i = 1;
                    while i + 1 < nn { comps.push(Comparator { i, j: i + 1 }); i += 2; }
                }
                ComparatorNetwork { n: nn, comparators: comps }
            };
            // Verify ε = 0
            let test_eps = measure_epsilon(&perfect_halver_fn(base_m), 500, 11111);
            println!("    perfect halver ε = {test_eps:.6} (should be 0)");

            // Base net: level 0 → perfect (1/2, 0)-sep
            let base_net = halver_at_level(base_n, &perfect_halver_fn, 0);
            for append_level in [1, 2, 3, 4, 5] {
                let level_comps = halver_at_level(base_n, &perfect_halver_fn, append_level).comparators;
                let full_comps: Vec<Comparator> = base_net.comparators.iter().chain(level_comps.iter()).copied().collect();
                let full_net = ComparatorNetwork { n: base_n, comparators: full_comps };

                // Old claim: (1/4, 0 + 2*0) = (1/4, 0)-sep
                let new_gamma = 0.25;
                let sep_eps = 0.0;

                let trials = 1000;
                let mut violations = 0;
                for _ in 0..trials {
                    let mut perm = random_perm(base_n);
                    full_net.exec(&mut perm);
                    if check_sep_initial(&perm, base_n, new_gamma, sep_eps).is_some()
                        || check_sep_final(&perm, base_n, new_gamma, sep_eps).is_some() {
                        violations += 1;
                    }
                }
                let chunk_m = base_n / (1 << append_level) / 2;
                println!(
                    "    level={append_level} (chunk_m={chunk_m:>3}): (1/4, 0)-sep viol={violations}/{trials} {}",
                    if violations == 0 { "OK" } else if append_level == 1 { "OK (aligned)" }
                    else { "FAIL (misaligned!)" }
                );
            }
        }
        println!();
    }

    // ══════════════════════════════════════════════════════
    // Part D: Odd chunk size bug (confirmed counterexample)
    // ══════════════════════════════════════════════════════
    println!("══════════════════════════════════════════════════════");
    println!("Part D: Odd chunk size bug (divisibility hypothesis)");
    println!("══════════════════════════════════════════════════════\n");

    {
        // The halverAtLevel construction doesn't cover the last position of each
        // chunk when chunkSize is odd (2*halfChunk < chunkSize). This leaves a
        // "stranded" position that can hold a small value, violating the separator bound.
        //
        // The fix: add hypothesis 2 | (n / 2^t) to separator_halving_step,
        // and 2^t | n to halverToSeparator_isSeparator.

        // Perfect halver (ε = 0): sorting network on 2*m wires
        let perfect_halver_fn = |half_m: usize| -> ComparatorNetwork {
            if half_m == 0 { return ComparatorNetwork { n: 0, comparators: vec![] }; }
            let nn = 2 * half_m;
            let mut comps = Vec::new();
            for _pass in 0..nn {
                let mut i = 0;
                while i + 1 < nn { comps.push(Comparator { i, j: i + 1 }); i += 2; }
                i = 1;
                while i + 1 < nn { comps.push(Comparator { i, j: i + 1 }); i += 2; }
            }
            ComparatorNetwork { n: nn, comparators: comps }
        };

        println!("  --- Odd n, t=0: should FAIL (chunkSize odd) ---");
        for n in [3, 5, 7, 9, 11] {
            let net = halver_at_level(n, &perfect_halver_fn, 0);
            let chunk_size = n;
            let half_chunk = chunk_size / 2;

            // Craft w₁ with value 0 at uncovered position
            let uncovered = 2 * half_chunk;
            let mut w1: Vec<usize> = (0..n).collect();
            w1.swap(0, uncovered);
            // Apply halver
            net.exec(&mut w1);
            let viol = check_sep_initial(&w1, n, 0.5, 0.0);
            let status = if viol.is_some() { "FAIL (expected)" } else { "OK (unexpected!)" };
            println!("    n={n}: chunk={chunk_size}, 2*half={}, uncovered={uncovered} → {status}",
                2 * half_chunk);
        }

        println!("\n  --- Even n, t=0: should PASS (chunkSize even, 2 | n) ---");
        for n in [2, 4, 6, 8, 10, 12, 16, 32] {
            let net = halver_at_level(n, &perfect_halver_fn, 0);
            let mut found = false;
            let mut rng: u64 = 42 + n as u64;
            for _ in 0..10000 {
                let mut perm: Vec<usize> = (0..n).collect();
                for i in (1..n).rev() {
                    rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
                    let j = rng as usize % (i + 1);
                    perm.swap(i, j);
                }
                net.exec(&mut perm);
                if check_sep_initial(&perm, n, 0.5, 0.0).is_some()
                    || check_sep_final(&perm, n, 0.5, 0.0).is_some() {
                    found = true;
                    break;
                }
            }
            println!("    n={n}: 2|{n}={} → {}", n % 2 == 0,
                if found { "FAIL" } else { "OK" });
        }

        println!("\n  --- Higher levels: 2^t | n → OK, otherwise may fail ---");
        for &(n, t) in &[(12, 2), (24, 3), (48, 4), (10, 1), (14, 1), (6, 1)] {
            let chunk_size = n / (1 << t);
            let even_chunk = chunk_size % 2 == 0;
            let divides = n % (1 << (t + 1)) == 0;

            // Build iterated net for t+1 levels
            let halver_fn_ref = &perfect_halver_fn;
            let net = halver_network(n, halver_fn_ref, t + 1);
            let gamma = 1.0 / (1u64 << (t + 1)) as f64;

            let mut found = false;
            // Try all permutations for small n, random for larger
            if n <= 12 {
                let mut perm: Vec<usize> = (0..n).collect();
                loop {
                    let mut v = perm.clone();
                    net.exec(&mut v);
                    if check_sep_initial(&v, n, gamma, 0.0).is_some() {
                        found = true;
                        break;
                    }
                    if !next_permutation(&mut perm) { break; }
                }
            } else {
                let mut rng: u64 = 42 + n as u64 + t as u64 * 100;
                for _ in 0..50000 {
                    let mut perm: Vec<usize> = (0..n).collect();
                    for i in (1..n).rev() {
                        rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
                        let j = rng as usize % (i + 1);
                        perm.swap(i, j);
                    }
                    net.exec(&mut perm);
                    if check_sep_initial(&perm, n, gamma, 0.0).is_some() {
                        found = true;
                        break;
                    }
                }
            }
            println!("    n={n}, t={t}: chunk={chunk_size}, even={even_chunk}, 2^(t+1)|n={divides} → {}",
                if found { "FAIL" } else { "OK" });
        }
    }

    // ──────────────────────────────────────────────────────────
    // Part E: Sublemma tests for separator_halving_step
    //
    // Tests the two key counting sublemmas:
    // E1. halverAtLevel_chunk0_count_eq: count of values < k at positions < C
    //     is preserved by halverAtLevel
    // E2. halverAtLevel_near_outsider_le: count of values < k at positions
    //     in [H, C) is ≤ ε₁ · a where a = count of chunk-0 values < k
    // ──────────────────────────────────────────────────────────
    println!("\n\n=== Part E: Sublemma tests for separator_halving_step ===\n");

    // Perfect halver: odd-even transposition sort (enough passes for small sizes)
    let perfect_halver_fn_e = |half_m: usize| -> ComparatorNetwork {
        let nn = 2 * half_m;
        let mut comparators = Vec::new();
        for _pass in 0..nn {
            let mut i = 0;
            while i + 1 < nn { comparators.push(Comparator { i, j: i + 1 }); i += 2; }
            i = 1;
            while i + 1 < nn { comparators.push(Comparator { i, j: i + 1 }); i += 2; }
        }
        ComparatorNetwork { n: nn, comparators }
    };

    {
        println!("--- E1: halverAtLevel_chunk0_count_eq ---");
        println!("  Count of values < k at positions < C preserved by halverAtLevel\n");

        let mut all_ok = true;
        for &n in &[8, 16, 32, 64, 128] {
            for t in 0..5 {
                let c = n / (1 << t);
                if c < 2 || c % 2 != 0 { continue; }
                if (1 << t) > n { break; }

                let halver_fn_ref = &perfect_halver_fn_e;
                let level_net = halver_at_level(n, halver_fn_ref, t);

                let mut rng: u64 = 77 + n as u64 * 13 + t as u64 * 7;
                let mut ok = true;
                for _ in 0..5000 {
                    // Random permutation as w₁
                    let mut w1: Vec<usize> = (0..n).collect();
                    for i in (1..n).rev() {
                        rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
                        let j = rng as usize % (i + 1);
                        w1.swap(i, j);
                    }
                    let mut w2 = w1.clone();
                    level_net.exec(&mut w2);

                    // Check: for all k, count of values < k at positions < C is preserved
                    for k in 0..=n {
                        let count_w1 = (0..c).filter(|&pos| w1[pos] < k).count();
                        let count_w2 = (0..c).filter(|&pos| w2[pos] < k).count();
                        if count_w1 != count_w2 {
                            println!("  FAIL: n={n}, t={t}, k={k}: w1_count={count_w1}, w2_count={count_w2}");
                            ok = false;
                            all_ok = false;
                            break;
                        }
                    }
                    if !ok { break; }
                }
                if ok {
                    print!("  n={n}, t={t}, C={c}: OK  ");
                }
            }
            println!();
        }
        println!("{}", if all_ok { "  All E1 tests passed!" } else { "  SOME E1 TESTS FAILED!" });
    }

    println!();
    {
        println!("--- E2: halverAtLevel_near_outsider_le ---");
        println!("  Near outsiders ≤ ε₁ · a (with perfect halver, ε₁=0 → must be 0)\n");

        let mut all_ok = true;
        for &n in &[8, 16, 32, 64, 128] {
            for t in 0..5 {
                let c = n / (1 << t);
                if c < 2 || c % 2 != 0 { continue; }
                if (1 << t) > n { break; }
                let h = c / 2;

                let halver_fn_ref = &perfect_halver_fn_e;
                let level_net = halver_at_level(n, halver_fn_ref, t);

                let mut rng: u64 = 99 + n as u64 * 17 + t as u64 * 11;
                let mut worst_ratio: f64 = 0.0;
                let mut fail = false;
                for _ in 0..5000 {
                    let mut w1: Vec<usize> = (0..n).collect();
                    for i in (1..n).rev() {
                        rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
                        let j = rng as usize % (i + 1);
                        w1.swap(i, j);
                    }
                    let mut w2 = w1.clone();
                    level_net.exec(&mut w2);

                    // For each k ≤ H: count near outsiders and chunk-0 small values
                    for k in 0..=h {
                        let a = (0..c).filter(|&pos| w1[pos] < k).count();
                        let near = (h..c).filter(|&pos| w2[pos] < k).count();
                        // For perfect halver (ε₁=0): near should be 0
                        if near > 0 {
                            println!("  FAIL: n={n}, t={t}, k={k}: near={near}, a={a}");
                            fail = true;
                            all_ok = false;
                            break;
                        }
                        // Track worst ratio for imperfect halvers (here always 0)
                        if a > 0 {
                            let ratio = near as f64 / a as f64;
                            if ratio > worst_ratio { worst_ratio = ratio; }
                        }
                    }
                    if fail { break; }
                }
                if !fail {
                    print!("  n={n}, t={t}, C={c}, H={h}: OK (worst_ratio={worst_ratio:.4})  ");
                }
            }
            println!();
        }

        // Also test with imperfect halver (expander-based) if graph data available
        println!("\n  With expander halver (if available):");
        let graph_path = "data/1728/graph.bin";
        if std::path::Path::new(graph_path).exists() {
            let g = RegularGraph::from_binary_file(graph_path, 1728, 12);
            let exp_halver = expander_halver(&g);
            let exp_halver_fn = |_m: usize| -> ComparatorNetwork {
                // This halver is for m=1728 specifically. For testing, we need
                // to test at the right size. Use a generic perfect halver for
                // sizes ≠ 1728 and the expander halver for size 1728.
                ComparatorNetwork { n: 2 * _m, comparators: Vec::new() }
            };
            // Test with n = 2*1728 = 3456, t=0 (chunk = 3456, halfChunk = 1728)
            let n = 2 * 1728;
            let t = 0;
            let c = n;
            let h = c / 2; // = 1728
            // Build halverAtLevel manually with the expander halver at offset 0
            let mut level_comps = Vec::new();
            for comp in &exp_halver.comparators {
                level_comps.push(Comparator { i: comp.i, j: comp.j });
            }
            let level_net = ComparatorNetwork { n, comparators: level_comps };

            let mut rng: u64 = 12345;
            let mut worst_ratio: f64 = 0.0;
            let trials = 1000;
            for _ in 0..trials {
                let mut w1: Vec<usize> = (0..n).collect();
                for i in (1..n).rev() {
                    rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
                    let j = rng as usize % (i + 1);
                    w1.swap(i, j);
                }
                let mut w2 = w1.clone();
                level_net.exec(&mut w2);

                for k in (0..=h).step_by(h.max(1) / 20 + 1) {
                    let a = (0..c).filter(|&pos| w1[pos] < k).count();
                    let near = (h..c).filter(|&pos| w2[pos] < k).count();
                    if a > 0 {
                        let ratio = near as f64 / a as f64;
                        if ratio > worst_ratio { worst_ratio = ratio; }
                    }
                }
            }
            println!("  n={n}, t={t}: worst near/a ratio = {worst_ratio:.4} (should be ≤ ε₁)");
        } else {
            println!("  (skipped: {graph_path} not found)");
        }

        println!("\n{}", if all_ok { "  All E2 tests passed!" } else { "  SOME E2 TESTS FAILED!" });
    }

    println!("\n=== All tests complete ===");
}

fn next_permutation(arr: &mut Vec<usize>) -> bool {
    let n = arr.len();
    if n <= 1 { return false; }
    let mut i = n - 1;
    while i > 0 && arr[i - 1] >= arr[i] { i -= 1; }
    if i == 0 { return false; }
    let mut j = n - 1;
    while arr[j] <= arr[i - 1] { j -= 1; }
    arr.swap(i - 1, j);
    arr[i..].reverse();
    true
}
