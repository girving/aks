#!/usr/bin/env -S cargo +nightly -Zscript
//! Simulation of Seiferas's bag-tree sorting network invariant.
//! Tests the four-clause invariant and rebagging procedure.
//!
//! Reference: Seiferas (2009), "Sorting networks of logarithmic depth,
//! further simplified", Sections 2-5.

use std::collections::BTreeMap;

/// Parameters for the sorting network construction
#[derive(Clone, Debug)]
struct Params {
    a: f64,      // A > 1: capacity growth per tree level
    nu: f64,     // ν ∈ (0,1): capacity decay per stage
    lambda: f64,  // λ ∈ (0,1/2): separator fringe fraction
    eps: f64,     // ε > 0: separator error rate
}

/// Separator model for testing
#[derive(Clone, Copy, Debug)]
enum SepModel {
    /// Perfect sort (no errors)
    Perfect,
    /// Old model: sort then swap ceil(ε·n) random pairs.
    /// Always swaps ≥ 1 pair even for small bags — unrealistic.
    RandomSwap,
    /// Formal stochastic model: sort, then independently displace each item with prob ε.
    /// For any quantile of size m, expected ε·m items displaced.
    /// Naturally handles small bags: usually 0 displacements when m·ε < 1.
    /// This models the (λ, ε)-separator definition: for all γ' ≤ λ, at most
    /// ε·γ'·n of the ⌊γ'·n⌋ smallest items are displaced beyond position ⌊λ·n⌋.
    Formal,
    /// Deterministic adversarial model: introduces exactly ⌊ε·k⌋ errors.
    /// For small bags (⌊ε·m/2⌋ = 0): NO errors (perfect sort), matching real separators.
    /// For large bags: maximizes errors within the separator definition's bounds.
    /// Two error types:
    /// 1. Halving errors: ⌊ε·half⌋ items from each half placed in wrong half
    ///    (items near the midpoint, maximizing sibling leakage)
    /// 2. Fringe leakage: ⌊ε·F⌋ items from each fringe leak into middle
    ///    (items near fringe boundary, maximizing wrong-child placement)
    /// This is the WORST CASE — if invariant holds here, it holds for any valid separator.
    Adversarial {
        lambda: f64,  // need λ to compute fringe size
    },
}

/// Apply separator model to items in a bag.
/// Sorts by rank, then introduces errors according to the model.
fn apply_separator(items: &mut Vec<usize>, model: SepModel, eps: f64, rng: &mut Rng) {
    items.sort();
    match model {
        SepModel::Perfect => {}
        SepModel::RandomSwap => {
            if items.len() > 1 {
                let num_swaps = (eps * items.len() as f64).ceil() as usize;
                for _ in 0..num_swaps {
                    let i = rng.next_usize(items.len());
                    let j = rng.next_usize(items.len());
                    items.swap(i, j);
                }
            }
        }
        SepModel::Formal => {
            let n = items.len();
            if n <= 1 { return; }
            // Each item independently displaced with probability ε
            let mut displaced: Vec<usize> = Vec::new();
            for i in 0..n {
                if rng.next_f64() < eps {
                    displaced.push(i);
                }
            }
            if displaced.len() < 2 { return; }
            // Fisher-Yates shuffle of values at displaced positions
            let mut values: Vec<usize> = displaced.iter().map(|&i| items[i]).collect();
            for i in (1..values.len()).rev() {
                let j = rng.next_usize(i + 1);
                values.swap(i, j);
            }
            for (k, &pos) in displaced.iter().enumerate() {
                items[pos] = values[k];
            }
        }
        SepModel::Adversarial { lambda } => {
            let m = items.len();
            if m <= 1 { return; }

            let fringe = (lambda * m as f64).floor() as usize;
            let middle_start = fringe;
            let middle_end = m.saturating_sub(fringe);
            let middle_size = middle_end.saturating_sub(middle_start);
            let half = middle_size / 2;

            // 1. Halving errors: swap ⌊ε·half⌋ items between left and right middle.
            //    Swap items nearest the midpoint (worst case for sibling leakage).
            let halving_errors = (eps * half as f64).floor() as usize;
            if halving_errors > 0 && half > 0 {
                for k in 0..halving_errors.min(half) {
                    let left_pos = middle_start + half - 1 - k;
                    let right_pos = middle_start + half + k;
                    if left_pos < right_pos && right_pos < middle_end {
                        items.swap(left_pos, right_pos);
                    }
                }
            }

            // 2. Fringe leakage: swap ⌊ε·F⌋ items from each fringe into middle.
            //    From left fringe: items closest to boundary (highest ranked in fringe)
            //    go into the LEFT middle (just past the fringe boundary).
            //    From right fringe: items closest to boundary go into RIGHT middle.
            let fringe_errors = (eps * fringe as f64).floor() as usize;
            if fringe_errors > 0 && fringe > 0 && middle_size > 2 * halving_errors {
                // Left fringe → left middle (avoiding halving error zone)
                let avail = (half.saturating_sub(halving_errors)).min(fringe_errors);
                for k in 0..avail {
                    items.swap(fringe - 1 - k, middle_start + k);
                }
                // Right fringe → right middle
                for k in 0..avail {
                    let right_fringe_pos = middle_end + k;
                    let right_mid_pos = middle_end - 1 - k;
                    if right_fringe_pos < m && right_mid_pos >= middle_start + half {
                        items.swap(right_fringe_pos, right_mid_pos);
                    }
                }
            }
        }
    }
}

impl Params {
    fn seiferas_preview() -> Self {
        Params { a: 10.0, nu: 0.65, lambda: 1.0/99.0, eps: 1.0/99.0 }
    }

    /// Capacity of a bag at given level after t stages: n·ν^t·A^level
    fn capacity(&self, n: usize, t: usize, level: usize) -> f64 {
        (n as f64) * self.nu.powi(t as i32) * self.a.powi(level as i32)
    }

    /// Constraint C3: ν ≥ 4λA + 5/(2A)
    fn check_c3(&self) -> bool {
        self.nu >= 4.0 * self.lambda * self.a + 5.0 / (2.0 * self.a)
    }

    /// Constraint C4 for j > 1: 2Aε + 1/A ≤ ν
    fn check_c4_j_gt_1(&self) -> bool {
        2.0 * self.a * self.eps + 1.0 / self.a <= self.nu
    }

    /// Constraint C4 for j = 1 (master constraint)
    fn check_c4_j_eq_1(&self) -> bool {
        let a = self.a;
        let e = self.eps;
        let l = self.lambda;
        let lhs = 2.0*l*e*a + e*l/a + e/(2.0*a)
            + 2.0*l*e*a / (1.0 - (2.0*e*a).powi(2))
            + 1.0 / (8.0*a*a*a - 2.0*a);
        lhs <= l * self.nu
    }

    fn check_all_constraints(&self) -> bool {
        self.check_c3() && self.check_c4_j_gt_1() && self.check_c4_j_eq_1()
    }

    fn print_constraints(&self) {
        let a = self.a;
        let e = self.eps;
        let l = self.lambda;
        println!("  C3: ν ≥ 4λA + 5/(2A) = {:.6}, ν = {:.6} → {}",
            4.0*l*a + 5.0/(2.0*a), self.nu, self.check_c3());
        println!("  C4(j>1): 2Aε + 1/A = {:.6} ≤ ν = {:.6} → {}",
            2.0*a*e + 1.0/a, self.nu, self.check_c4_j_gt_1());
        let lhs = 2.0*l*e*a + e*l/a + e/(2.0*a)
            + 2.0*l*e*a / (1.0 - (2.0*e*a).powi(2))
            + 1.0 / (8.0*a*a*a - 2.0*a);
        println!("  C4(j=1): lhs = {:.6} ≤ λν = {:.6} → {}",
            lhs, l * self.nu, self.check_c4_j_eq_1());
    }
}

/// Simple LCG random number generator (no external deps)
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Rng(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn next_usize(&mut self, bound: usize) -> usize {
        (self.next_u64() % bound as u64) as usize
    }
    fn next_f64(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 / (1u64 << 53) as f64
    }
}

/// State of the bag tree
struct BagTree {
    n: usize,
    max_level: usize,  // deepest level (leaves = pairs)
    /// (level, idx) -> sorted ranks of items currently in this bag
    bags: BTreeMap<(usize, usize), Vec<usize>>,
}

#[derive(Debug)]
struct InvariantViolation {
    clause: usize,
    detail: String,
}

impl BagTree {
    fn new(n: usize) -> Self {
        assert!(n.is_power_of_two() && n >= 4);
        let max_level = n.trailing_zeros() as usize - 1;
        let mut bags = BTreeMap::new();
        // Initially all items in root
        bags.insert((0, 0), (0..n).collect());
        BagTree { n, max_level, bags }
    }

    /// Native bag index for item with sorted rank r at given level.
    /// nativeBagIdx(n, level, r) = r / (n / 2^level)
    fn native_bag_idx(&self, level: usize, rank: usize) -> usize {
        let chunk_size = self.n >> level;
        if chunk_size == 0 { rank } else { rank / chunk_size }
    }

    /// Is item with given rank j-strange at bag (level, idx)?
    /// Shifted definition (Seiferas): diverges at level-(j-1).
    ///   j=1: not native to this bag. j=2: not native to parent.
    fn is_j_stranger(&self, rank: usize, level: usize, idx: usize, j: usize) -> bool {
        if j == 0 || j > level { return false; }
        let check_level = level - (j - 1);
        let check_idx = idx >> (j - 1);
        self.native_bag_idx(check_level, rank) != check_idx
    }

    /// Old (unshifted) definition for comparison: diverges at level-j.
    fn is_j_stranger_unshifted(&self, rank: usize, level: usize, idx: usize, j: usize) -> bool {
        if j == 0 || j > level { return false; }
        let ancestor_level = level - j;
        let ancestor_idx = idx >> j;
        self.native_bag_idx(ancestor_level, rank) != ancestor_idx
    }

    /// Count j-strangers among given items at bag (level, idx)
    fn j_stranger_count(&self, items: &[usize], level: usize, idx: usize, j: usize) -> usize {
        items.iter().filter(|&&rank| self.is_j_stranger(rank, level, idx, j)).count()
    }

    fn j_stranger_count_unshifted(&self, items: &[usize], level: usize, idx: usize, j: usize) -> usize {
        items.iter().filter(|&&rank| self.is_j_stranger_unshifted(rank, level, idx, j)).count()
    }

    /// Total items across all bags
    fn total_items(&self) -> usize {
        self.bags.values().map(|v| v.len()).sum()
    }

    /// Check all four clauses of the invariant at stage t.
    /// Returns Ok(()) if all hold, Err with first violation otherwise.
    fn check_invariant(&self, params: &Params, t: usize) -> Result<(), InvariantViolation> {
        // Clause 1: alternating levels empty
        // Convention: levels where (t + level) % 2 != 0 are empty.
        // At t=0: level 0 (root) is nonempty, odd levels empty. ✓
        for (&(level, idx), items) in &self.bags {
            if (t + level) % 2 != 0 && !items.is_empty() {
                return Err(InvariantViolation {
                    clause: 1,
                    detail: format!("bag ({},{}) has {} items but (t+level)%2={} (should be empty)",
                        level, idx, items.len(), (t + level) % 2),
                });
            }
        }

        // Clause 2: uniform size at each active level
        for level in 0..=self.max_level {
            if (t + level) % 2 != 0 { continue; } // skip empty levels
            let num_bags = 1usize << level;
            let sizes: Vec<usize> = (0..num_bags)
                .map(|idx| self.bags.get(&(level, idx)).map_or(0, |v| v.len()))
                .collect();
            if !sizes.windows(2).all(|w| w[0] == w[1]) {
                return Err(InvariantViolation {
                    clause: 2,
                    detail: format!("level {} non-uniform: sizes {:?}", level, &sizes[..sizes.len().min(8)]),
                });
            }
        }

        // Clause 3: capacity bound
        for (&(level, _idx), items) in &self.bags {
            if items.is_empty() { continue; }
            let b = params.capacity(self.n, t, level);
            if items.len() as f64 > b + 0.001 {
                return Err(InvariantViolation {
                    clause: 3,
                    detail: format!("bag ({},{}) has {} items > capacity {:.2}",
                        level, _idx, items.len(), b),
                });
            }
        }

        // Clause 4: stranger bounds
        for (&(level, idx), items) in &self.bags {
            if items.is_empty() { continue; }
            let b = params.capacity(self.n, t, level);
            for j in 1..=level {
                let count = self.j_stranger_count(items, level, idx, j);
                let bound = params.lambda * params.eps.powi(j as i32 - 1) * b;
                if count as f64 > bound + 0.001 {
                    return Err(InvariantViolation {
                        clause: 4,
                        detail: format!("bag ({},{}) has {} {}-strangers > bound {:.4} (λε^{}·b)",
                            level, idx, count, j, bound, j-1),
                    });
                }
            }
        }

        Ok(())
    }

    /// Perform one stage of the separation-rebagging procedure.
    /// At stage t, processes all nonempty bags (parity t%2) and
    /// redistributes to bags at parity (t+1)%2.
    ///
    /// use_eps: if true, apply ε-approximate separator; if false, perfect sort.
    fn do_stage(&mut self, params: &Params, t: usize, model: SepModel, rng: &mut Rng) {
        let mut new_bags: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();

        // Collect all active bags
        let active: Vec<((usize, usize), Vec<usize>)> = self.bags.iter()
            .filter(|(_, items)| !items.is_empty())
            .map(|(&k, v)| (k, v.clone()))
            .collect();

        for ((level, idx), mut items) in active {
            // Step 1: Apply separator
            apply_separator(&mut items, model, params.eps, rng);

            let b = params.capacity(self.n, t, level);
            let kick_per_side = (params.lambda * b).floor() as usize;
            let has_parent = level > 0;
            let has_children = level < self.max_level;

            if !has_parent && !has_children {
                // Root is also leaf (n=2 case, shouldn't happen with n≥4)
                panic!("Root is leaf, n must be ≥ 4");
            }

            if !has_parent {
                // Root: no kickback, split all to children
                let mut remaining = items;
                // Root should always have even count (n is power of 2,
                // and items at root are always even by construction)
                if remaining.len() % 2 == 1 {
                    // Shouldn't happen at root, but handle gracefully
                    // This would be a bug in the construction
                    panic!("Odd items at root: {}", remaining.len());
                }
                let mid = remaining.len() / 2;
                let right: Vec<_> = remaining.split_off(mid);
                new_bags.entry((level + 1, 2 * idx)).or_default().extend(remaining);
                new_bags.entry((level + 1, 2 * idx + 1)).or_default().extend(right);
            } else if !has_children {
                // Leaf: all items go to parent
                // Feasibility check: items ≤ 2⌊λb⌋ + 1
                if items.len() > 2 * kick_per_side + 1 {
                    eprintln!("WARNING: Leaf ({},{}) infeasible: {} items > 2⌊λb⌋+1 = {}",
                        level, idx, items.len(), 2 * kick_per_side + 1);
                }
                new_bags.entry((level - 1, idx / 2)).or_default().extend(items);
            } else {
                // Internal node: kick back to parent, split rest to children
                let total = items.len();
                let kick_small = kick_per_side.min(total);
                let kick_large = kick_per_side.min(total.saturating_sub(kick_small));

                // Items going to parent: smallest kick_small + largest kick_large
                let parent_entry = new_bags.entry((level - 1, idx / 2)).or_default();
                for &item in &items[..kick_small] {
                    parent_entry.push(item);
                }
                for &item in &items[total - kick_large..] {
                    parent_entry.push(item);
                }

                // Middle items
                let mut middle: Vec<usize> = items[kick_small..total - kick_large].to_vec();

                // If odd, kick one more to parent
                if middle.len() % 2 == 1 {
                    let mid_idx = middle.len() / 2;
                    let mid_item = middle.remove(mid_idx);
                    parent_entry.push(mid_item);
                }

                // Split remaining to children
                let half = middle.len() / 2;
                let right: Vec<_> = middle.split_off(half);
                new_bags.entry((level + 1, 2 * idx)).or_default().extend(middle);
                new_bags.entry((level + 1, 2 * idx + 1)).or_default().extend(right);
            }
        }

        self.bags = new_bags;
    }

    /// Print summary of current state
    fn print_summary(&self, t: usize) {
        let mut by_level: BTreeMap<usize, (usize, usize)> = BTreeMap::new(); // level -> (count, total_items)
        for (&(level, _), items) in &self.bags {
            if !items.is_empty() {
                let entry = by_level.entry(level).or_default();
                entry.0 += 1;
                entry.1 += items.len();
            }
        }
        print!("  t={}: ", t);
        for (level, (count, total)) in &by_level {
            print!("L{}:{}bags/{}items  ", level, count, total);
        }
        println!("(total={})", self.total_items());
    }

    /// Count all strangers at a given level
    fn total_strangers_at_level(&self, level: usize) -> usize {
        let num_bags = 1usize << level;
        let mut total = 0;
        for idx in 0..num_bags {
            if let Some(items) = self.bags.get(&(level, idx)) {
                total += self.j_stranger_count(items, level, idx, 1);
            }
        }
        total
    }

    /// Check if all items are in their native leaf bags
    fn all_native(&self) -> bool {
        for (&(level, idx), items) in &self.bags {
            for &rank in items {
                if self.native_bag_idx(level, rank) != idx {
                    return false;
                }
            }
        }
        true
    }

    /// Shifted j-stranger definition matching Seiferas's convention.
    /// j-stranger at (level, idx) iff nativeBagIdx(n, level-(j-1), rank) != idx/2^(j-1).
    ///   j=1: not native to this bag (nativeBagIdx(n, level, rank) != idx)
    ///   j=2: not native to parent (nativeBagIdx(n, level-1, rank) != idx/2)
    /// Same as is_j_stranger (kept for backward compatibility with tests).
    fn is_j_stranger_shifted(&self, rank: usize, level: usize, idx: usize, j: usize) -> bool {
        self.is_j_stranger(rank, level, idx, j)
    }

    fn j_stranger_count_shifted(&self, items: &[usize], level: usize, idx: usize, j: usize) -> usize {
        self.j_stranger_count(items, level, idx, j)
    }

    /// Map from rank to (level, idx) for all items currently in bags.
    fn item_locations(&self) -> Vec<Option<(usize, usize)>> {
        let mut locs = vec![None; self.n];
        for (&(level, idx), items) in &self.bags {
            for &rank in items {
                locs[rank] = Some((level, idx));
            }
        }
        locs
    }

    /// Check invariant using shifted j-stranger definition.
    fn check_invariant_shifted(&self, params: &Params, t: usize) -> Result<(), InvariantViolation> {
        // Clauses 1-3 identical to check_invariant
        for (&(level, idx), items) in &self.bags {
            if (t + level) % 2 != 0 && !items.is_empty() {
                return Err(InvariantViolation {
                    clause: 1,
                    detail: format!("bag ({},{}) nonempty at wrong parity", level, idx),
                });
            }
        }
        for level in 0..=self.max_level {
            if (t + level) % 2 != 0 { continue; }
            let num_bags = 1usize << level;
            let sizes: Vec<usize> = (0..num_bags)
                .map(|idx| self.bags.get(&(level, idx)).map_or(0, |v| v.len()))
                .collect();
            if !sizes.windows(2).all(|w| w[0] == w[1]) {
                return Err(InvariantViolation {
                    clause: 2,
                    detail: format!("level {} non-uniform: {:?}", level, &sizes[..sizes.len().min(8)]),
                });
            }
        }
        for (&(level, _idx), items) in &self.bags {
            if items.is_empty() { continue; }
            let b = params.capacity(self.n, t, level);
            if items.len() as f64 > b + 0.001 {
                return Err(InvariantViolation {
                    clause: 3,
                    detail: format!("bag ({},{}) {} items > cap {:.2}", level, _idx, items.len(), b),
                });
            }
        }
        // Clause 4: shifted stranger bounds
        for (&(level, idx), items) in &self.bags {
            if items.is_empty() { continue; }
            let b = params.capacity(self.n, t, level);
            for j in 1..=level {
                let count = self.j_stranger_count_shifted(items, level, idx, j);
                let bound = params.lambda * params.eps.powi(j as i32 - 1) * b;
                if count as f64 > bound + 0.001 {
                    return Err(InvariantViolation {
                        clause: 4,
                        detail: format!("shifted: ({},{}) {} {}-strangers > {:.4}",
                            level, idx, count, j, bound),
                    });
                }
            }
        }
        Ok(())
    }
}

/// Run simulation with given parameters and return (stages_run, final_result)
fn run_simulation(
    n: usize,
    params: &Params,
    max_stages: usize,
    model: SepModel,
    seed: u64,
    verbose: bool,
) -> Result<usize, (usize, InvariantViolation)> {
    let mut tree = BagTree::new(n);
    let mut rng = Rng::new(seed);

    // Check initial invariant
    if let Err(v) = tree.check_invariant(params, 0) {
        return Err((0, v));
    }
    if verbose { tree.print_summary(0); }

    for t in 0..max_stages {
        tree.do_stage(params, t, model, &mut rng);

        if let Err(v) = tree.check_invariant(params, t + 1) {
            if verbose {
                tree.print_summary(t + 1);
                println!("  VIOLATION at t={}: clause {}: {}", t+1, v.clause, v.detail);
            }
            return Err((t + 1, v));
        }

        if verbose { tree.print_summary(t + 1); }

        // Check convergence: leaf capacity < 1/λ (Seiferas stopping criterion)
        let leaf_cap = params.capacity(n, t + 1, tree.max_level);
        let threshold = 1.0 / params.lambda;
        if leaf_cap < threshold {
            if verbose {
                println!("  Converged at t={}: leaf capacity {:.4} < 1/λ = {:.1}",
                    t+1, leaf_cap, threshold);
            }
            return Ok(t + 1);
        }
    }

    Ok(max_stages)
}

fn test_seiferas_params() {
    println!("=== Test 1: Seiferas preview parameters (A=10, λ=ε=1/99, ν=0.65) ===");
    let params = Params::seiferas_preview();
    params.print_constraints();
    // Note: C3 is barely violated (0.654 > 0.65), but floor effects may save it

    for &n in &[8, 16, 32, 64, 128, 256, 512, 1024] {
        let max_stages = 200;
        match run_simulation(n, &params, max_stages, SepModel::Perfect, 42, false) {
            Ok(stages) => println!("  n={:5}: OK, converged in {} stages (perfect sep)", n, stages),
            Err((t, v)) => println!("  n={:5}: FAIL at t={}, clause {}: {}", n, t, v.clause, v.detail),
        }
    }

    // Also test with ν adjusted to exactly satisfy C3
    let nu_c3 = 4.0 * (1.0/99.0) * 10.0 + 5.0 / 20.0 + 0.001;
    println!("\n  With ν={:.6} (just above C3 threshold):", nu_c3);
    let params2 = Params { nu: nu_c3, ..params };
    params2.print_constraints();
    for &n in &[64, 256, 1024] {
        match run_simulation(n, &params2, 200, SepModel::Perfect, 42, false) {
            Ok(stages) => println!("  n={:5}: OK, converged in {} stages", n, stages),
            Err((t, v)) => println!("  n={:5}: FAIL at t={}, clause {}: {}", n, t, v.clause, v.detail),
        }
    }
}

fn test_approximate_separator() {
    println!("\n=== Test 2: Approximate separator (ε > 0) ===");
    let params = Params::seiferas_preview();

    // Show first failure for each n
    for &n in &[16, 64, 256, 1024] {
        let mut ok = 0;
        let mut fail_counts = [0usize; 5]; // clause 1-4 + other
        let mut first_fail: Option<(usize, InvariantViolation)> = None;
        for seed in 0..20 {
            match run_simulation(n, &params, 200, SepModel::RandomSwap, seed, false) {
                Ok(_) => ok += 1,
                Err((t, v)) => {
                    let idx = if v.clause <= 4 { v.clause } else { 0 };
                    fail_counts[idx] += 1;
                    if first_fail.is_none() { first_fail = Some((t, v)); }
                }
            }
        }
        print!("  n={:5}: {}/20 ok", n, ok);
        if let Some((t, v)) = first_fail {
            print!(" | first fail: t={}, clause {}: {}", t, v.clause, &v.detail[..v.detail.len().min(60)]);
        }
        println!();
    }
}

fn test_constraint_violations() {
    println!("\n=== Test 3: Parameter constraint violations ===");

    // Test C3 violation: ν < 4λA + 5/(2A)
    {
        let threshold = 4.0 * (1.0/99.0) * 10.0 + 5.0 / 20.0;
        let params = Params { a: 10.0, nu: threshold - 0.05, lambda: 1.0/99.0, eps: 1.0/99.0 };
        println!("  C3 violation (ν={:.4} < {:.4}):", params.nu, threshold);
        params.print_constraints();
        for &n in &[64, 256, 1024] {
            match run_simulation(n, &params, 100, SepModel::Perfect, 42, false) {
                Ok(stages) => println!("    n={}: OK (converged in {} stages) - no violation found!", n, stages),
                Err((t, v)) => println!("    n={}: FAIL at t={}, clause {}: {}", n, t, v.clause, v.detail),
            }
        }
    }

    // Test C4(j>1) violation: 2Aε + 1/A > ν
    {
        let threshold = 2.0 * 10.0 * (1.0/99.0) + 1.0/10.0;
        let params = Params { a: 10.0, nu: threshold - 0.05, lambda: 1.0/99.0, eps: 1.0/99.0 };
        println!("  C4(j>1) violation (ν={:.4} < {:.4}):", params.nu, threshold);
        params.print_constraints();
        for &n in &[64, 256, 1024] {
            match run_simulation(n, &params, 100, SepModel::RandomSwap, 42, false) {
                Ok(stages) => println!("    n={}: OK (converged in {} stages) - no violation found!", n, stages),
                Err((t, v)) => println!("    n={}: FAIL at t={}, clause {}: {}", n, t, v.clause, v.detail),
            }
        }
    }
}

fn test_various_parameters() {
    println!("\n=== Test 4: Various parameter settings ===");

    let test_cases = vec![
        ("A=5, λ=ε=1/50, ν=0.65", Params { a: 5.0, nu: 0.65, lambda: 1.0/50.0, eps: 1.0/50.0 }),
        ("A=20, λ=ε=1/200, ν=0.55", Params { a: 20.0, nu: 0.55, lambda: 1.0/200.0, eps: 1.0/200.0 }),
        ("A=3, λ=ε=1/30, ν=0.8", Params { a: 3.0, nu: 0.8, lambda: 1.0/30.0, eps: 1.0/30.0 }),
        ("A=2, λ=ε=1/20, ν=0.9", Params { a: 2.0, nu: 0.9, lambda: 1.0/20.0, eps: 1.0/20.0 }),
    ];

    for (name, params) in &test_cases {
        let ok = params.check_all_constraints();
        println!("  {}: constraints {}", name, if ok { "✓" } else { "✗" });
        if !ok { params.print_constraints(); }

        for &n in &[64, 256] {
            match run_simulation(n, params, 200, SepModel::Perfect, 42, false) {
                Ok(stages) => println!("    n={}: OK in {} stages", n, stages),
                Err((t, v)) => println!("    n={}: FAIL at t={}, clause {}: {}", n, t, v.clause, v.detail),
            }
        }
    }
}

fn test_initial_invariant_parity() {
    println!("\n=== Test 5: Verify alternating-empty parity convention ===");
    // At t=0: root (level 0) has items. (t+level)%2 = 0 → nonempty.
    // Levels with (t+level)%2 = 1 → empty.
    let tree = BagTree::new(16);
    let params = Params::seiferas_preview();

    // Our convention: (t+level)%2 != 0 → must be empty
    // At t=0, level=0: (0+0)%2 = 0 → can be nonempty ✓
    // At t=0, level=1: (0+1)%2 = 1 → must be empty ✓
    match tree.check_invariant(&params, 0) {
        Ok(()) => println!("  Initial invariant holds ✓"),
        Err(v) => println!("  Initial invariant FAILS: clause {}: {}", v.clause, v.detail),
    }

    // Test that the WRONG parity convention fails
    // If we used (t+level)%2 == 0 → empty, then root at t=0 should be empty, but it has items
    let root_items = tree.bags.get(&(0, 0)).map_or(0, |v| v.len());
    println!("  Root has {} items at t=0", root_items);
    println!("  (0+0)%2 = {} → our convention says nonempty (correct)", (0+0) % 2);
    println!("  Plan's convention '(t+level)%2=0 → empty' would require root empty (WRONG)");
}

fn test_verbose_small() {
    println!("\n=== Test 6: Verbose trace for n=16 ===");
    let params = Params::seiferas_preview();
    match run_simulation(16, &params, 30, SepModel::Perfect, 42, true) {
        Ok(stages) => println!("  Converged in {} stages", stages),
        Err((t, v)) => println!("  FAIL at t={}: clause {}: {}", t, v.clause, v.detail),
    }
}

fn test_stranger_tracking() {
    println!("\n=== Test 7: Stranger counts with approximate separator ===");
    let params = Params::seiferas_preview();
    let n = 256;
    let mut tree = BagTree::new(n);
    let mut rng = Rng::new(123);

    for t in 0..20 {
        tree.do_stage(&params, t, SepModel::RandomSwap, &mut rng);

        // Count strangers at each active level
        let mut stranger_info = Vec::new();
        for level in 0..=tree.max_level {
            if (t + 1 + level) % 2 != 0 { continue; }
            let total_strangers = tree.total_strangers_at_level(level);
            let total_items: usize = (0..(1 << level))
                .map(|idx| tree.bags.get(&(level, idx)).map_or(0, |v| v.len()))
                .sum();
            if total_items > 0 {
                stranger_info.push((level, total_strangers, total_items));
            }
        }

        print!("  t={:2}: ", t + 1);
        for (level, strangers, items) in &stranger_info {
            print!("L{}:{}/{} ({:.1}%)  ", level, strangers, items,
                100.0 * *strangers as f64 / (*items as f64).max(1.0));
        }
        println!();

        let leaf_cap = params.capacity(n, t + 1, tree.max_level);
        if leaf_cap < 1.0 { break; }
    }
}

fn test_uniform_size_detail() {
    println!("\n=== Test 8: Uniform size verification ===");
    let params = Params::seiferas_preview();
    let n = 64;
    let mut tree = BagTree::new(n);
    let mut rng = Rng::new(42);

    for t in 0..15 {
        tree.do_stage(&params, t, SepModel::Perfect, &mut rng);

        // Show sizes at each active level
        print!("  t={:2}: ", t + 1);
        for level in 0..=tree.max_level {
            if (t + 1 + level) % 2 != 0 { continue; }
            let sizes: Vec<usize> = (0..(1 << level))
                .map(|idx| tree.bags.get(&(level, idx)).map_or(0, |v| v.len()))
                .collect();
            let all_same = sizes.windows(2).all(|w| w[0] == w[1]);
            print!("L{}:sz={} (uniform={})  ", level, sizes[0], all_same);
        }
        println!();
    }
}

/// Test the capacity sublemmas: items_from_below ≤ 4λbA + 2, items_from_above ≤ b/(2A)
fn test_capacity_sublemmas() {
    println!("\n=== Test 9: Capacity sublemmas (items from below/above) ===");
    let params = Params::seiferas_preview();

    for &n in &[64, 256, 1024] {
        let mut tree = BagTree::new(n);
        let mut rng = Rng::new(42);

        // Track flows: for each receiving bag, record items_from_below and items_from_above
        let mut max_ratio_below: f64 = 0.0;
        let mut max_ratio_above: f64 = 0.0;
        let mut max_ratio_total: f64 = 0.0;

        let threshold = 1.0 / params.lambda;

        for t in 0..200 {
            // Before processing, record who has what
            let active: Vec<((usize, usize), Vec<usize>)> = tree.bags.iter()
                .filter(|(_, items)| !items.is_empty())
                .map(|(&k, v)| (k, v.clone()))
                .collect();

            // Simulate the stage and track flows
            let mut flows: BTreeMap<(usize, usize), (usize, usize)> = BTreeMap::new(); // (from_below, from_above)

            for ((level, idx), mut items) in active.clone() {
                items.sort();
                let b = params.capacity(n, t, level);
                let kick_per_side = (params.lambda * b).floor() as usize;
                let has_parent = level > 0;
                let has_children = level < tree.max_level;

                if !has_parent {
                    // Root: all to children
                    let mid = items.len() / 2;
                    let from_above = flows.entry((level + 1, 2 * idx)).or_default();
                    from_above.1 += mid;
                    let from_above = flows.entry((level + 1, 2 * idx + 1)).or_default();
                    from_above.1 += items.len() - mid;
                } else if !has_children {
                    // Leaf: all to parent
                    let from_below = flows.entry((level - 1, idx / 2)).or_default();
                    from_below.0 += items.len();
                } else {
                    let kick_small = kick_per_side.min(items.len());
                    let kick_large = kick_per_side.min(items.len().saturating_sub(kick_small));
                    let kicked = kick_small + kick_large;
                    let mut remaining = items.len() - kicked;
                    let mut extra_kick = 0;
                    if remaining % 2 == 1 { extra_kick = 1; remaining -= 1; }

                    let from_below = flows.entry((level - 1, idx / 2)).or_default();
                    from_below.0 += kicked + extra_kick;

                    if remaining > 0 {
                        let half = remaining / 2;
                        let from_above = flows.entry((level + 1, 2 * idx)).or_default();
                        from_above.1 += half;
                        let from_above = flows.entry((level + 1, 2 * idx + 1)).or_default();
                        from_above.1 += remaining - half;
                    }
                }
            }

            // Check sublemma bounds for each receiving bag
            for (&(level, _idx), &(from_below, from_above)) in &flows {
                let b = params.capacity(n, t + 1, level);
                let b_prev = params.capacity(n, t, level);

                // items_from_below ≤ 4λbA + 2 (using PREVIOUS capacity for children)
                // children have capacity b_prev * A
                let below_bound = 4.0 * params.lambda * b_prev * params.a + 2.0;
                if from_below > 0 && below_bound > 0.0 {
                    let ratio = from_below as f64 / below_bound;
                    if ratio > max_ratio_below { max_ratio_below = ratio; }
                }

                // items_from_above ≤ b_prev/(2A) (using PREVIOUS capacity for parent)
                // parent has capacity b_prev / A
                let above_bound = b_prev / (2.0 * params.a);
                if from_above > 0 && above_bound > 0.0 {
                    let ratio = from_above as f64 / above_bound;
                    if ratio > max_ratio_above { max_ratio_above = ratio; }
                }

                // total ≤ νb
                let total = from_below + from_above;
                if total > 0 && b > 0.0 {
                    let ratio = total as f64 / b;
                    if ratio > max_ratio_total { max_ratio_total = ratio; }
                }
            }

            tree.do_stage(&params, t, SepModel::Perfect, &mut rng);
            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < threshold { break; }
        }

        println!("  n={:5}: max(items_below/bound)={:.4}, max(items_above/bound)={:.4}, max(total/νb)={:.4}",
            n, max_ratio_below, max_ratio_above, max_ratio_total);
    }
}

/// Test with a better approximate separator model:
/// Sort items, then for each child half, independently displace ceil(ε·half_size) items
fn test_controlled_displacement() {
    println!("\n=== Test 10: Controlled displacement separator ===");
    let params = Params::seiferas_preview();

    for &n in &[64, 256, 1024] {
        let mut tree = BagTree::new(n);
        let mut rng = Rng::new(42);
        let threshold = 1.0 / params.lambda;
        let mut result = "OK";
        let mut converge_t = 0;

        for t in 0..200 {
            // Custom stage with controlled displacement
            let mut new_bags: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();
            let active: Vec<_> = tree.bags.iter()
                .filter(|(_, items)| !items.is_empty())
                .map(|(&k, v)| (k, v.clone()))
                .collect();

            for ((level, idx), mut items) in active {
                items.sort(); // Perfect sort first

                let b = params.capacity(tree.n, t, level);
                let kick_per_side = (params.lambda * b).floor() as usize;
                let has_parent = level > 0;
                let has_children = level < tree.max_level;

                if !has_parent {
                    // Root: split with controlled displacement
                    let mid = items.len() / 2;
                    let mut left: Vec<usize> = items[..mid].to_vec();
                    let mut right: Vec<usize> = items[mid..].to_vec();

                    // Displace: swap ceil(ε·mid) items between halves
                    let num_displace = ((params.eps * mid as f64).ceil() as usize).min(left.len()).min(right.len());
                    for _ in 0..num_displace {
                        let i = rng.next_usize(left.len());
                        let j = rng.next_usize(right.len());
                        std::mem::swap(&mut left[i], &mut right[j]);
                    }

                    new_bags.entry((level + 1, 2 * idx)).or_default().extend(left);
                    new_bags.entry((level + 1, 2 * idx + 1)).or_default().extend(right);
                } else if !has_children {
                    new_bags.entry((level - 1, idx / 2)).or_default().extend(items);
                } else {
                    let total = items.len();
                    let kick_small = kick_per_side.min(total);
                    let kick_large = kick_per_side.min(total.saturating_sub(kick_small));

                    let parent_entry = new_bags.entry((level - 1, idx / 2)).or_default();
                    for &item in &items[..kick_small] {
                        parent_entry.push(item);
                    }
                    for &item in &items[total - kick_large..] {
                        parent_entry.push(item);
                    }

                    let mut middle: Vec<usize> = items[kick_small..total - kick_large].to_vec();
                    if middle.len() % 2 == 1 {
                        let mi = middle.len() / 2;
                        let mid_item = middle.remove(mi);
                        parent_entry.push(mid_item);
                    }

                    let half = middle.len() / 2;
                    if half > 0 {
                        let mut left: Vec<usize> = middle[..half].to_vec();
                        let mut right: Vec<usize> = middle[half..].to_vec();

                        // Controlled displacement between children
                        let num_displace = ((params.eps * half as f64).ceil() as usize)
                            .min(left.len()).min(right.len());
                        for _ in 0..num_displace {
                            let i = rng.next_usize(left.len());
                            let j = rng.next_usize(right.len());
                            std::mem::swap(&mut left[i], &mut right[j]);
                        }

                        new_bags.entry((level + 1, 2 * idx)).or_default().extend(left);
                        new_bags.entry((level + 1, 2 * idx + 1)).or_default().extend(right);
                    }
                }
            }

            tree.bags = new_bags;

            if let Err(v) = tree.check_invariant(&params, t + 1) {
                result = "FAIL";
                println!("  n={:5}: FAIL at t={}, clause {}: {}", n, t+1, v.clause,
                    &v.detail[..v.detail.len().min(70)]);
                break;
            }

            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < threshold {
                converge_t = t + 1;
                break;
            }
        }
        if result == "OK" {
            println!("  n={:5}: OK, converged at t={}", n, converge_t);
        }
    }
}

/// Test convergence rate: stages = C * log2(n)
fn test_convergence_rate() {
    println!("\n=== Test 11: Convergence rate analysis ===");
    let params = Params::seiferas_preview();

    println!("  {:>8} {:>8} {:>10} {:>10}", "n", "stages", "log2(n)", "stages/log2");
    for exp in 3..=14 {
        let n = 1usize << exp;
        match run_simulation(n, &params, 500, SepModel::Perfect, 42, false) {
            Ok(stages) => {
                let log2n = exp as f64;
                println!("  {:>8} {:>8} {:>10.1} {:>10.2}", n, stages, log2n, stages as f64 / log2n);
            }
            Err((t, v)) => println!("  {:>8} FAIL at t={}, clause {}", n, t, v.clause),
        }
    }
}

/// Check (λ, ε)-separation property on a separator output.
/// Returns (initial_ok, final_ok, max_ratio).
fn check_sep_property(items: &[usize], lambda: f64, eps: f64) -> (bool, bool, f64) {
    let m = items.len();
    let lambda_m = (lambda * m as f64).floor() as usize;
    if lambda_m == 0 {
        // Vacuously true: no quantiles to check when fringe is empty
        return (true, true, 0.0);
    }

    let mut sorted_vals: Vec<usize> = items.to_vec();
    sorted_vals.sort();
    let mut initial_ok = true;
    let mut final_ok = true;
    let mut max_ratio: f64 = 0.0;

    // SepInitial: for each k ∈ [1, lambda_m], at most ε·k of the k smallest
    // are at positions ≥ lambda_m
    for k in 1..=lambda_m.min(m) {
        let threshold = sorted_vals[k - 1];
        let count: usize = items[lambda_m..].iter()
            .filter(|&&v| v <= threshold).count();
        let bound = eps * k as f64;
        if count as f64 > bound { initial_ok = false; }
        if bound > 0.0 {
            let ratio = count as f64 / bound;
            if ratio > max_ratio { max_ratio = ratio; }
        }
    }

    // SepFinal: symmetrically for largest
    for k in 1..=lambda_m.min(m) {
        let threshold = sorted_vals[m - k];
        let count: usize = items[..m.saturating_sub(lambda_m)].iter()
            .filter(|&&v| v >= threshold).count();
        let bound = eps * k as f64;
        if count as f64 > bound { final_ok = false; }
        if bound > 0.0 {
            let ratio = count as f64 / bound;
            if ratio > max_ratio { max_ratio = ratio; }
        }
    }

    (initial_ok, final_ok, max_ratio)
}

/// Check ε-halving property: at most ⌊ε·(m/2)⌋ items from each half in wrong half.
fn check_halving_property(items: &[usize], eps: f64) -> (bool, usize, f64) {
    let m = items.len();
    let half = m / 2;
    if half == 0 { return (true, 0, 0.0); }

    // Items 0..half-1 by value should be in positions 0..half-1
    let wrong_in_top = items[..half].iter().filter(|&&v| v >= half).count();
    let wrong_in_bot = items[half..].iter().filter(|&&v| v < half).count();
    let max_wrong = wrong_in_top.max(wrong_in_bot);
    let bound = (eps * half as f64).floor() as usize;
    let ratio = if bound > 0 { max_wrong as f64 / bound as f64 } else if max_wrong > 0 { f64::INFINITY } else { 0.0 };
    (max_wrong <= bound, max_wrong, ratio)
}

/// Verify separator models satisfy (λ, ε)-separation and ε-halving.
fn test_formal_sep_validity() {
    println!("\n=== Test 12: Separator model validity ===");
    let params = Params::seiferas_preview();
    let mut rng = Rng::new(42);

    let models: Vec<(&str, SepModel)> = vec![
        ("Formal", SepModel::Formal),
        ("Adversarial", SepModel::Adversarial { lambda: params.lambda }),
    ];

    for (name, model) in &models {
        println!("  --- {} model ---", name);
        for &m in &[10, 50, 100, 200, 500, 1000, 5000] {
            let trials = 2000;
            let mut sep_fails = 0;
            let mut halv_fails = 0;
            let mut max_sep_ratio: f64 = 0.0;
            let mut max_halv_ratio: f64 = 0.0;

            for _ in 0..trials {
                let mut items: Vec<usize> = (0..m).collect();
                for i in (1..m).rev() {
                    let j = rng.next_usize(i + 1);
                    items.swap(i, j);
                }

                apply_separator(&mut items, *model, params.eps, &mut rng);

                let (i_ok, f_ok, sep_r) = check_sep_property(&items, params.lambda, params.eps);
                if !i_ok || !f_ok { sep_fails += 1; }
                if sep_r > max_sep_ratio { max_sep_ratio = sep_r; }

                let (h_ok, _, halv_r) = check_halving_property(&items, params.eps);
                if !h_ok { halv_fails += 1; }
                if halv_r > max_halv_ratio && halv_r.is_finite() { max_halv_ratio = halv_r; }
            }

            println!("    m={:5}: sep pass {}/{}, halv pass {}/{}, max_sep_ratio={:.3}, max_halv_ratio={:.3}",
                m, trials - sep_fails, trials, trials - halv_fails, trials,
                max_sep_ratio, max_halv_ratio);
        }
    }
}

/// Full invariant simulation with formal separator model.
/// Tests many sizes and seeds to check whether the four-clause invariant holds.
fn test_formal_sep_invariant() {
    println!("\n=== Test 13: Invariant with formal separator model ===");
    let params = Params::seiferas_preview();
    let num_seeds = 100;

    println!("  {:>6} {:>6} {:>8} {:>8} {:>8} {:>8} {:>8}",
        "n", "ok", "cl1", "cl2", "cl3", "cl4", "conv_avg");

    for &n in &[8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096] {
        let mut ok_count = 0;
        let mut clause_fails = [0usize; 5]; // index 1-4 for clauses
        let mut total_conv_stages = 0usize;
        let mut first_fail: Option<String> = None;

        for seed in 0..num_seeds {
            match run_simulation(n, &params, 300, SepModel::Formal, seed, false) {
                Ok(stages) => {
                    ok_count += 1;
                    total_conv_stages += stages;
                }
                Err((t, v)) => {
                    let idx = v.clause.min(4);
                    clause_fails[idx] += 1;
                    if first_fail.is_none() {
                        first_fail = Some(format!("t={} cl{}: {}",
                            t, v.clause, &v.detail[..v.detail.len().min(50)]));
                    }
                }
            }
        }

        let avg_conv = if ok_count > 0 { total_conv_stages as f64 / ok_count as f64 } else { 0.0 };
        print!("  {:>6} {:>4}/{} {:>8} {:>8} {:>8} {:>8} {:>8.1}",
            n, ok_count, num_seeds,
            clause_fails[1], clause_fails[2], clause_fails[3], clause_fails[4], avg_conv);
        if let Some(ref f) = first_fail {
            print!("  | {}", f);
        }
        println!();
    }
}

/// Track stranger bound tightness across simulation.
/// For each j, track max(actual_strangers / bound) across all bags and stages.
fn test_stranger_bound_tightness() {
    println!("\n=== Test 14: Stranger bound tightness (formal separator) ===");
    let params = Params::seiferas_preview();

    for &n in &[64, 256, 1024] {
        // Track max ratio for each j value
        let mut max_ratio_by_j: Vec<f64> = vec![0.0; 20]; // j = 0..19
        let mut rng = Rng::new(42);

        let mut tree = BagTree::new(n);
        let threshold = 1.0 / params.lambda;

        for t in 0..200 {
            tree.do_stage(&params, t, SepModel::Formal, &mut rng);

            // Check stranger bounds at all active bags
            for level in 0..=tree.max_level {
                if (t + 1 + level) % 2 != 0 { continue; }
                let num_bags = 1usize << level;
                let b = params.capacity(n, t + 1, level);

                for idx in 0..num_bags {
                    if let Some(items) = tree.bags.get(&(level, idx)) {
                        if items.is_empty() { continue; }
                        for j in 1..=level.min(19) {
                            let count = tree.j_stranger_count(items, level, idx, j);
                            let bound = params.lambda * params.eps.powi(j as i32 - 1) * b;
                            if bound > 0.001 {
                                let ratio = count as f64 / bound;
                                if ratio > max_ratio_by_j[j] {
                                    max_ratio_by_j[j] = ratio;
                                }
                            }
                        }
                    }
                }
            }

            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < threshold { break; }
        }

        print!("  n={:5}:", n);
        for j in 1..=10 {
            if max_ratio_by_j[j] > 0.0 {
                print!("  j={}:{:.3}", j, max_ratio_by_j[j]);
            }
        }
        println!();
    }
}

/// Test halving property: after separator, how many items go to "wrong" child?
fn test_halving_errors() {
    println!("\n=== Test 15: Halving errors in formal separator ===");
    let params = Params::seiferas_preview();

    for &m in &[10, 50, 100, 500, 1000] {
        let trials = 5000;
        let mut max_half_error_ratio: f64 = 0.0;
        let mut rng = Rng::new(42);

        for _ in 0..trials {
            let mut items: Vec<usize> = (0..m).collect();
            for i in (1..m).rev() {
                let j = rng.next_usize(i + 1);
                items.swap(i, j);
            }

            apply_separator(&mut items, SepModel::Formal, params.eps, &mut rng);

            // After separator, split at midpoint.
            // Count items in first half whose rank ≥ m/2 ("wrong half").
            let half = m / 2;
            let wrong_in_first_half = items[..half].iter().filter(|&&v| v >= half).count();
            let wrong_in_second_half = items[half..].iter().filter(|&&v| v < half).count();
            let max_wrong = wrong_in_first_half.max(wrong_in_second_half);

            let bound = params.eps * half as f64;
            if bound > 0.0 {
                let ratio = max_wrong as f64 / bound;
                if ratio > max_half_error_ratio { max_half_error_ratio = ratio; }
            }
        }

        println!("  m={:5}: max(halving_errors / ε·(m/2)) = {:.4} (bound ≤ 1.0 required)",
            m, max_half_error_ratio);
    }
}

/// Verbose trace with formal separator for small n.
fn test_formal_sep_verbose() {
    println!("\n=== Test 16: Verbose trace with formal separator (n=64) ===");
    let params = Params::seiferas_preview();

    match run_simulation(64, &params, 50, SepModel::Formal, 42, true) {
        Ok(stages) => println!("  Converged in {} stages", stages),
        Err((t, v)) => println!("  FAIL at t={}: clause {}: {}", t, v.clause, v.detail),
    }
}

/// Invariant test with adversarial separator (deterministic worst-case).
fn test_adversarial_sep_invariant() {
    println!("\n=== Test 17: Invariant with adversarial separator ===");
    let params = Params::seiferas_preview();
    let model = SepModel::Adversarial { lambda: params.lambda };

    println!("  {:>6} {:>8} {:>8}", "n", "result", "stages");
    for exp in 3..=14 {
        let n = 1usize << exp;
        match run_simulation(n, &params, 500, model, 42, false) {
            Ok(stages) => println!("  {:>6} {:>8} {:>8}", n, "OK", stages),
            Err((t, v)) => println!("  {:>6} {:>8} {:>8}  | cl{}: {}",
                n, format!("F@t={}", t), 0, v.clause,
                &v.detail[..v.detail.len().min(50)]),
        }
    }
}

/// Compare convergence rates across all separator models.
fn test_model_comparison() {
    println!("\n=== Test 18: Model comparison (Perfect vs Adversarial vs Formal vs RandomSwap) ===");
    let params = Params::seiferas_preview();
    let adv = SepModel::Adversarial { lambda: params.lambda };

    println!("  {:>6} {:>10} {:>10} {:>10} {:>10}", "n", "Perfect", "Adversarl", "Formal", "RandSwap");
    for exp in 3..=12 {
        let n = 1usize << exp;

        let perfect = match run_simulation(n, &params, 300, SepModel::Perfect, 42, false) {
            Ok(s) => format!("{}", s),
            Err((t, v)) => format!("F@{}c{}", t, v.clause),
        };

        let adversarial = match run_simulation(n, &params, 300, adv, 42, false) {
            Ok(s) => format!("{}", s),
            Err((t, v)) => format!("F@{}c{}", t, v.clause),
        };

        let formal = match run_simulation(n, &params, 300, SepModel::Formal, 42, false) {
            Ok(s) => format!("{}", s),
            Err((t, v)) => format!("F@{}c{}", t, v.clause),
        };

        let random = match run_simulation(n, &params, 300, SepModel::RandomSwap, 42, false) {
            Ok(s) => format!("{}", s),
            Err((t, v)) => format!("F@{}c{}", t, v.clause),
        };

        println!("  {:>6} {:>10} {:>10} {:>10} {:>10}", n, perfect, adversarial, formal, random);
    }
}

/// Compare shifted vs unshifted j-stranger definitions.
/// Shifted (Seiferas): j-stranger iff nativeBagIdx(n, level-(j-1), rank) != idx/2^(j-1)
///   j=1 means "not native to this bag"
/// Unshifted (current Lean): j-stranger iff nativeBagIdx(n, level-j, rank) != idx/2^j
///   j=1 means "not native to parent"
/// Both should satisfy the invariant. Shifted counts more strangers.
fn test_shifted_vs_unshifted() {
    println!("\n=== Test 19: Shifted vs unshifted j-stranger definitions ===");
    let params = Params::seiferas_preview();
    let model = SepModel::Adversarial { lambda: params.lambda };

    println!("  {:>6} {:>8} {:>8} {:>10} {:>10} {:>8}",
        "n", "sh_ok", "un_ok", "max_r_sh", "max_r_un", "extra");

    for exp in 3..=12 {
        let n = 1usize << exp;
        let mut tree = BagTree::new(n);
        let mut rng = Rng::new(42);
        let threshold = 1.0 / params.lambda;
        let mut shifted_ok = true;
        let mut unshifted_ok = true;
        let mut max_ratio_shifted: f64 = 0.0;
        let mut max_ratio_unshifted: f64 = 0.0;
        let mut max_extra: usize = 0;

        for t in 0..300 {
            tree.do_stage(&params, t, model, &mut rng);

            if tree.check_invariant_shifted(&params, t + 1).is_err() {
                shifted_ok = false;
            }
            if tree.check_invariant(&params, t + 1).is_err() {
                unshifted_ok = false;
            }

            for level in 0..=tree.max_level {
                if (t + 1 + level) % 2 != 0 { continue; }
                let b = params.capacity(n, t + 1, level);
                for idx in 0..(1usize << level) {
                    if let Some(items) = tree.bags.get(&(level, idx)) {
                        if items.is_empty() { continue; }
                        for j in 1..=level {
                            let cs = tree.j_stranger_count(items, level, idx, j);
                            let cu = tree.j_stranger_count_unshifted(items, level, idx, j);
                            let bound = params.lambda * params.eps.powi(j as i32 - 1) * b;
                            let extra = cs.saturating_sub(cu);
                            if extra > max_extra { max_extra = extra; }
                            if bound > 0.001 {
                                let rs = cs as f64 / bound;
                                let ru = cu as f64 / bound;
                                if rs > max_ratio_shifted { max_ratio_shifted = rs; }
                                if ru > max_ratio_unshifted { max_ratio_unshifted = ru; }
                            }
                        }
                    }
                }
            }

            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < threshold { break; }
        }

        println!("  {:>6} {:>8} {:>8} {:>10.4} {:>10.4} {:>8}",
            n, shifted_ok, unshifted_ok, max_ratio_shifted, max_ratio_unshifted, max_extra);
    }
}

/// 1-stranger source decomposition (shifted definition, j=1).
/// For each bag B receiving items, classify 1-strangers by source:
///   (a) Was a 2-stranger (shifted) at a child — came from below
///   (b) Was a 1-stranger (shifted) at parent D — came from above, previously strange
///   (c) Was NOT a 1-stranger at D, native to sibling C — newly strange
/// Seiferas bounds (fraction of b = n*nu^t*A^level):
///   (a) <= 2*lam*eps*A,  (b) <= eps*lam/A,
///   (c) <= eps/(2A) + 2*lam*eps*A/(1-(2*eps*A)^2) + 1/(8A^3-2A)
fn test_source_decomposition() {
    println!("\n=== Test 20: 1-stranger source decomposition (shifted, j=1) ===");
    let params = Params::seiferas_preview();
    let a = params.a;
    let e = params.eps;
    let l = params.lambda;

    let bound_a_frac = 2.0 * l * e * a;
    let bound_b_frac = e * l / a;
    let bound_c_frac = e / (2.0 * a)
        + 2.0 * l * e * a / (1.0 - (2.0 * e * a).powi(2))
        + 1.0 / (8.0 * a.powi(3) - 2.0 * a);
    let bound_total_frac = l * params.nu;

    println!("  Bounds (fraction of b):");
    println!("    (a) 2*lam*eps*A           = {:.6}", bound_a_frac);
    println!("    (b) eps*lam/A             = {:.6}", bound_b_frac);
    println!("    (c) eps/(2A) + geo + high = {:.6}", bound_c_frac);
    println!("    Sum (a)+(b)+(c)           = {:.6}", bound_a_frac + bound_b_frac + bound_c_frac);
    println!("    Required <= lam*nu        = {:.6}", bound_total_frac);
    println!();

    let models: Vec<(&str, SepModel)> = vec![
        ("Adversarial", SepModel::Adversarial { lambda: params.lambda }),
        ("Formal", SepModel::Formal),
        ("Perfect", SepModel::Perfect),
    ];

    for (model_name, model) in &models {
        println!("  --- {} separator ---", model_name);

        for &n in &[64, 256, 1024, 4096] {
            let mut tree = BagTree::new(n);
            let mut rng = Rng::new(42);
            let threshold = 1.0 / params.lambda;

            let mut max_a_ratio: f64 = 0.0;
            let mut max_b_ratio: f64 = 0.0;
            let mut max_c_ratio: f64 = 0.0;
            let mut max_total_ratio: f64 = 0.0;
            let mut c_not_sibling = 0usize;

            for t in 0..300 {
                let pre_locs = tree.item_locations();

                // Pre-compute shifted 1-stranger status at old locations
                let mut pre_shifted_1s = vec![false; n];
                for rank in 0..n {
                    if let Some((lev, id)) = pre_locs[rank] {
                        pre_shifted_1s[rank] = tree.is_j_stranger_shifted(rank, lev, id, 1);
                    }
                }

                tree.do_stage(&params, t, *model, &mut rng);

                for level in 0..=tree.max_level {
                    if (t + 1 + level) % 2 != 0 { continue; }
                    // b = capacity at B's level at stage t (pre-stage)
                    let b = (n as f64) * params.nu.powi(t as i32) * params.a.powi(level as i32);

                    for idx in 0..(1usize << level) {
                        let items = match tree.bags.get(&(level, idx)) {
                            Some(v) if !v.is_empty() => v,
                            _ => continue,
                        };

                        let mut sa = 0usize;
                        let mut sb = 0usize;
                        let mut sc = 0usize;

                        for &rank in items {
                            // Is this item a 1-stranger at B (shifted)?
                            if !tree.is_j_stranger_shifted(rank, level, idx, 1) { continue; }

                            let Some((old_level, _old_idx)) = pre_locs[rank] else { continue };

                            if old_level > level {
                                // From a child: was a 2-stranger there (shifted)
                                sa += 1;
                            } else if old_level < level {
                                // From parent D
                                if pre_shifted_1s[rank] {
                                    sb += 1; // was already 1-stranger at D
                                } else {
                                    sc += 1; // native to D, must be native to sibling C
                                    // Sanity check
                                    let sibling_idx = idx ^ 1;
                                    if tree.native_bag_idx(level, rank) != sibling_idx {
                                        c_not_sibling += 1;
                                    }
                                }
                            }
                        }

                        let total = sa + sb + sc;
                        let ba = bound_a_frac * b;
                        let bb = bound_b_frac * b;
                        let bc = bound_c_frac * b;
                        let bt = bound_total_frac * b;

                        if ba > 0.01 {
                            let r = sa as f64 / ba;
                            if r > max_a_ratio { max_a_ratio = r; }
                        }
                        if bb > 0.01 {
                            let r = sb as f64 / bb;
                            if r > max_b_ratio { max_b_ratio = r; }
                        }
                        if bc > 0.01 {
                            let r = sc as f64 / bc;
                            if r > max_c_ratio { max_c_ratio = r; }
                        }
                        if bt > 0.01 {
                            let r = total as f64 / bt;
                            if r > max_total_ratio { max_total_ratio = r; }
                        }
                    }
                }

                let leaf_cap = params.capacity(n, t + 1, tree.max_level);
                if leaf_cap < threshold { break; }
            }

            print!("    n={:5}: (a)={:.4} (b)={:.4} (c)={:.4} total={:.4}",
                n, max_a_ratio, max_b_ratio, max_c_ratio, max_total_ratio);
            if c_not_sibling > 0 {
                print!(" [!{} not sibling]", c_not_sibling);
            }
            println!();
        }
    }
}

/// j>1 source decomposition (shifted, j=2).
/// Sources of 2-strangers at B:
///   (a) 3-strangers at children (shifted) — at most 2*lam*eps^2*b*A
///   (b) 1-strangers at parent (shifted), filtered — at most eps*lam*b/A
/// Constraint: 2*A*eps + 1/A <= nu
fn test_j_gt_1_source_decomposition() {
    println!("\n=== Test 21: j=2 stranger source decomposition (shifted) ===");
    let params = Params::seiferas_preview();
    let a = params.a;
    let e = params.eps;
    let l = params.lambda;

    // For j=2: bound = lam*eps * nu * b
    // Source (a): 2 * lam * eps^2 * b * A  (3-strangers at children)
    // Source (b): eps * lam * b / A         (1-strangers at parent, filtered)
    let bound_a_frac = 2.0 * l * e * e * a;
    let bound_b_frac = e * l / a;
    let bound_total_frac = l * e * params.nu;

    println!("  j=2 bounds (fraction of b):");
    println!("    (a) 2*lam*eps^2*A = {:.8}", bound_a_frac);
    println!("    (b) eps*lam/A     = {:.8}", bound_b_frac);
    println!("    Total <= lam*eps*nu = {:.8}", bound_total_frac);

    let model = SepModel::Adversarial { lambda: params.lambda };

    for &n in &[64, 256, 1024, 4096] {
        let mut tree = BagTree::new(n);
        let mut rng = Rng::new(42);
        let threshold = 1.0 / params.lambda;

        let mut max_a_ratio: f64 = 0.0;
        let mut max_b_ratio: f64 = 0.0;
        let mut max_total_ratio: f64 = 0.0;

        for t in 0..300 {
            let pre_locs = tree.item_locations();
            let mut pre_shifted_1s = vec![false; n];
            for rank in 0..n {
                if let Some((lev, id)) = pre_locs[rank] {
                    pre_shifted_1s[rank] = tree.is_j_stranger_shifted(rank, lev, id, 1);
                }
            }

            tree.do_stage(&params, t, model, &mut rng);

            for level in 0..=tree.max_level {
                if (t + 1 + level) % 2 != 0 { continue; }
                if level < 2 { continue; } // j=2 requires level >= 2
                let b = (n as f64) * params.nu.powi(t as i32) * params.a.powi(level as i32);

                for idx in 0..(1usize << level) {
                    let items = match tree.bags.get(&(level, idx)) {
                        Some(v) if !v.is_empty() => v,
                        _ => continue,
                    };

                    let mut sa = 0usize;
                    let mut sb = 0usize;

                    for &rank in items {
                        // Is this item a 2-stranger at B (shifted)?
                        if !tree.is_j_stranger_shifted(rank, level, idx, 2) { continue; }

                        let Some((old_level, _)) = pre_locs[rank] else { continue };

                        if old_level > level {
                            // From child: was a 3-stranger there (shifted)
                            sa += 1;
                        } else if old_level < level {
                            // From parent: was a 1-stranger there (shifted)
                            // (only 1-strangers at D can become 2-strangers at B from above)
                            sb += 1;
                        }
                    }

                    let total = sa + sb;
                    let ba = bound_a_frac * b;
                    let bb = bound_b_frac * b;
                    let bt = bound_total_frac * b;

                    if ba > 0.001 {
                        let r = sa as f64 / ba;
                        if r > max_a_ratio { max_a_ratio = r; }
                    }
                    if bb > 0.001 {
                        let r = sb as f64 / bb;
                        if r > max_b_ratio { max_b_ratio = r; }
                    }
                    if bt > 0.001 {
                        let r = total as f64 / bt;
                        if r > max_total_ratio { max_total_ratio = r; }
                    }
                }
            }

            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < threshold { break; }
        }

        println!("    n={:5}: (a)={:.4} (b)={:.4} total={:.4}",
            n, max_a_ratio, max_b_ratio, max_total_ratio);
    }
}

/// Stress-test source bounds with larger eps (tighter constraint margin).
/// Seiferas params (eps=1/99) leave large margin. Try eps up to constraint limit.
fn test_source_bounds_stress() {
    println!("\n=== Test 22: Source bounds stress test (larger eps) ===");

    // Try several eps values with A=10, nu=0.65, lambda=eps
    let test_eps = [0.005, 0.008, 1.0/99.0, 0.012, 0.013];
    let n = 4096usize;

    println!("  {:>8} {:>8} {:>8} {:>8} {:>8} {:>8} {:>8} {:>8}",
        "eps", "C4j1_ok", "inv_ok", "(a)", "(b)", "(c)", "total", "margin");

    for &eps in &test_eps {
        let params = Params { a: 10.0, nu: 0.65, lambda: eps, eps };
        let a = params.a;
        let e = params.eps;
        let l = params.lambda;

        let bound_a_frac = 2.0 * l * e * a;
        let bound_b_frac = e * l / a;
        let bound_c_frac = e / (2.0 * a)
            + 2.0 * l * e * a / (1.0 - (2.0 * e * a).powi(2))
            + 1.0 / (8.0 * a.powi(3) - 2.0 * a);
        let bound_total_frac = l * params.nu;
        let c4_ok = params.check_c4_j_eq_1();
        let margin = 1.0 - (bound_a_frac + bound_b_frac + bound_c_frac) / bound_total_frac;

        let model = SepModel::Adversarial { lambda: params.lambda };
        let mut tree = BagTree::new(n);
        let mut rng = Rng::new(42);
        let threshold = 1.0 / params.lambda;

        let mut max_a: f64 = 0.0;
        let mut max_b: f64 = 0.0;
        let mut max_c: f64 = 0.0;
        let mut max_t: f64 = 0.0;
        let mut inv_ok = true;

        for t in 0..300 {
            let pre_locs = tree.item_locations();
            let mut pre_s1 = vec![false; n];
            for rank in 0..n {
                if let Some((lev, id)) = pre_locs[rank] {
                    pre_s1[rank] = tree.is_j_stranger_shifted(rank, lev, id, 1);
                }
            }

            tree.do_stage(&params, t, model, &mut rng);

            if tree.check_invariant_shifted(&params, t + 1).is_err() {
                inv_ok = false;
            }

            for level in 0..=tree.max_level {
                if (t + 1 + level) % 2 != 0 { continue; }
                let b = (n as f64) * params.nu.powi(t as i32) * params.a.powi(level as i32);

                for idx in 0..(1usize << level) {
                    let items = match tree.bags.get(&(level, idx)) {
                        Some(v) if !v.is_empty() => v,
                        _ => continue,
                    };

                    let mut sa = 0usize;
                    let mut sb = 0usize;
                    let mut sc = 0usize;

                    for &rank in items {
                        if !tree.is_j_stranger_shifted(rank, level, idx, 1) { continue; }
                        let Some((old_level, _)) = pre_locs[rank] else { continue };
                        if old_level > level {
                            sa += 1;
                        } else if old_level < level {
                            if pre_s1[rank] { sb += 1; } else { sc += 1; }
                        }
                    }

                    let total = sa + sb + sc;
                    let ba = bound_a_frac * b;
                    let bb = bound_b_frac * b;
                    let bc = bound_c_frac * b;
                    let bt = bound_total_frac * b;

                    if ba > 0.01 { max_a = max_a.max(sa as f64 / ba); }
                    if bb > 0.01 { max_b = max_b.max(sb as f64 / bb); }
                    if bc > 0.01 { max_c = max_c.max(sc as f64 / bc); }
                    if bt > 0.01 { max_t = max_t.max(total as f64 / bt); }
                }
            }

            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < threshold { break; }
        }

        println!("  {:>8.5} {:>8} {:>8} {:>8.4} {:>8.4} {:>8.4} {:>8.4} {:>7.1}%",
            eps, c4_ok, inv_ok, max_a, max_b, max_c, max_t, margin * 100.0);
    }
}

/// === RISK REDUCTION TEST A ===
/// Detailed rebagging flow validation: track exact item counts per flow direction
/// and verify they match the Seiferas formulas precisely.
/// Checks: fringe = floor(lam * b), odd adjustment, items_from_below <= 4*lam*b*A + 2,
/// items_from_above <= b/(2A), no items lost or duplicated.
fn test_rebagging_flow_validation() {
    println!("\n=== Test A: Rebagging flow validation (detailed) ===");
    let params = Params::seiferas_preview();
    let model = SepModel::Adversarial { lambda: params.lambda };

    for &n in &[8, 16, 64, 256, 1024, 4096] {
        let mut tree = BagTree::new(n);
        let mut rng = Rng::new(42);
        let threshold = 1.0 / params.lambda;
        let mut max_fringe_error: f64 = 0.0; // |actual_fringe - floor(lam*b)| / floor(lam*b)
        let mut max_odd_adj = 0usize;
        let mut items_lost = false;
        let mut items_duped = false;
        let mut max_from_below_ratio: f64 = 0.0;
        let mut max_from_above_ratio: f64 = 0.0;
        let mut max_total_ratio: f64 = 0.0;

        for t in 0..300 {
            let pre_total = tree.total_items();
            let pre_locs = tree.item_locations();

            // Snapshot active bags
            let active: Vec<((usize, usize), Vec<usize>)> = tree.bags.iter()
                .filter(|(_, items)| !items.is_empty())
                .map(|(&k, v)| (k, v.clone()))
                .collect();

            // Compute expected fringe sizes
            for &((level, _idx), ref items) in &active {
                let b = params.capacity(n, t, level);
                let expected_fringe = (params.lambda * b).floor() as usize;
                let actual_kick = if level > 0 && level < tree.max_level {
                    let kick_small = expected_fringe.min(items.len());
                    let kick_large = expected_fringe.min(items.len().saturating_sub(kick_small));
                    kick_small + kick_large
                } else { 0 };
                if expected_fringe > 0 && level > 0 && level < tree.max_level {
                    let expected_total_kick = 2 * expected_fringe;
                    let err = (actual_kick as f64 - expected_total_kick as f64).abs()
                        / expected_total_kick as f64;
                    if err > max_fringe_error { max_fringe_error = err; }
                }
            }

            // Track flows by destination
            let mut flows: BTreeMap<(usize, usize), (usize, usize, usize)> = BTreeMap::new();
            // (from_below, from_above, odd_adjustment)
            for ((level, idx), mut items) in active.clone() {
                items.sort();
                let b = params.capacity(tree.n, t, level);
                let kick_per_side = (params.lambda * b).floor() as usize;
                let has_parent = level > 0;
                let has_children = level < tree.max_level;

                if !has_parent {
                    let mid = items.len() / 2;
                    let f = flows.entry((level + 1, 2 * idx)).or_default();
                    f.1 += mid;
                    let f = flows.entry((level + 1, 2 * idx + 1)).or_default();
                    f.1 += items.len() - mid;
                } else if !has_children {
                    let f = flows.entry((level - 1, idx / 2)).or_default();
                    f.0 += items.len();
                } else {
                    let kick_small = kick_per_side.min(items.len());
                    let kick_large = kick_per_side.min(items.len().saturating_sub(kick_small));
                    let kicked = kick_small + kick_large;
                    let mut remaining = items.len() - kicked;
                    let odd = if remaining % 2 == 1 { 1 } else { 0 };
                    if odd > max_odd_adj { max_odd_adj = odd; }
                    remaining -= odd;

                    let f = flows.entry((level - 1, idx / 2)).or_default();
                    f.0 += kicked + odd;
                    f.2 += odd;

                    if remaining > 0 {
                        let half = remaining / 2;
                        let f = flows.entry((level + 1, 2 * idx)).or_default();
                        f.1 += half;
                        let f = flows.entry((level + 1, 2 * idx + 1)).or_default();
                        f.1 += remaining - half;
                    }
                }
            }

            // Check bounds on flows
            for (&(level, _), &(from_below, from_above, _odd)) in &flows {
                let b_old = params.capacity(n, t, level);
                let b_new = params.capacity(n, t + 1, level);

                // items_from_below bound: 4*lambda*b_old*A + 2
                let below_bound = 4.0 * params.lambda * b_old * params.a + 2.0;
                if from_below > 0 && below_bound > 0.0 {
                    let r = from_below as f64 / below_bound;
                    if r > max_from_below_ratio { max_from_below_ratio = r; }
                }

                // items_from_above bound: b_old / (2A)
                let above_bound = b_old / (2.0 * params.a);
                if from_above > 0 && above_bound > 0.0 {
                    let r = from_above as f64 / above_bound;
                    if r > max_from_above_ratio { max_from_above_ratio = r; }
                }

                // total bound: b_new = nu * b_old
                let total = from_below + from_above;
                if total > 0 && b_new > 0.0 {
                    let r = total as f64 / b_new;
                    if r > max_total_ratio { max_total_ratio = r; }
                }
            }

            tree.do_stage(&params, t, model, &mut rng);

            let post_total = tree.total_items();
            if post_total != pre_total { items_lost = true; }

            // Check no duplicates
            let mut seen = vec![false; n];
            for (_, items) in &tree.bags {
                for &rank in items {
                    if seen[rank] { items_duped = true; }
                    seen[rank] = true;
                }
            }

            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < threshold { break; }
        }

        let ok = !items_lost && !items_duped && max_total_ratio <= 1.001;
        println!("  n={:5}: {} | below={:.4} above={:.4} total={:.4} | lost={} dup={} fringe_err={:.4} odd={}",
            n, if ok { "OK" } else { "FAIL" },
            max_from_below_ratio, max_from_above_ratio, max_total_ratio,
            items_lost, items_duped, max_fringe_error, max_odd_adj);
    }
}

/// === RISK REDUCTION TEST D ===
/// End-to-end sorting check: run full pipeline and verify all items end up
/// in their native bags at convergence (= sorted).
/// For small n: test ALL permutations via identity (perfect sep).
/// For larger n: test with adversarial separator and check convergence.
fn test_end_to_end_sorting() {
    println!("\n=== Test D: End-to-end sorting verification ===");
    let params = Params::seiferas_preview();

    // Part 1: Small n with perfect separator — should ALWAYS converge to native bags
    println!("  Part 1: Perfect separator, verify all items native at convergence");
    for &n in &[8, 16, 32, 64, 128, 256, 512, 1024] {
        let mut tree = BagTree::new(n);
        let mut rng = Rng::new(42);
        let threshold = 1.0 / params.lambda;
        let mut converged_t = 0;

        for t in 0..500 {
            tree.do_stage(&params, t, SepModel::Perfect, &mut rng);
            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < threshold {
                converged_t = t + 1;
                break;
            }
        }

        // Check: every item is in its native bag
        let all_native = tree.all_native();
        // Also check: all bags have at most 1 item (converged to singletons)
        let max_bag_size: usize = tree.bags.values().map(|v| v.len()).max().unwrap_or(0);
        let total_1strangers: usize = (0..=tree.max_level)
            .flat_map(|level| (0..(1usize << level)).map(move |idx| (level, idx)))
            .map(|(level, idx)| {
                tree.bags.get(&(level, idx)).map_or(0, |items|
                    tree.j_stranger_count(items, level, idx, 1))
            }).sum();

        println!("    n={:5}: conv@t={:3} | native={} max_bag={} strangers={}",
            n, converged_t, all_native, max_bag_size, total_1strangers);
    }

    // Part 2: Adversarial separator — check items end up native despite errors
    println!("  Part 2: Adversarial separator, verify sorting at convergence");
    for &n in &[8, 16, 32, 64, 256, 1024, 4096] {
        let model = SepModel::Adversarial { lambda: params.lambda };
        let mut tree = BagTree::new(n);
        let mut rng = Rng::new(42);
        let threshold = 2.0; // Our Lean converged def: bagCapacity < 2

        let mut converged_t = 0;
        let mut invariant_ok = true;

        for t in 0..500 {
            tree.do_stage(&params, t, model, &mut rng);

            if tree.check_invariant_shifted(&params, t + 1).is_err() {
                invariant_ok = false;
            }

            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < threshold {
                converged_t = t + 1;
                break;
            }
        }

        let all_native = tree.all_native();
        let max_bag_size: usize = tree.bags.values().map(|v| v.len()).max().unwrap_or(0);
        let total_items: usize = tree.total_items();

        println!("    n={:5}: conv@t={:3} | native={} inv={} max_bag={} items={}",
            n, converged_t, all_native, invariant_ok, max_bag_size, total_items);
    }

    // Part 3: Multiple seeds, check all converge and sort
    println!("  Part 3: Adversarial, multiple seeds, n=256");
    let n = 256;
    let model = SepModel::Adversarial { lambda: params.lambda };
    let mut all_ok = true;
    let mut max_conv_t = 0;
    let mut native_count = 0;

    for seed in 0..100 {
        let mut tree = BagTree::new(n);
        let mut rng = Rng::new(seed);

        for t in 0..500 {
            tree.do_stage(&params, t, model, &mut rng);
            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < 2.0 {
                if t + 1 > max_conv_t { max_conv_t = t + 1; }
                break;
            }
        }

        if tree.all_native() { native_count += 1; } else { all_ok = false; }
    }
    println!("    100 seeds: {}/100 native, max_conv_t={}, all_ok={}",
        native_count, max_conv_t, all_ok);
}

/// === RISK REDUCTION TEST B ===
/// Tight bound ratio analysis for ALL invariant clauses simultaneously.
/// For each clause, track max(observed/bound) across all bags, stages, and j values.
/// Identifies which clause is tightest (closest to violation).
fn test_tight_bound_ratios() {
    println!("\n=== Test B: Tight bound ratios for all clauses ===");
    let params = Params::seiferas_preview();

    let models: Vec<(&str, SepModel)> = vec![
        ("Perfect", SepModel::Perfect),
        ("Adversarial", SepModel::Adversarial { lambda: params.lambda }),
    ];

    for (model_name, model) in &models {
        println!("  --- {} separator ---", model_name);
        println!("    {:>6} {:>10} {:>10} {:>10} {:>10} {:>10} {:>10}",
            "n", "cap_ratio", "s1_ratio", "s2_ratio", "s3_ratio", "total_s", "tightest");

        for &n in &[64, 256, 1024, 4096, 16384] {
            let mut tree = BagTree::new(n);
            let mut rng = Rng::new(42);
            let threshold = 1.0 / params.lambda;

            let mut max_cap_ratio: f64 = 0.0;    // clause 3
            let mut max_s_ratio = vec![0.0f64; 10]; // clause 4, j=1..9
            let mut max_total_s: f64 = 0.0;       // total 1-strangers / bound

            for t in 0..300 {
                tree.do_stage(&params, t, *model, &mut rng);

                for level in 0..=tree.max_level {
                    if (t + 1 + level) % 2 != 0 { continue; }
                    let b = params.capacity(n, t + 1, level);

                    for idx in 0..(1usize << level) {
                        let items = match tree.bags.get(&(level, idx)) {
                            Some(v) if !v.is_empty() => v,
                            _ => continue,
                        };

                        // Clause 3: capacity
                        if b > 0.01 {
                            let r = items.len() as f64 / b;
                            if r > max_cap_ratio { max_cap_ratio = r; }
                        }

                        // Clause 4: stranger bounds
                        for j in 1..=level.min(9) {
                            let count = tree.j_stranger_count(items, level, idx, j);
                            let bound = params.lambda * params.eps.powi(j as i32 - 1) * b;
                            if bound > 0.01 {
                                let r = count as f64 / bound;
                                if r > max_s_ratio[j] { max_s_ratio[j] = r; }
                            }
                        }
                    }
                }

                let leaf_cap = params.capacity(n, t + 1, tree.max_level);
                if leaf_cap < threshold { break; }
            }

            // Find tightest
            let mut tightest = "cap";
            let mut tightest_val = max_cap_ratio;
            for j in 1..=9 {
                if max_s_ratio[j] > tightest_val {
                    tightest_val = max_s_ratio[j];
                    tightest = match j { 1 => "s1", 2 => "s2", 3 => "s3", _ => "s4+" };
                }
            }

            println!("    {:>6} {:>10.4} {:>10.4} {:>10.4} {:>10.4} {:>10.4} {:>10}",
                n, max_cap_ratio, max_s_ratio[1], max_s_ratio[2],
                max_s_ratio.get(3).copied().unwrap_or(0.0),
                tightest_val, tightest);
        }
    }
}

/// === RISK REDUCTION TEST C ===
/// 1-stranger counterexample search: try to maximize 1-stranger ratios.
/// Uses multiple adversarial strategies and different seeds.
/// If any ratio exceeds 1.0, the Lean lemma statement is FALSE.
fn test_1stranger_counterexample_search() {
    println!("\n=== Test C: 1-stranger counterexample search ===");
    let params = Params::seiferas_preview();

    // Strategy 1: Standard adversarial, many seeds
    println!("  Strategy 1: Standard adversarial, 200 seeds");
    let mut global_max: f64 = 0.0;
    let mut worst_n = 0;
    let mut worst_seed = 0;
    let mut worst_t = 0;

    for &n in &[64, 256, 1024, 4096] {
        let model = SepModel::Adversarial { lambda: params.lambda };
        let mut n_max: f64 = 0.0;

        for seed in 0..200 {
            let mut tree = BagTree::new(n);
            let mut rng = Rng::new(seed);
            let threshold = 1.0 / params.lambda;

            for t in 0..300 {
                tree.do_stage(&params, t, model, &mut rng);

                for level in 0..=tree.max_level {
                    if (t + 1 + level) % 2 != 0 { continue; }
                    let b = params.capacity(n, t + 1, level);

                    for idx in 0..(1usize << level) {
                        if let Some(items) = tree.bags.get(&(level, idx)) {
                            if items.is_empty() { continue; }
                            let count = tree.j_stranger_count(items, level, idx, 1);
                            let bound = params.lambda * b;
                            if bound > 0.01 {
                                let r = count as f64 / bound;
                                if r > n_max { n_max = r; }
                                if r > global_max {
                                    global_max = r;
                                    worst_n = n;
                                    worst_seed = seed;
                                    worst_t = t + 1;
                                }
                            }
                        }
                    }
                }

                let leaf_cap = params.capacity(n, t + 1, tree.max_level);
                if leaf_cap < threshold { break; }
            }
        }

        let ok = n_max <= 1.0;
        println!("    n={:5}: max_1stranger_ratio={:.6} {}", n, n_max,
            if ok { "OK" } else { "EXCEEDS BOUND!" });
    }

    println!("    Global max: {:.6} at n={} seed={} t={}",
        global_max, worst_n, worst_seed, worst_t);
    if global_max > 1.0 {
        println!("    *** COUNTEREXAMPLE FOUND *** — Lean lemma is FALSE");
    } else {
        println!("    No counterexample found (max ratio {:.4}% of bound)", global_max * 100.0);
    }

    // Strategy 2: Formal stochastic separator, check tail behavior
    println!("  Strategy 2: Formal stochastic, 200 seeds (tail risk)");
    let mut formal_max: f64 = 0.0;

    for &n in &[256, 1024, 4096] {
        let mut n_max: f64 = 0.0;

        for seed in 0..200 {
            let mut tree = BagTree::new(n);
            let mut rng = Rng::new(seed);
            let threshold = 1.0 / params.lambda;

            for t in 0..300 {
                tree.do_stage(&params, t, SepModel::Formal, &mut rng);

                for level in 0..=tree.max_level {
                    if (t + 1 + level) % 2 != 0 { continue; }
                    let b = params.capacity(n, t + 1, level);

                    for idx in 0..(1usize << level) {
                        if let Some(items) = tree.bags.get(&(level, idx)) {
                            if items.is_empty() { continue; }
                            let count = tree.j_stranger_count(items, level, idx, 1);
                            let bound = params.lambda * b;
                            if bound > 0.01 {
                                let r = count as f64 / bound;
                                if r > n_max { n_max = r; }
                                if r > formal_max { formal_max = r; }
                            }
                        }
                    }
                }

                let leaf_cap = params.capacity(n, t + 1, tree.max_level);
                if leaf_cap < threshold { break; }
            }
        }

        println!("    n={:5}: max_1stranger_ratio={:.6}", n, n_max);
    }
    println!("    Formal global max: {:.6}", formal_max);
}

/// === RISK REDUCTION TEST E ===
/// Parameter sensitivity sweep: vary A, ν, λ, ε and check which constraints
/// are tight, what the margin is, and whether the invariant holds.
fn test_parameter_sensitivity() {
    println!("\n=== Test E: Parameter sensitivity sweep ===");

    // Sweep 1: vary A with lambda=eps=1/99, nu adjusted to satisfy constraints
    println!("  Sweep 1: Vary A (lambda=eps=1/99)");
    println!("    {:>6} {:>8} {:>8} {:>8} {:>8} {:>8} {:>8}",
        "A", "nu_min", "C3_lhs", "C4j>1", "C4j=1", "margin%", "inv_ok");

    for a_int in [2, 3, 5, 8, 10, 15, 20, 30, 50] {
        let a = a_int as f64;
        let e = 1.0 / 99.0;
        let l = 1.0 / 99.0;

        // Minimum nu from constraints
        let c3_rhs = 4.0 * l * a + 5.0 / (2.0 * a);
        let c4gt1_rhs = 2.0 * a * e + 1.0 / a;
        let c4eq1_lhs = 2.0*l*e*a + e*l/a + e/(2.0*a)
            + 2.0*l*e*a / (1.0 - (2.0*e*a).powi(2))
            + 1.0 / (8.0*a*a*a - 2.0*a);
        let c4eq1_rhs = c4eq1_lhs / l; // nu >= c4eq1_lhs / lambda

        let nu_min = c3_rhs.max(c4gt1_rhs).max(c4eq1_rhs);
        let nu = (nu_min + 0.01).min(0.99);
        let margin = 1.0 - nu_min / nu;

        // Test invariant at this point
        let params = Params { a, nu, lambda: l, eps: e };
        let model = SepModel::Adversarial { lambda: l };
        let n = 1024;
        let inv_ok = match run_simulation(n, &params, 300, model, 42, false) {
            Ok(_) => true,
            Err(_) => false,
        };

        println!("    {:>6.0} {:>8.4} {:>8.4} {:>8.4} {:>8.6} {:>7.1}% {:>8}",
            a, nu_min, c3_rhs, c4gt1_rhs, c4eq1_rhs, margin * 100.0, inv_ok);
    }

    // Sweep 2: vary epsilon with A=10, lambda=eps, nu adjusted
    println!("  Sweep 2: Vary eps (A=10, lambda=eps)");
    println!("    {:>10} {:>8} {:>8} {:>8} {:>8} {:>8}",
        "eps", "nu_min", "C3_lhs", "C4j>1", "C4j=1", "margin%");

    for &eps_denom in &[200, 150, 100, 99, 80, 60, 50, 40, 30, 25, 20] {
        let e = 1.0 / eps_denom as f64;
        let l = e;
        let a = 10.0;

        if (2.0 * e * a).abs() >= 1.0 { continue; } // geometric series diverges

        let c3_rhs = 4.0 * l * a + 5.0 / (2.0 * a);
        let c4gt1_rhs = 2.0 * a * e + 1.0 / a;
        let c4eq1_lhs = 2.0*l*e*a + e*l/a + e/(2.0*a)
            + 2.0*l*e*a / (1.0 - (2.0*e*a).powi(2))
            + 1.0 / (8.0*a*a*a - 2.0*a);
        let c4eq1_rhs = c4eq1_lhs / l;

        let nu_min = c3_rhs.max(c4gt1_rhs).max(c4eq1_rhs);
        let margin = if nu_min < 1.0 { 1.0 - nu_min } else { -1.0 };

        println!("    {:>10.6} {:>8.4} {:>8.4} {:>8.4} {:>8.4} {:>7.1}%",
            e, nu_min, c3_rhs, c4gt1_rhs, c4eq1_rhs, margin * 100.0);
    }

    // Sweep 3: decouple lambda and eps
    println!("  Sweep 3: Decouple lambda and eps (A=10)");
    println!("    {:>8} {:>8} {:>8} {:>8} {:>8}",
        "lambda", "eps", "nu_min", "tight", "feas");

    for &lam_d in &[50, 80, 99, 150, 200] {
        for &eps_d in &[50, 80, 99, 150, 200] {
            let l = 1.0 / lam_d as f64;
            let e = 1.0 / eps_d as f64;
            let a = 10.0;

            if (2.0 * e * a).abs() >= 1.0 { continue; }

            let c3_rhs = 4.0 * l * a + 5.0 / (2.0 * a);
            let c4gt1_rhs = 2.0 * a * e + 1.0 / a;
            let c4eq1_lhs = 2.0*l*e*a + e*l/a + e/(2.0*a)
                + 2.0*l*e*a / (1.0 - (2.0*e*a).powi(2))
                + 1.0 / (8.0*a*a*a - 2.0*a);
            let c4eq1_rhs = c4eq1_lhs / l;

            let nu_min = c3_rhs.max(c4gt1_rhs).max(c4eq1_rhs);
            let tight = if nu_min == c3_rhs { "C3" }
                else if nu_min == c4gt1_rhs { "C4>1" }
                else { "C4=1" };
            let feas = if nu_min < 1.0 { "yes" } else { "NO" };

            println!("    1/{:<5} 1/{:<5} {:>8.4} {:>8} {:>8}",
                lam_d, eps_d, nu_min, tight, feas);
        }
    }
}

fn main() {
    test_initial_invariant_parity();
    test_seiferas_params();
    test_verbose_small();
    test_uniform_size_detail();
    test_capacity_sublemmas();
    test_convergence_rate();
    test_controlled_displacement();
    test_constraint_violations();
    test_various_parameters();
    // New tests for separator models
    test_formal_sep_validity();
    test_formal_sep_invariant();
    test_stranger_bound_tightness();
    test_halving_errors();
    test_adversarial_sep_invariant();
    test_model_comparison();
    // Source decomposition tests
    test_shifted_vs_unshifted();
    test_source_decomposition();
    test_j_gt_1_source_decomposition();
    test_source_bounds_stress();
    // Risk reduction tests A-E
    test_rebagging_flow_validation();       // A: rebagging detail
    test_end_to_end_sorting();              // D: end-to-end sorting check
    test_tight_bound_ratios();              // B: all clause ratios
    test_1stranger_counterexample_search(); // C: counterexample search
    test_parameter_sensitivity();           // E: parameter sweep
}
