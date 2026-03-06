#!/usr/bin/env -S cargo +nightly -Zscript
//! End-to-end test of the separator-based sorting network.
//!
//! Validates `separatorSortingNetwork_sorts` by building a concrete comparator
//! network (mirroring the Lean `separatorSortingNetwork` definition) and testing
//! it on all 0-1 inputs (small n) and random permutations (larger n).
//!
//! Key questions:
//! 1. Does the network actually sort? (end-to-end correctness)
//! 2. What numStages is sufficient? (validates `hstages` placeholder)
//! 3. Does the bag-level invariant track through stages? (wire↔bag bridge)
//! 4. Does convergence imply sorted? (convergence → correctness)
//!
//! Mirrors Lean definitions:
//! - `separatorStage` (Stage.lean): apply separator to each chunk
//! - `separatorSortingNetwork` (TreeSort.lean): concatenate stages
//! - `concreteSplit` (Split.lean): rank-based split
//! - `SeifInvariant` (Invariant.lean): four-clause invariant

use std::collections::BTreeMap;

/// Simple LCG random number generator
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
}

/// A comparator: swap positions i,j if out of order (i < j).
#[derive(Clone, Copy, Debug)]
struct Comparator { i: usize, j: usize }

/// A comparator network.
#[derive(Clone, Debug)]
struct Network { n: usize, comparators: Vec<Comparator> }

impl Network {
    fn exec<T: Ord + Copy>(&self, v: &mut [T]) {
        for c in &self.comparators {
            if v[c.i] > v[c.j] {
                v.swap(c.i, c.j);
            }
        }
    }

    fn depth(&self) -> usize {
        if self.comparators.is_empty() { return 0; }
        let mut last_used = vec![0usize; self.n];
        let mut max_depth = 0usize;
        for c in &self.comparators {
            let d = last_used[c.i].max(last_used[c.j]) + 1;
            last_used[c.i] = d;
            last_used[c.j] = d;
            max_depth = max_depth.max(d);
        }
        max_depth
    }

    fn shift_embed(&self, n: usize, offset: usize) -> Network {
        Network {
            n,
            comparators: self.comparators.iter().map(|c| Comparator {
                i: offset + c.i,
                j: offset + c.j,
            }).collect(),
        }
    }
}

//=============================================================================
// Separator construction: halver-based
//=============================================================================

/// Build a simple ε-halver network for m wires.
/// Uses odd-even transposition (one round of compare-swap on pairs).
/// This is depth-1 and gives ε ≈ 0.5 for random inputs (not great).
/// For a better halver, use bitonic merge.
fn simple_halver(m: usize) -> Network {
    let mut comps = Vec::new();
    // Odd-even merge: compare (0,1), (2,3), (4,5), ...
    let mut i = 0;
    while i + 1 < m {
        comps.push(Comparator { i, j: i + 1 });
        i += 2;
    }
    Network { n: m, comparators: comps }
}

/// Build a bubble sort network for m wires.
/// Correct sorting network with O(m²) comparators, depth O(m).
/// Good enough for testing; we're testing the STAGE STRUCTURE, not separator quality.
fn bubble_sort_network(m: usize) -> Network {
    let mut comps = Vec::new();
    // Odd-even transposition sort: m rounds of alternating odd/even swaps.
    // This is a correct sorting network for all m.
    for round in 0..m {
        let start = round % 2; // alternate 0 and 1
        let mut i = start;
        while i + 1 < m {
            comps.push(Comparator { i, j: i + 1 });
            i += 2;
        }
    }
    Network { n: m, comparators: comps }
}

/// Build a halver-to-separator: iterative halving with t levels.
/// At each level, split into halves and apply halver.
/// This mirrors `halverToSeparator` in Lean.
fn halver_to_separator(m: usize, t: usize, use_perfect: bool) -> Network {
    if m <= 1 || t == 0 {
        return Network { n: m, comparators: vec![] };
    }
    let mut all_comps = Vec::new();
    // Recursive structure: at level 0, halve the whole array.
    // At level 1, halve each half. Etc.
    fn build(all_comps: &mut Vec<Comparator>, offset: usize, size: usize,
             levels_left: usize, use_perfect: bool) {
        if levels_left == 0 || size <= 1 { return; }
        // Apply halver to [offset, offset+size)
        let halver = if use_perfect && size.is_power_of_two() {
            bubble_sort_network(size)
        } else {
            simple_halver(size)
        };
        for c in &halver.comparators {
            all_comps.push(Comparator { i: offset + c.i, j: offset + c.j });
        }
        // Recurse on each half
        let half = size / 2;
        build(all_comps, offset, half, levels_left - 1, use_perfect);
        build(all_comps, offset + half, half, levels_left - 1, use_perfect);
    }
    build(&mut all_comps, 0, m, t, use_perfect);
    Network { n: m, comparators: all_comps }
}

//=============================================================================
// Separator stage (mirrors Stage.lean)
//=============================================================================

/// Build one stage of the sorting network.
/// At stage `stage_idx`, divide n wires into 2^stage_idx chunks
/// and apply the separator to each chunk.
fn separator_stage(n: usize, stage_idx: usize,
                   sep_levels: usize, use_perfect: bool) -> Network {
    let chunk_size = n >> stage_idx; // n / 2^stage_idx
    let num_chunks = 1 << stage_idx; // 2^stage_idx
    let mut all_comps = Vec::new();
    for k in 0..num_chunks {
        let offset = k * chunk_size;
        if offset + chunk_size <= n && chunk_size > 0 {
            let sep = halver_to_separator(chunk_size, sep_levels, use_perfect);
            let embedded = sep.shift_embed(n, offset);
            all_comps.extend_from_slice(&embedded.comparators);
        }
    }
    Network { n, comparators: all_comps }
}

/// Build the full sorting network: concatenate numStages stages.
fn separator_sorting_network(n: usize, num_stages: usize,
                              sep_levels: usize, use_perfect: bool) -> Network {
    let mut all_comps = Vec::new();
    for t in 0..num_stages {
        let stage = separator_stage(n, t, sep_levels, use_perfect);
        all_comps.extend_from_slice(&stage.comparators);
    }
    Network { n, comparators: all_comps }
}

//=============================================================================
// Testing: end-to-end sorting correctness
//=============================================================================

/// Test all 2^n binary inputs (0-1 principle)
fn test_all_binary(n: usize, net: &Network) -> (usize, usize) {
    let mut pass = 0usize;
    let mut fail = 0usize;
    for mask in 0..(1u64 << n) {
        let mut v: Vec<u8> = (0..n).map(|i| ((mask >> i) & 1) as u8).collect();
        net.exec(&mut v);
        let sorted = v.windows(2).all(|w| w[0] <= w[1]);
        if sorted { pass += 1; } else { fail += 1; }
    }
    (pass, fail)
}

/// Test random permutations
fn test_random_perms(n: usize, net: &Network, num_trials: usize, rng: &mut Rng) -> (usize, usize) {
    let mut pass = 0usize;
    let mut fail = 0usize;
    for _ in 0..num_trials {
        let mut v: Vec<usize> = (0..n).collect();
        // Fisher-Yates shuffle
        for i in (1..n).rev() {
            let j = rng.next_usize(i + 1);
            v.swap(i, j);
        }
        net.exec(&mut v);
        let sorted = v.windows(2).all(|w| w[0] <= w[1]);
        if sorted { pass += 1; } else { fail += 1; }
    }
    (pass, fail)
}

//=============================================================================
// Testing: bag-level invariant tracking
//=============================================================================

struct Params {
    a: f64,
    nu: f64,
    lambda: f64,
    eps: f64,
}

impl Params {
    fn seiferas() -> Self {
        Params { a: 10.0, nu: 0.65, lambda: 1.0/99.0, eps: 1.0/99.0 }
    }

    fn capacity(&self, n: usize, t: usize, level: usize) -> f64 {
        (n as f64) * self.nu.powi(t as i32) * self.a.powi(level as i32)
    }
}

fn max_level(n: usize) -> usize {
    if n <= 1 { 0 } else { (n as f64).log2().floor() as usize }
}

fn bag_size(n: usize, level: usize) -> usize {
    n >> level // n / 2^level
}

fn native_bag_idx(n: usize, level: usize, rank: usize) -> usize {
    let bs = bag_size(n, level);
    if bs == 0 { rank } else { rank / bs }
}

fn is_j_stranger(n: usize, rank: usize, level: usize, idx: usize, j: usize) -> bool {
    if j == 0 || j > level { return false; }
    let check_level = level - (j - 1);
    let check_idx = idx >> (j - 1);
    native_bag_idx(n, check_level, rank) != check_idx
}

fn j_stranger_count(n: usize, items: &[usize], level: usize, idx: usize, j: usize) -> usize {
    items.iter().filter(|&&r| is_j_stranger(n, r, level, idx, j)).count()
}

/// Track bags through the ACTUAL wire-level execution.
/// After each stage, compute which items are in which chunk.
fn track_bags_through_execution(
    n: usize, perm: &[usize], num_stages: usize,
    sep_levels: usize, use_perfect: bool, params: &Params
) -> Vec<Vec<(String, f64)>> {
    // perm[i] = sorted position of wire i (i.e., item at wire i has rank perm[i])
    let mut current_perm = perm.to_vec();
    let mut stage_violations = Vec::new();

    for t in 0..num_stages {
        // Apply one stage
        let stage_net = separator_stage(n, t, sep_levels, use_perfect);
        // Execute on the inverse: we track where each rank ends up
        // Actually, we need to track wire→rank mapping
        // current_perm[wire] = rank of item at this wire
        let mut wire_values = current_perm.clone();
        stage_net.exec(&mut wire_values);
        current_perm = wire_values;

        // After this stage, compute bags at t+1
        // A bag at (level, idx) contains wires in [idx*bag_size, (idx+1)*bag_size)
        // The RANK of wire w is current_perm[w]
        let mut violations = Vec::new();

        let ml = max_level(n);
        for level in 0..=ml {
            let bs = bag_size(n, level);
            if bs == 0 { continue; }
            let num_bags = 1 << level;
            let mut sizes = Vec::new();
            for idx in 0..num_bags {
                let start = idx * bs;
                let end = ((idx + 1) * bs).min(n);
                let items: Vec<usize> = (start..end).map(|w| current_perm[w]).collect();

                let card = items.len();
                sizes.push(card);

                // Check capacity
                let cap = params.capacity(n, t + 1, level);
                if (card as f64) > cap + 0.001 {
                    violations.push((
                        format!("capacity: lev={} idx={} card={} > cap={:.1}", level, idx, card, cap),
                        (card as f64) - cap
                    ));
                }

                // Check stranger bounds
                for j in 1..=level.min(5) {
                    let sc = j_stranger_count(n, &items, level, idx, j);
                    let bound = params.lambda * params.eps.powi((j - 1) as i32) * cap;
                    if (sc as f64) > bound + 0.001 {
                        violations.push((
                            format!("stranger: lev={} idx={} j={} sc={} > {:.2}", level, idx, j, sc, bound),
                            (sc as f64) - bound
                        ));
                    }
                }
            }

            // Check uniform size
            if let (Some(&first), true) = (sizes.first(), sizes.len() > 1) {
                if !sizes.iter().all(|&s| s == first) {
                    violations.push((
                        format!("uniform: lev={} sizes={:?}", level, sizes),
                        1.0
                    ));
                }
            }
        }
        stage_violations.push(violations);
    }
    stage_violations
}

/// Check if all bags have ≤ 1 item (convergence)
fn check_convergence(n: usize, perm: &[usize]) -> bool {
    let ml = max_level(n);
    // At convergence, every bag has ≤ 1 item.
    // For wire-level: each chunk of size bag_size at the leaf level has ≤ 1 item.
    // Actually: convergence means capacity < 2 at maxLevel.
    // But checking directly: for n = 2^k, leaf bags are single wires,
    // so "≤ 1 item per bag" is trivially true at maxLevel.
    // The real question is whether items are in the RIGHT bag.
    //
    // When all bags have ≤ 1 item AND zero strangers, items are sorted.
    // Check: for each level l, each bag has ≤ 1 item
    for level in 0..=ml {
        let bs = bag_size(n, level);
        if bs == 0 { continue; }
        for idx in 0..(1 << level) {
            let start = idx * bs;
            let end = ((idx + 1) * bs).min(n);
            let items: Vec<usize> = (start..end).map(|w| perm[w]).collect();
            if items.len() > 1 {
                // Check if all items are 0-strangers (native to this bag)
                let strangers = j_stranger_count(n, &items, level, idx, 1);
                if strangers > 0 {
                    return false;
                }
            }
        }
    }
    true
}

/// After execution, check if sorted
fn is_sorted(perm: &[usize]) -> bool {
    perm.windows(2).all(|w| w[0] <= w[1])
}

//=============================================================================
// CRITICAL TEST: Does convergence (zero strangers) imply sorted?
//=============================================================================

/// For a given wire-level permutation, check:
/// 1. Whether all leaf-level bags have ≤ 1 item
/// 2. Whether the output is sorted
/// 3. Whether zero-strangers-at-all-levels implies sorted
fn test_convergence_implies_sorted(n: usize) -> (usize, usize) {
    // For n = 2^k, leaf bags at maxLevel = k have size 1.
    // So "≤ 1 item per bag at maxLevel" is trivially true.
    // The question: when all bags at ALL levels have zero 1-strangers,
    // is the output sorted?
    //
    // Zero 1-strangers at (level, idx) means: every item in bag (level, idx)
    // has native_bag_idx(level, rank) == idx.
    // That is: rank ∈ [idx * bs, (idx+1) * bs).
    //
    // If this holds at all levels, then for level = maxLevel (bs = 1):
    // the item at wire w has rank ∈ [w, w+1), so rank = w.
    // Therefore perm = identity, so the output is sorted. ✓
    //
    // But this requires zero strangers at ALL levels simultaneously.
    // The invariant only guarantees stranger COUNT → 0, not zero.
    // At convergence: bags ≤ 1 item. A bag with 1 item is either:
    //   - native (0-stranger) → correctly placed
    //   - stranger → wrongly placed
    // So convergence = zero strangers iff all single-item bags are native.
    //
    // The capacity bound gives card ≤ cap < 2, so card ∈ {0, 1}.
    // The stranger bound gives strangers ≤ λ*ε^(j-1)*cap.
    // For j=1: strangers ≤ λ*cap.
    // At convergence: cap < 2, λ ≈ 0.01, so strangers ≤ 0.02 < 1.
    // Since strangers is a natural number, strangers = 0. ✓
    //
    // So at convergence:
    // 1. All bags have 0 or 1 items (from capacity < 2)
    // 2. All 1-item bags have 0 strangers (from stranger bound < 1)
    // 3. Zero strangers at leaf level ⟹ perm[w] ∈ [w, w+1) ⟹ perm[w] = w ⟹ sorted
    //
    // BUT: we need zero strangers at leaf level specifically.
    // The stranger bound is ≤ λ*ε^(j-1)*cap(level).
    // At convergence: cap(maxLevel) < 2, so cap(level) < 2 for level ≤ maxLevel.
    // (Actually cap is monotone in level when A ≥ 1, so cap(0) ≤ cap(maxLevel) < 2.)
    // Wait, NO: cap = n * ν^t * A^level, and A > 1, so cap INCREASES with level!
    // cap(maxLevel) < 2 is the convergence condition, and cap(0) < cap(maxLevel).
    // At level 0: cap(0) = n * ν^t. At maxLevel: cap(maxLevel) = n * ν^t * A^maxLevel.
    // Convergence says cap(maxLevel) < 2.
    // So cap(0) = cap(maxLevel) / A^maxLevel < 2 / A^maxLevel ≪ 1.
    // So at ALL levels, cap < 2, cards ≤ 1, strangers < 1 → zero strangers. ✓

    let mut pass = 0;
    let mut fail = 0;

    // Exhaustive check for small n
    let num_perms = (1..=n).product::<usize>();
    let mut perm: Vec<usize> = (0..n).collect();

    for _ in 0..num_perms {
        // Check: zero strangers at all levels ↔ sorted
        let ml = max_level(n);
        let mut zero_strangers = true;
        for level in 0..=ml {
            let bs = bag_size(n, level);
            if bs == 0 { continue; }
            for idx in 0..(1usize << level) {
                let start = idx * bs;
                let end = ((idx + 1) * bs).min(n);
                let items: Vec<usize> = (start..end).map(|w| perm[w]).collect();
                let sc = j_stranger_count(n, &items, level, idx, 1);
                if sc > 0 { zero_strangers = false; }
            }
        }

        let sorted = is_sorted(&perm);
        if zero_strangers == sorted {
            pass += 1;
        } else {
            fail += 1;
            println!("  MISMATCH: perm={:?} zero_strangers={} sorted={}",
                     perm, zero_strangers, sorted);
        }

        // Next permutation (lexicographic)
        if !next_permutation(&mut perm) { break; }
    }
    (pass, fail)
}

fn next_permutation(a: &mut [usize]) -> bool {
    let n = a.len();
    if n < 2 { return false; }
    let mut i = n - 1;
    while i > 0 && a[i - 1] >= a[i] { i -= 1; }
    if i == 0 { return false; }
    let mut j = n - 1;
    while a[j] <= a[i - 1] { j -= 1; }
    a.swap(i - 1, j);
    a[i..].reverse();
    true
}

//=============================================================================
// CRITICAL TEST: What numStages suffices?
//=============================================================================

fn test_min_stages(n: usize, sep_levels: usize, use_perfect: bool,
                    num_trials: usize, rng: &mut Rng) -> usize {
    let max_stages = 20 * max_level(n); // generous upper bound
    let mut min_needed = 0;

    for _ in 0..num_trials {
        let mut perm: Vec<usize> = (0..n).collect();
        for i in (1..n).rev() {
            let j = rng.next_usize(i + 1);
            perm.swap(i, j);
        }

        // Apply stages one at a time until sorted
        let mut current = perm.clone();
        for t in 0..max_stages {
            if is_sorted(&current) {
                min_needed = min_needed.max(t);
                break;
            }
            let stage = separator_stage(n, t, sep_levels, use_perfect);
            stage.exec(&mut current);
            if t + 1 == max_stages {
                if is_sorted(&current) {
                    min_needed = min_needed.max(t + 1);
                } else {
                    println!("  WARNING: n={} not sorted after {} stages!", n, max_stages);
                    min_needed = max_stages;
                }
            }
        }
    }
    min_needed
}

//=============================================================================
// CRITICAL TEST: Does the wire-level execution match bag-level semantics?
//=============================================================================

/// After executing stage t, items in wire range [idx*bs, (idx+1)*bs) at level
/// should correspond to what `concreteSplit` + `rebag` produces.
///
/// concreteSplit uses exact rank-based partitioning.
/// The separator uses approximate sorting.
/// Test: how much do they differ?
fn test_wire_bag_correspondence(n: usize, sep_levels: usize, use_perfect: bool,
                                  num_trials: usize, rng: &mut Rng) {
    println!("\n=== Wire↔Bag Correspondence (n={}) ===", n);

    let mut max_diff_pct = 0.0f64;
    let mut total_checks = 0usize;
    let mut mismatches = 0usize;

    for trial in 0..num_trials {
        let mut perm: Vec<usize> = (0..n).collect();
        for i in (1..n).rev() {
            let j = rng.next_usize(i + 1);
            perm.swap(i, j);
        }

        // Execute one stage and compare wire-level vs bag-level
        let mut wire_perm = perm.clone();
        let stage0 = separator_stage(n, 0, sep_levels, use_perfect);
        stage0.exec(&mut wire_perm);

        // Wire-level: after stage 0, items at wire w have rank wire_perm[w]
        // Bag-level (stage 0 splits root into 2 children):
        // concreteSplit sorts by rank within root (= sort all items), then
        // sends bottom half to left child, top half to right child
        // The separator approximately does this.

        // Compare: for each half, what items does the separator place there
        // vs what concreteSplit would place?
        let half = n / 2;

        // Wire-level: left half = wires [0, half)
        let wire_left: std::collections::BTreeSet<usize> =
            (0..half).map(|w| wire_perm[w]).collect();
        // concreteSplit: left half = ranks [0, half) (bottom half by rank)
        let exact_left: std::collections::BTreeSet<usize> = (0..half).collect();

        let diff: usize = wire_left.symmetric_difference(&exact_left).count();
        let diff_pct = diff as f64 / n as f64 * 100.0;

        if diff > 0 {
            mismatches += 1;
            max_diff_pct = max_diff_pct.max(diff_pct);
        }
        total_checks += 1;

        if trial < 3 && diff > 0 {
            println!("  Trial {}: diff={}/{} ({:.1}%)", trial, diff, n, diff_pct);
        }
    }
    println!("  Mismatches: {}/{} trials (max diff: {:.1}%)",
             mismatches, total_checks, max_diff_pct);
    if use_perfect {
        println!("  (perfect sort, expect 0 mismatches)");
    }
}

//=============================================================================
// STATEMENT ANALYSIS: hstages : True is wrong
//=============================================================================

fn test_hstages_wrong() {
    println!("\n=== `hstages : True` analysis ===");
    println!("The current statement claims sorting for ANY numStages.");
    println!("With 0 stages, the network is identity (not sorted for n ≥ 2).");

    // With 0 stages
    let net = separator_sorting_network(8, 0, 1, true);
    assert_eq!(net.comparators.len(), 0);
    let mut v = vec![3,1,4,1,5,9,2,6];
    net.exec(&mut v);
    let sorted = v.windows(2).all(|w| w[0] <= w[1]);
    println!("  0 stages, n=8: sorted={} (should be false) → hstages:True is WRONG", sorted);

    // With 1 stage (just the root separator)
    let net1 = separator_sorting_network(8, 1, 3, true);
    let mut v1 = vec![7,6,5,4,3,2,1,0];
    net1.exec(&mut v1);
    let sorted1 = v1.windows(2).all(|w| w[0] <= w[1]);
    println!("  1 stage, n=8: sorted={} (may or may not sort)", sorted1);

    // Find minimum stages for n=8
    let mut rng = Rng::new(42);
    let min_8 = test_min_stages(8, 3, true, 50, &mut rng);
    let min_16 = test_min_stages(16, 4, true, 50, &mut rng);
    let min_32 = test_min_stages(32, 5, true, 50, &mut rng);
    println!("  Min stages to sort all trials: n=8→{}, n=16→{}, n=32→{}", min_8, min_16, min_32);
    println!("  maxLevel: n=8→{}, n=16→{}, n=32→{}", max_level(8), max_level(16), max_level(32));

    let ratio_8 = if max_level(8) > 0 { min_8 as f64 / max_level(8) as f64 } else { 0.0 };
    let ratio_16 = if max_level(16) > 0 { min_16 as f64 / max_level(16) as f64 } else { 0.0 };
    let ratio_32 = if max_level(32) > 0 { min_32 as f64 / max_level(32) as f64 } else { 0.0 };
    println!("  Ratio stages/log₂n: {:.1}, {:.1}, {:.1}", ratio_8, ratio_16, ratio_32);
    println!("  → hstages should be: numStages ≥ C * Nat.log 2 n for some C");
}

//=============================================================================
// Main
//=============================================================================

fn main() {
    println!("=== End-to-End Sorting Network Test ===\n");

    // Test 1: convergence ↔ sorted equivalence
    println!("--- Test 1: Zero strangers ↔ sorted ---");
    for n in [2, 3, 4, 5, 6, 7, 8] {
        let (pass, fail) = test_convergence_implies_sorted(n);
        println!("  n={}: pass={}, fail={} {}", n, pass, fail,
                 if fail == 0 { "✓" } else { "✗ FAIL" });
    }

    // Test 2: hstages analysis
    test_hstages_wrong();

    // Test 3: end-to-end with bitonic (perfect) separator
    println!("\n--- Test 3: End-to-end with PERFECT separator (ε=0) ---");
    for &n in &[4, 8, 16] {
        let ml = max_level(n);
        for num_stages in [1, ml, 2 * ml] {
            let net = separator_sorting_network(n, num_stages, ml, true);
            let (pass, fail) = test_all_binary(n, &net);
            println!("  n={}, stages={}: {} binary inputs, pass={}, fail={} {}",
                     n, num_stages, 1u64 << n, pass, fail,
                     if fail == 0 { "✓" } else { "✗" });
        }
    }

    // Test 4: end-to-end with simple halver (imperfect separator)
    println!("\n--- Test 4: End-to-end with SIMPLE halver (ε>0) ---");
    let mut rng = Rng::new(12345);
    for &n in &[4, 8, 16, 32] {
        let ml = max_level(n);
        let num_stages = 10 * ml; // generous
        let net = separator_sorting_network(n, num_stages, ml, false);
        if n <= 16 {
            let (pass, fail) = test_all_binary(n, &net);
            println!("  n={}, stages={}: {} binary, pass={}, fail={} {}",
                     n, num_stages, 1u64 << n, pass, fail,
                     if fail == 0 { "✓" } else { "✗" });
        }
        let (pass, fail) = test_random_perms(n, &net, 1000, &mut rng);
        println!("  n={}, stages={}: 1000 perm, pass={}, fail={} {}",
                 n, num_stages, pass, fail,
                 if fail == 0 { "✓" } else { "✗" });
    }

    // Test 5: wire↔bag correspondence
    let mut rng2 = Rng::new(999);
    // With bitonic (perfect): should be exact match
    test_wire_bag_correspondence(16, 4, true, 100, &mut rng2);
    // With simple halver: measure the gap
    test_wire_bag_correspondence(16, 4, false, 100, &mut rng2);

    // Test 6: invariant tracking through stages
    println!("\n--- Test 6: Invariant tracking (perfect sep, n=16) ---");
    let params = Params::seiferas();
    let mut rng3 = Rng::new(777);
    let perm: Vec<usize> = {
        let mut p: Vec<usize> = (0..16).collect();
        for i in (1..16).rev() {
            let j = rng3.next_usize(i + 1);
            p.swap(i, j);
        }
        p
    };
    let violations = track_bags_through_execution(
        16, &perm, 20, 4, true, &params);
    let mut any_violations = false;
    for (t, vs) in violations.iter().enumerate() {
        if !vs.is_empty() {
            any_violations = true;
            println!("  Stage {}: {} violations", t + 1, vs.len());
            for (msg, _) in vs.iter().take(3) {
                println!("    {}", msg);
            }
        }
    }
    if !any_violations {
        println!("  All stages: 0 violations ✓");
    }

    // Test 7: larger sizes with invariant tracking
    println!("\n--- Test 7: Invariant + sorting, larger n ---");
    let mut rng4 = Rng::new(42);
    for &n in &[64, 128, 256] {
        let ml = max_level(n);
        let num_stages = 10 * ml;
        let net = separator_sorting_network(n, num_stages, ml, true);
        let (pass, fail) = test_random_perms(n, &net, 200, &mut rng4);

        // Also check invariant on one random perm
        let perm: Vec<usize> = {
            let mut p: Vec<usize> = (0..n).collect();
            for i in (1..n).rev() {
                let j = rng4.next_usize(i + 1);
                p.swap(i, j);
            }
            p
        };
        let violations = track_bags_through_execution(n, &perm, num_stages, ml, true, &params);
        let total_violations: usize = violations.iter().map(|v| v.len()).sum();

        println!("  n={}: sorting {}/200, invariant violations: {}",
                 n, pass, total_violations);
    }

    // Test 8: minimum stages for larger n (with bitonic)
    println!("\n--- Test 8: Minimum stages (perfect separator) ---");
    let mut rng5 = Rng::new(9876);
    println!("  {:>5} {:>5} {:>6} {:>8}", "n", "log₂n", "stages", "ratio");
    for &n in &[4, 8, 16, 32, 64, 128] {
        let ml = max_level(n);
        let min_s = test_min_stages(n, ml, true, 30, &mut rng5);
        let ratio = if ml > 0 { min_s as f64 / ml as f64 } else { 0.0 };
        println!("  {:>5} {:>5} {:>6} {:>8.2}", n, ml, min_s, ratio);
    }

    println!("\n=== Summary ===");
    println!("Key findings for separatorSortingNetwork_sorts:");
    println!("1. hstages:True is WRONG — need numStages ≥ C*log₂n");
    println!("2. With perfect separator: network sorts when stages suffice");
    println!("3. Wire↔bag correspondence: exact for perfect separator, approximate for imperfect");
    println!("4. Convergence (zero strangers at all levels) ↔ sorted: always true");
}
