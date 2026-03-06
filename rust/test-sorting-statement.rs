#!/usr/bin/env -S cargo +nightly -Zscript
//! Targeted analysis of `separatorSortingNetwork_sorts` statement correctness.
//!
//! Key findings from the full test:
//! 1. hstages:True is WRONG (0 stages = identity, doesn't sort)
//! 2. Zero strangers ↔ sorted FAILS for non-power-of-2 sizes
//! 3. Perfect separator sorts with 1 stage (correct for powers of 2)
//!
//! This script digs deeper into:
//! - WHY zero-strangers doesn't imply sorted for non-power-of-2
//! - The wire↔bag bridge: how separator execution relates to concreteSplit
//! - What the CORRECT theorem statement should be
//! - Whether `separatorStage` has the right chunking structure

fn bag_size(n: usize, level: usize) -> usize {
    n >> level
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

fn max_level(n: usize) -> usize {
    if n <= 1 { 0 } else { (n as f64).log2().floor() as usize }
}

fn is_sorted(perm: &[usize]) -> bool {
    perm.windows(2).all(|w| w[0] <= w[1])
}

/// Analyze zero-stranger failure at n=6
fn analyze_n6_failure() {
    println!("=== Analysis: zero strangers ≠ sorted for n=6 ===\n");

    let n = 6;
    let ml = max_level(n); // floor(log2(6)) = 2
    println!("n={}, maxLevel={}", n, ml);
    println!("bagSize: level 0 = {}, level 1 = {}, level 2 = {}",
             bag_size(n, 0), bag_size(n, 1), bag_size(n, 2));
    println!("Number of bags: level 0: {}, level 1: {}, level 2: {}",
             1, 2, 4);

    // The counterexample: perm=[0,1,2,3,5,4]
    let perm = vec![0, 1, 2, 3, 5, 4];
    println!("\nCounterexample: perm={:?}", perm);
    println!("Is sorted: {}", is_sorted(&perm));

    for level in 0..=ml {
        let bs = bag_size(n, level);
        if bs == 0 { continue; }
        let num_bags = 1usize << level;
        for idx in 0..num_bags {
            let start = idx * bs;
            let end = ((idx + 1) * bs).min(n);
            let items: Vec<usize> = (start..end).map(|w| perm[w]).collect();
            let sc = items.iter().filter(|&&r| is_j_stranger(n, r, level, idx, 1)).count();

            // Show native bag computation for each item
            let natives: Vec<String> = items.iter()
                .map(|&r| format!("{}(nat{})", r, native_bag_idx(n, level, r)))
                .collect();

            println!("  level={} idx={}: wires [{},{}), items={:?} native={} strangers={}",
                     level, idx, start, end, items, natives.join(","), sc);
        }

        // Show uncovered wires
        let covered = num_bags * bs;
        if covered < n {
            println!("  *** UNCOVERED wires [{},{}) at level {} ***",
                     covered, n, level);
            let uncovered: Vec<usize> = (covered..n).map(|w| perm[w]).collect();
            println!("      items in uncovered range: {:?}", uncovered);
        }
    }

    println!("\nRoot cause: bag_size(6,2)={}, num_bags=4, covers 4 wires.",
             bag_size(n, 2));
    println!("Wires 4,5 are NOT in any level-2 bag.");
    println!("Items at wires 4,5 have ranks [5,4] — within the leaf-level");
    println!("chunk boundary but NOT sorted. Zero strangers because");
    println!("the stranger check only covers bags that exist.");
    println!("\nFix: require n = 2^k (all wires covered at all levels).\n");
}

/// Analyze the wire↔bag bridge
fn analyze_wire_bag_bridge() {
    println!("=== Wire↔Bag Bridge Analysis ===\n");

    // Key question: when the separator sorts each chunk,
    // does the result correspond to concreteSplit at the bag level?
    //
    // concreteSplit uses rankInBag (exact rank within bag).
    // The separator approximately sorts within each chunk.
    // For a perfect separator (exact sort), they should match.
    //
    // At stage t, separatorStage divides wires into 2^t chunks.
    // After sorting each chunk, items within each chunk are sorted.
    //
    // concreteSplit at level t, bag idx:
    //   - Items = all items in bag (t, idx)
    //   - Rank = position among items sorted by perm value
    //   - Bottom half → left child, top half → right child
    //
    // Wire-level after separator:
    //   - Chunk [idx*bs, (idx+1)*bs) is sorted
    //   - Bottom half = wires [idx*bs, idx*bs + bs/2) → left child
    //   - Top half = wires [idx*bs + bs/2, (idx+1)*bs) → right child
    //
    // Are these the same? YES, when:
    // 1. Items in bag (t, idx) correspond to wires [idx*bs, (idx+1)*bs)
    //    (i.e., the bag assignment matches the wire partition)
    // 2. The separator sorts exactly (ε=0)
    //
    // Condition 1 holds at t=0 (all items in root = wires [0,n)).
    // After sorting at stage 0, does condition 1 hold at stage 1?
    //
    // At stage 0: sort entire array. Items get their correct sorted order.
    // At stage 1: bags at level 1 are wires [0, n/2) and [n/2, n).
    //   After sorting, items with ranks [0, n/2) are at wires [0, n/2). ✓
    //   Items with ranks [n/2, n) are at wires [n/2, n). ✓
    //   So condition 1 holds.
    //
    // At stage 1: sort each half. Items within each half get sorted.
    // At stage 2: bags at level 2 are quarters.
    //   After sorting each half, items with ranks [0, n/4) are at wires [0, n/4). ✓
    //   Etc. ✓
    //
    // WAIT: this assumes the stages go 0, 1, 2, ... (i.e., stageIdx corresponds
    // to the tree level). But Seiferas says stages ALTERNATE between levels!
    //
    // The Lean `separatorStage` uses stageIdx directly: at stage t, chunks
    // have size n/2^t. This means:
    //   Stage 0: sort whole array (level 0 split)
    //   Stage 1: sort halves (level 1 split)
    //   Stage 2: sort quarters (level 2 split)
    //   ...
    // This is NOT the alternating pattern from Seiferas.
    //
    // Seiferas's paper says (Section 7): at each stage, apply the separator
    // to all ACTIVE bags (those where (t + level) % 2 = 0).
    // The alternating_empty invariant means only one parity of levels is active.
    //
    // But `separatorStage` doesn't use alternating levels. It applies the
    // separator at a FIXED level (stageIdx). This is a DIFFERENT construction
    // from what `concreteSplit` / `SeifInvariant` assumes.

    println!("CRITICAL FINDING: Stage structure mismatch\n");
    println!("separatorStage (Lean):     stage t → chunks of size n/2^t");
    println!("  Stage 0: sort [0,n)");
    println!("  Stage 1: sort [0,n/2), [n/2,n)");
    println!("  Stage 2: sort [0,n/4), [n/4,n/2), [n/2,3n/4), [3n/4,n)");
    println!("  ...");
    println!("  This goes TOP-DOWN through the tree.\n");

    println!("Seiferas invariant (concreteSplit):");
    println!("  Stage t operates on bags at ALL active levels");
    println!("  Active levels: where (t + level) % 2 = 0");
    println!("  At t=0: level 0 active (split root)");
    println!("  At t=1: level 1 active (split children of root)");
    println!("  At t=2: level 0 AND level 2 active");
    println!("  ...");
    println!("  This is an ALTERNATING multi-level pattern.\n");

    println!("The mismatch:");
    println!("  - separatorStage processes ONE level per stage");
    println!("  - concreteSplit processes ALL active levels per stage");
    println!("  - These give DIFFERENT networks!\n");

    println!("Impact on the proof:");
    println!("  Option A: Change separatorStage to match concreteSplit (multi-level)");
    println!("  Option B: Change the invariant to track one-level-per-stage");
    println!("  Option C: The current setup is wrong — separatorStage doesn't");
    println!("            correspond to what concreteSplit describes.\n");

    println!("Severity: This is a STRUCTURAL mismatch, not a minor gap.");
    println!("The proof of separatorSortingNetwork_sorts needs to connect");
    println!("the wire-level execution to the bag-level invariant, and");
    println!("the stage structures don't match.\n");

    // However: verify that the TOP-DOWN approach also works
    println!("Does the top-down approach work empirically?");
    println!("Test: perfect separator, top-down stages, n = 2^k.\n");

    // For n = 2^k with perfect separator:
    // Stage 0: sort whole array → sorted. Done in 1 stage.
    // So the top-down approach trivially works for perfect separator.
    // For imperfect separator: need to check.

    println!("For PERFECT separator: 1 stage suffices (sorts whole array).");
    println!("For IMPERFECT separator: top-down only processes each level ONCE.");
    println!("  Seiferas's alternating stages process each level O(log n) times,");
    println!("  driving stranger counts to 0 exponentially.");
    println!("  Top-down processes each level once → may not converge.\n");
}

/// Verify the gap: separatorStage doesn't match SeifInvariant alternation
fn verify_stage_level_mismatch() {
    println!("=== Stage↔Level Mismatch Verification ===\n");

    // The alternating_empty invariant says: (t + level) % 2 ≠ 0 → empty.
    // At t=0: level 0 is active (0+0=0 even). Level 1 is inactive (0+1=1 odd).
    // At t=1: level 0 inactive (1+0=1 odd). Level 1 active (1+1=2 even).
    // At t=2: level 0 active, level 2 active. Level 1 inactive.
    // At t=3: level 1 active, level 3 active. Level 0 inactive.
    //
    // So at each stage t, ALL levels with same parity as t are active.
    // Seiferas applies the separator to ALL active bags simultaneously.
    //
    // separatorStage applies separator only to level stageIdx.
    //
    // These are fundamentally different!

    let n = 16;
    let ml = max_level(n);
    println!("n={}, maxLevel={}\n", n, ml);

    println!("{:>5} | Seiferas active levels | separatorStage level", "stage");
    println!("------+------------------------+---------------------");
    for t in 0..10 {
        let active: Vec<usize> = (0..=ml).filter(|&l| (t + l) % 2 == 0).collect();
        println!("{:>5} | {:?}{} | {}", t,
                 active,
                 " ".repeat(22usize.saturating_sub(format!("{:?}", active).len())),
                 t);
    }

    println!("\nSeiferas: each level gets processed every OTHER stage.");
    println!("  Level 0 processed at stages 0, 2, 4, 6, ...");
    println!("  Level 1 processed at stages 1, 3, 5, 7, ...");
    println!("  Level 2 processed at stages 2, 4, 6, 8, ...");
    println!("  Total: each level processed ~T/2 times in T stages.\n");

    println!("separatorStage: each level processed ONCE.");
    println!("  Level 0 at stage 0, level 1 at stage 1, ...");
    println!("  Total: each level processed 1 time.\n");

    println!("This means separatorStage can't drive convergence for ε > 0.");
    println!("With imperfect separator, each application has ε errors.");
    println!("Seiferas's repeated processing drives errors to ε^(T/2) → 0.");
    println!("separatorStage's single processing leaves ε errors.\n");

    // BUT: can separatorStage be ITERATED?
    println!("HOWEVER: separatorSortingNetwork repeats stages 0..numStages-1.");
    println!("So level 0 IS processed multiple times (at stages 0, numChunks, ...).");
    println!("Wait, no: stages go 0, 1, 2, ..., numStages-1.");
    println!("Stage 0 always processes level 0 (chunks of size n).");
    println!("Stage 1 always processes level 1 (chunks of size n/2).");
    println!("After stage maxLevel, stages go BEYOND the tree depth!");
    println!("Stage maxLevel+1: chunks of size n/2^(maxLevel+1) = 1.");
    println!("Stages beyond maxLevel are NO-OPS (chunk size ≤ 1).\n");

    println!("CONCLUSION: With current separatorStage, each tree level is");
    println!("processed EXACTLY ONCE. This is insufficient for convergence");
    println!("with ε > 0 separator. The construction needs to be iterated.\n");

    println!("FIX OPTIONS:");
    println!("1. Change separatorStage to process ALL active levels (match Seiferas)");
    println!("2. Change separatorSortingNetwork to cycle through levels repeatedly");
    println!("   (e.g., stage t processes level t % (maxLevel + 1))");
    println!("3. The current code is actually correct IF stages repeat, but the");
    println!("   stage index modular interpretation is needed.");
    println!();

    // Verify option 2: cycling
    println!("Checking option 2: Does stage t process level (t mod maxLevel+1)?");
    println!("separatorStage at stage t uses chunk_size = n / 2^t.");
    println!("For t > maxLevel: chunk_size = n / 2^t = 0 (integer division).");
    println!("So stages beyond maxLevel are truly no-ops.\n");

    println!("This confirms: the current separatorSortingNetwork processes");
    println!("each level at most once. For numStages > maxLevel, extra stages");
    println!("do nothing. The network is equivalent to sorting the tree top-down.\n");

    println!("For the PROOF: either fix separatorStage to iterate, or");
    println!("recognize that with a PERFECT separator (ε=0), one pass suffices.");
    println!("The theorem as stated (with sep having IsSeparator property)");
    println!("needs an iterating stage structure.\n");
}

/// What should the correct statement be?
fn correct_statement_analysis() {
    println!("=== Correct Statement for separatorSortingNetwork_sorts ===\n");

    println!("Current (WRONG) statement:");
    println!("  theorem separatorSortingNetwork_sorts");
    println!("    (sep : SeparatorFamily gam eps d_sep) (numStages : ℕ)");
    println!("    (hstages : True)");
    println!("    (v : Fin n → Bool) :");
    println!("    Monotone ((separatorSortingNetwork n sep numStages).exec v)\n");

    println!("Issues:");
    println!("  1. hstages : True — FALSE (0 stages = identity, not sorted)");
    println!("  2. No n = 2^k requirement — zero-strangers≠sorted for non-power-of-2");
    println!("  3. separatorStage processes each level once — doesn't converge for ε>0");
    println!("  4. No constraint on gam (γ) — need γ to match the tree structure\n");

    println!("CORRECT statement should be:");
    println!("  theorem separatorSortingNetwork_sorts");
    println!("    (sep : SeparatorFamily gam eps d_sep)");
    println!("    (hn : ∃ k, n = 2 ^ k)");
    println!("    (hgam : gam = 1 / 2)  -- or gam ≤ 1/2");
    println!("    (heps : eps < some_threshold)");
    println!("    (numStages : ℕ)");
    println!("    (hstages : numStages ≥ convergence_bound n)");
    println!("    (v : Fin n → Bool) :");
    println!("    Monotone ((separatorSortingNetwork n sep numStages).exec v)\n");

    println!("  AND: separatorStage needs to be fixed to cycle through levels");
    println!("  (currently processes each level once; needs repeated processing).\n");

    println!("  The separatorStage fix: change stageIdx in the stage construction to");
    println!("  stageIdx % (maxLevel n + 1)  or  restructure to match Seiferas's");
    println!("  alternating-level pattern.\n");

    println!("  Alternative: keep the current top-down structure but change the");
    println!("  INVARIANT to match it (track progress per-level, not alternating).\n");

    println!("RISK SUMMARY for B4 (separatorSortingNetwork_sorts):");
    println!("  - Statement bug: hstages : True → EASY FIX");
    println!("  - Power-of-2 requirement: add hn : ∃ k, n = 2^k → EASY FIX");
    println!("  - Stage structure mismatch → HARD FIX (architecture change)");
    println!("  - Wire↔bag bridge → depends on stage structure fix");
}

fn main() {
    analyze_n6_failure();
    analyze_wire_bag_bridge();
    verify_stage_level_mismatch();
    correct_statement_analysis();
}
