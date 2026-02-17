/-
  # Halver Network Correctness

  Proves that the recursive halving network produces ε·depth-nearsorted output
  for every permutation input.
  (AKS Section 4, page 5: "it is easy to see")

  ## Proof outline

  The proof tracks individual element trajectories through the recursive halving:

  1. **Correctly classified.** Value `b` is "correctly classified at level `l`" if
     the halver at level `l` places it in the sub-interval containing `b.val` at the
     level-`(l+1)` partition. Since level `l` splits sub-intervals of size `n/2^l`
     into halves of size `n/2^(l+1)`, correct classification means `b` goes to the
     half containing position `b.val`.

  2. **All-correct → near target.** If `b` is correctly classified at every level
     `0, ..., depth-1`, then after `depth` levels, `b` is at a position within
     `n/2^depth` of `b.val`.

  3. **Blow-up covers displacement.** The hypothesis `1 ≤ ε · depth · 2^depth`
     ensures `n/2^depth ≤ ⌊(ε · depth) · n⌋`, so correctly-classified values
     are within the blow-up radius.

  4. **Per-level misclassification bound.** At level `l`, the halver at the
     boundary sub-interval (straddling the threshold for initial segment `k`)
     misclassifies at most `ε · k` values in `[0, k)`. This uses `IsEpsilonHalver`
     applied to the local permutation within the sub-interval.

  5. **Union bound.** Each value is assigned to at most one level (the first level
     where it's misclassified). Total misclassified ≤ `Σ_l ε·k = depth · ε · k`.

  6. **Assembly.** `|S \ Sδ.image w| ≤ (# misclassified values < k) ≤ δ · k`.

  Key difficulty: Step 4 requires connecting the halver's LOCAL guarantee (on
  the sub-interval's values) to the GLOBAL misclassification count. The `exec`
  on the sub-interval acts on the values via their local ranking, and
  `exec_comp_monotone` bridges local and global behavior.
-/

import AKS.Nearsort.Construction

open Finset BigOperators


/-! **Correctness infrastructure** -/

/-- The state after applying the first `levels` levels of the halver network. -/
def halverNetworkPartial (n : ℕ)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (levels : ℕ) : ComparatorNetwork n :=
  { comparators := (List.range levels).flatMap fun l ↦
      (halverAtLevel n halvers l).comparators }

/-- The initial-segment nearsort bound: after `depth` levels of recursive halving,
    at most `ε · depth · k` elements of each initial segment `[0, k)` are displaced
    beyond the blow-up radius. -/
theorem halverNetwork_initialNearsorted {n : ℕ} (ε : ℝ) (depth d : ℕ)
    (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hdepth : (1 : ℝ) ≤ ε * ↑depth * 2 ^ depth)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (hhalvers : ∀ m, IsEpsilonHalver (halvers m) ε)
    (hhalver_size : ∀ m, (halvers m).size ≤ m * d)
    (v : Equiv.Perm (Fin n)) :
    InitialNearsorted ((halverNetwork n halvers depth).exec v) (ε * ↑depth) := by
  sorry

/-- The dual: final-segment nearsortedness follows from `EpsilonFinalHalved`
    (which is part of `IsEpsilonHalver`). The same per-level argument applies
    with reversed order. -/
theorem halverNetwork_finalNearsorted {n : ℕ} (ε : ℝ) (depth d : ℕ)
    (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hdepth : (1 : ℝ) ≤ ε * ↑depth * 2 ^ depth)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (hhalvers : ∀ m, IsEpsilonHalver (halvers m) ε)
    (hhalver_size : ∀ m, (halvers m).size ≤ m * d)
    (v : Equiv.Perm (Fin n)) :
    FinalNearsorted ((halverNetwork n halvers depth).exec v) (ε * ↑depth) := by
  sorry
