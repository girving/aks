/-
  # Separator Sorting Network Assembly

  Assembles the full separator-based sorting network from iterated stages
  (Seiferas 2009, Section 7) and proves the O(log n) depth bound.

  Key results:
  - `separatorSortingNetwork`: computable full sorting network
  - `separatorSortingNetwork_depth_le`: depth = numStages * d_sep
  - `separatorSortingNetwork_sorts`: correctness (via invariant convergence)
-/

import AKS.Bags.Stage

open Finset

/-! **Full Sorting Network** -/

/-- The full separator sorting network: concatenate `numStages` stages.
    Each stage applies the separator to all active bags.

    With Seiferas preview parameters (A=10, nu=0.65, lam=eps=1/99):
    `numStages = ceil(log(2A)/log(1/nu)) * log2(n)` ≈ 7 * log2(n).

    This is a computable `def`, not an existential. -/
def separatorSortingNetwork (n : ℕ) {gam eps : ℝ} {d_sep : ℕ}
    (sep : SeparatorFamily gam eps d_sep) (numStages : ℕ) :
    ComparatorNetwork n where
  comparators := (List.range numStages).flatMap fun t ↦
    (separatorStage n sep t).comparators

/-- Total depth is at most numStages times the separator depth.
    Follows from `separatorStage_depth_le` applied to each stage. -/
theorem separatorSortingNetwork_depth_le (n : ℕ) {gam eps : ℝ} {d_sep : ℕ}
    (sep : SeparatorFamily gam eps d_sep) (numStages : ℕ) :
    (separatorSortingNetwork n sep numStages).depth ≤ numStages * d_sep := by
  sorry

/-! **Convergence and Correctness** -/

/-- After enough stages, all bags have at most 1 item (capacity < 1/lam < 1).
    The number of stages needed is O(log n):
    `T = ceil(log(n * A^maxLevel * lam) / log(1/nu))`.
    Since `maxLevel = O(log n)` and A is constant, T = O(log n). -/
theorem separatorSortingNetwork_converges {n : ℕ} {A nu lam eps : ℝ}
    {gam : ℝ} {d_sep : ℕ} {sep : SeparatorFamily gam eps d_sep}
    {t : ℕ} {perm : Fin n → Fin n} {bags : BagAssignment n}
    (hparams : SatisfiesConstraints A nu lam eps)
    (inv : SeifInvariant n A nu lam eps t perm bags)
    (hconv : converged n A nu lam t) :
    ∀ level idx, (bags level idx).card ≤ 1 := by
  sorry

/-- The sorting network is correct: for Boolean inputs, the output is monotone.
    Proof sketch:
    1. Start with any permutation (via 0-1 principle)
    2. Initial invariant holds at t=0
    3. Each stage maintains the invariant
    4. After O(log n) stages, all bags have ≤ 1 item
    5. Zero strangers at convergence → items are sorted -/
theorem separatorSortingNetwork_sorts {n : ℕ} {gam eps : ℝ} {d_sep : ℕ}
    (sep : SeparatorFamily gam eps d_sep) (numStages : ℕ)
    (hstages : True)  -- placeholder for numStages ≥ O(log n)
    (v : Fin n → Bool) :
    Monotone ((separatorSortingNetwork n sep numStages).exec v) := by
  sorry

/-! **Depth Bound: O(log n)** -/

/-- The separator sorting network has depth O(log n).
    With separator depth `d_sep` and convergence in `C * Nat.log 2 n` stages:
    total depth ≤ `C * d_sep * Nat.log 2 n`. -/
theorem separatorSortingNetwork_depth_bound {n : ℕ} {gam eps : ℝ} {d_sep : ℕ}
    (sep : SeparatorFamily gam eps d_sep) (C : ℕ) :
    (separatorSortingNetwork n sep (C * Nat.log 2 n)).depth ≤
    C * d_sep * Nat.log 2 n := by
  calc (separatorSortingNetwork n sep (C * Nat.log 2 n)).depth
      ≤ (C * Nat.log 2 n) * d_sep :=
        separatorSortingNetwork_depth_le n sep (C * Nat.log 2 n)
    _ = C * d_sep * Nat.log 2 n := by ring
