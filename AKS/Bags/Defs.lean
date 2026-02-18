/-
  # Bag Definitions for Separator-Based Sorting

  Defines the binary bag tree structure and j-stranger counting for the
  Seiferas (2009) separator-based sorting network proof (Sections 2–5).

  Key definitions:
  - `bagSize`, `nativeBagIdx`: bag structure in the binary tree
  - `isJStranger`: whether an item diverges from its native path
  - `jStrangerCount`: count of j-strangers among items in a bag

  All definitions validated by Rust simulation (`rust/test-bags.rs`):
  - Invariant holds with adversarial separator for n = 8..16384
  - j-stranger monotonicity confirmed: (j+1)-strange → j-strange
  - Parity convention: (t + level) % 2 ≠ 0 → empty
-/

import AKS.Sort.Defs

open Finset

/-! **Bag Tree Structure** -/

/-- Size of each bag's native interval at a given level: `n / 2^level`.
    At level 0 (root): `bagSize n 0 = n`. At level `k`: each bag covers
    `n / 2^k` items. -/
def bagSize (n level : ℕ) : ℕ := n / 2 ^ level

/-- The bag index that an item with sorted rank `r` is native to at a given
    level. `nativeBagIdx n level r = r / (n / 2^level)`. -/
def nativeBagIdx (n level : ℕ) (r : ℕ) : ℕ := r / bagSize n level

/-! **j-Strangers (Seiferas Section 3)** -/

/-- An item with sorted rank `r` is `j`-strange at bag `(level, idx)` if its
    native path diverges from the bag's ancestry at level `level - j`.

    Guards (validated by Rust simulation):
    - `j ≥ 1`: 0-strange is vacuously false
    - `j ≤ level`: can't diverge above root

    Key properties:
    - `(j+1)`-strange → `j`-strange (divergence propagates: `a/2 ≠ b/2 → a ≠ b`)
    - Native items (rank in bag's interval) are not `j`-strange for any `j` -/
@[reducible] def isJStranger (n rank level idx j : ℕ) : Prop :=
  1 ≤ j ∧ j ≤ level ∧ nativeBagIdx n (level - j) rank ≠ idx / 2 ^ j

/-- Count of `j`-strangers among items in a bag.
    `perm` maps register positions to sorted ranks.
    `regs` is the set of register positions assigned to this bag. -/
def jStrangerCount (n : ℕ) (perm : Fin n → Fin n)
    (regs : Finset (Fin n)) (level idx j : ℕ) : ℕ :=
  (regs.filter (fun i ↦ isJStranger n (perm i).val level idx j)).card

/-! **Basic Lemmas** -/

@[simp] theorem bagSize_zero (n : ℕ) : bagSize n 0 = n := by
  simp [bagSize]

theorem bagSize_pos {n level : ℕ} (hn : 2 ^ level ≤ n) : 0 < bagSize n level := by
  exact Nat.div_pos hn (pow_pos (by omega) level)

@[simp] theorem nativeBagIdx_root {n r : ℕ} (hr : r < n) :
    nativeBagIdx n 0 r = 0 := by
  simp only [nativeBagIdx, bagSize_zero]
  exact Nat.div_eq_of_lt hr

theorem not_isJStranger_zero (n rank level idx : ℕ) :
    ¬isJStranger n rank level idx 0 := by
  simp [isJStranger]

theorem not_isJStranger_gt_level {n rank level idx j : ℕ} (h : level < j) :
    ¬isJStranger n rank level idx j := by
  simp only [isJStranger, not_and, not_not]
  omega

/-- `(j+1)`-strange → `j`-strange: divergence at a higher ancestor level implies
    divergence at a lower ancestor level. Uses `a/2 ≠ b/2 → a ≠ b`.
    Requires `n` is a power of 2 so that
    `nativeBagIdx n (ℓ-1) r = (nativeBagIdx n ℓ r) / 2`. -/
theorem isJStranger_antitone {n rank level idx j : ℕ}
    (hn : ∃ k, n = 2 ^ k) (hj : 1 ≤ j) (hjl : j + 1 ≤ level)
    (h : isJStranger n rank level idx (j + 1)) :
    isJStranger n rank level idx j := by
  sorry

/-- At the root level, all items are native (since `j ≤ 0` forces `j = 0`). -/
theorem not_isJStranger_at_root (n rank idx j : ℕ) :
    ¬isJStranger n rank 0 idx j := by
  simp only [isJStranger, not_and, not_not]
  omega

theorem jStrangerCount_empty (n : ℕ) (perm : Fin n → Fin n)
    (level idx j : ℕ) : jStrangerCount n perm ∅ level idx j = 0 := by
  simp [jStrangerCount]

/-- Stranger count is monotone in the register set. -/
theorem jStrangerCount_mono {n : ℕ} {perm : Fin n → Fin n}
    {s t : Finset (Fin n)} (hst : s ⊆ t) (level idx j : ℕ) :
    jStrangerCount n perm s level idx j ≤ jStrangerCount n perm t level idx j := by
  simp only [jStrangerCount]
  exact Finset.card_le_card (Finset.filter_subset_filter _ hst)

/-- The number of `j`-strangers is at most the number of items in the bag. -/
theorem jStrangerCount_le_card {n : ℕ} (perm : Fin n → Fin n)
    (regs : Finset (Fin n)) (level idx j : ℕ) :
    jStrangerCount n perm regs level idx j ≤ regs.card := by
  simp only [jStrangerCount]
  exact Finset.card_filter_le _ _

/-- No items are `j`-strange for `j = 0`. -/
theorem jStrangerCount_zero_j {n : ℕ} (perm : Fin n → Fin n)
    (regs : Finset (Fin n)) (level idx : ℕ) :
    jStrangerCount n perm regs level idx 0 = 0 := by
  simp only [jStrangerCount, isJStranger, show ¬(1 ≤ 0) by omega, false_and, filter_false,
    card_empty]

/-- No items are `j`-strange for `j > level`. -/
theorem jStrangerCount_zero_gt_level {n : ℕ} (perm : Fin n → Fin n)
    (regs : Finset (Fin n)) {level idx j : ℕ} (h : level < j) :
    jStrangerCount n perm regs level idx j = 0 := by
  simp only [jStrangerCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun _ _ ↦ not_isJStranger_gt_level h
