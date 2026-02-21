/-
  # Seiferas's Invariant

  Defines the invariant maintained by the bag-tree sorting network
  (Seiferas 2009, Sections 4–5) and states the maintenance theorems.

  The invariant has eight clauses:
  1. Alternating levels empty: `(t + level) % 2 ≠ 0 → empty`
  2. Uniform size: all bags at an active level have equal size
  3. Capacity: items ≤ n · ν^t · A^level
  4. Strangers: j-strangers ≤ lam * eps^(j-1) * capacity
  5. Partition: distinct (level, idx) pairs have disjoint register sets
  6. Bounded depth: bags beyond maxLevel are empty
  7. Index bound: bags at out-of-range indices are empty
  8. Even size at small cap: when cap(l) < A, bags at level l+1 have even card

  All definitions validated by Rust simulation (`rust/test-bags.rs`):
  - Invariant holds with adversarial separator for n = 8..16384
  - All clauses maintained across O(log n) stages
-/

import AKS.Bags.Defs
import AKS.Separator.Defs

open Finset

/-! **Bag Assignment** -/

/-- A bag assignment maps each (level, idx) pair to a set of register positions.
    `bagItems level idx` is the set of `Fin n` registers currently in bag `(level, idx)`. -/
abbrev BagAssignment (n : ℕ) := ℕ → ℕ → Finset (Fin n)

/-- Maximum tree level: leaves are at level `Nat.log 2 n - 1`.
    For `n = 2^k`, this gives `k - 1`. -/
def maxLevel (n : ℕ) : ℕ := Nat.log 2 n - 1

/-- Capacity of a bag at `(level, idx)` at stage `t`:
    `cap = n · ν^t · A^level`. -/
def bagCapacity (n : ℕ) (A ν : ℝ) (t level : ℕ) : ℝ :=
  ↑n * ν ^ t * A ^ level

/-! **Rebagging: How Items Move Between Bags** -/

/-- Result of applying a separator to one bag's items.
    Items are partitioned into three groups:
    - `toParent`: fringe items kicked up to parent bag
    - `toLeftChild`: middle items sent to left child bag (2*idx)
    - `toRightChild`: middle items sent to right child bag (2*idx+1) -/
structure SplitResult (n : ℕ) where
  toParent : Finset (Fin n)
  toLeftChild : Finset (Fin n)
  toRightChild : Finset (Fin n)

/-- Items received from parent during rebagging. At level 0, no parent exists.
    At level ≥ 1, the parent at `(level-1, idx/2)` sends items to its left (even idx)
    or right (odd idx) child. -/
def fromParent {n : ℕ} (split : ℕ → ℕ → SplitResult n) (level idx : ℕ) : Finset (Fin n) :=
  if level = 0 then ∅
  else if idx % 2 = 0
    then (split (level - 1) (idx / 2)).toLeftChild
    else (split (level - 1) (idx / 2)).toRightChild

/-- Reconstruct bag contents after rebagging. Each bag receives:
    - Fringe items kicked up from its two children
    - Middle items sent down from its parent -/
def rebag {n : ℕ} (split : ℕ → ℕ → SplitResult n) : BagAssignment n :=
  fun level idx ↦
    (split (level + 1) (2 * idx)).toParent ∪
    (split (level + 1) (2 * idx + 1)).toParent ∪
    fromParent split level idx

/-- Union bound on rebag cardinality. -/
theorem rebag_card_le {n : ℕ} (split : ℕ → ℕ → SplitResult n) (level idx : ℕ) :
    (rebag split level idx).card ≤
      (split (level + 1) (2 * idx)).toParent.card +
      (split (level + 1) (2 * idx + 1)).toParent.card +
      (fromParent split level idx).card := by
  unfold rebag
  linarith [card_union_le
      ((split (level + 1) (2 * idx)).toParent ∪ (split (level + 1) (2 * idx + 1)).toParent)
      (fromParent split level idx),
    card_union_le (split (level + 1) (2 * idx)).toParent
      (split (level + 1) (2 * idx + 1)).toParent]

/-! **Four-Clause Invariant (Seiferas Section 4)** -/

/-- Seiferas's four-clause invariant for the bag-tree sorting network.

    Parameters:
    - `A > 1`: capacity growth per tree level
    - `ν ∈ (0, 1)`: capacity decay per stage
    - `lam` in (0, 1/2): separator fringe fraction
    - `ε > 0`: separator error rate

    **Parity convention (validated by Rust simulation):**
    `(t + level) % 2 ≠ 0 → empty`.
    At t=0, root (level 0) is nonempty: (0+0)%2 = 0. ✓
    Odd levels at t=0 are empty: (0+1)%2 = 1 ≠ 0. ✓ -/
structure SeifInvariant (n : ℕ) (A ν lam ε : ℝ) (t : ℕ)
    (perm : Fin n → Fin n) (bags : BagAssignment n) : Prop where
  /-- (1) Alternating levels empty: levels where `(t + level)` is odd are empty. -/
  alternating_empty : ∀ level idx,
    (t + level) % 2 ≠ 0 → bags level idx = ∅
  /-- (2) Uniform: all bags at a given active level have equal size. -/
  uniform_size : ∀ level idx₁ idx₂,
    idx₁ < 2 ^ level → idx₂ < 2 ^ level →
    (bags level idx₁).card = (bags level idx₂).card
  /-- (3) Capacity: items in bag ≤ `n · ν^t · A^level`. -/
  capacity_bound : ∀ level idx,
    ((bags level idx).card : ℝ) ≤ bagCapacity n A ν t level
  /-- (4) Strangers: j-strangers ≤ `lam * ε^(j-1) * capacity`, for all `j ≥ 1`. -/
  stranger_bound : ∀ level idx j, 1 ≤ j →
    (jStrangerCount n perm (bags level idx) level idx j : ℝ) ≤
    lam * ε ^ (j - 1) * bagCapacity n A ν t level
  /-- (5) Partition: distinct (level, idx) pairs have disjoint register sets. -/
  bags_disjoint : ∀ l₁ l₂ i₁ i₂,
    (l₁, i₁) ≠ (l₂, i₂) → Disjoint (bags l₁ i₁) (bags l₂ i₂)
  /-- (6) Bounded depth: bags beyond maxLevel are empty. -/
  bounded_depth : ∀ level idx, maxLevel n < level → bags level idx = ∅
  /-- (7) Index bound: bags at out-of-range indices are empty. -/
  idx_bound : ∀ level idx, 2 ^ level ≤ idx → bags level idx = ∅
  /-- (8) Even size at small capacity: when cap(l) < A, bags at level l+1 have even card. -/
  small_cap_even : ∀ level idx,
    bagCapacity n A ν t level < A → Even (bags (level + 1) idx).card

/-! **Parameter Constraints (Seiferas Section 5)** -/

/-- Constraint (C3): capacity decay rate is large enough.
    `ν ≥ 4*lam*A + 5/(2*A)` ensures capacity is maintained. -/
def SatisfiesC3 (A ν lam : ℝ) : Prop :=
  ν ≥ 4 * lam * A + 5 / (2 * A)

/-- Constraint (C4, j > 1): stranger decay for higher-order strangers.
    `2·A·ε + 1/A ≤ ν` ensures j-stranger bounds are maintained for j ≥ 2. -/
def SatisfiesC4_gt1 (A ν ε : ℝ) : Prop :=
  2 * A * ε + 1 / A ≤ ν

/-- Constraint (C4, j = 1): the master constraint for 1-strangers.
    Combines contributions from children (2-strangers kicked up),
    parent (1-strangers sent down), and sibling leakage. -/
def SatisfiesC4_eq1 (A ν lam ε : ℝ) : Prop :=
  2 * lam * ε * A + ε * lam / A + ε / (2 * A)
  + 2 * lam * ε * A / (1 - (2 * ε * A) ^ 2)
  + 1 / (8 * A ^ 3 - 2 * A)
  ≤ lam * ν

/-- Combined coefficient for parent 1-stranger sources (Seiferas Section 5).
    Captures four sub-sources from the parent bag:
    (a) ε fraction of parent's 1-strangers escape filtering: `ε·λ/A`
    (b) Halving errors (C-native on wrong side): `ε/(2A)`
    (c) Excess C-native from subtree stranger accumulation: `2λεA/(1-(2εA)²)`
    (d) C-native items from above parent: `1/(8A³-2A)` -/
noncomputable def parentStrangerCoeff (A lam ε : ℝ) : ℝ :=
  ε * lam / A + ε / (2 * A) +
  2 * lam * ε * A / (1 - (2 * ε * A) ^ 2) +
  1 / (8 * A ^ 3 - 2 * A)

/-- Coefficient for sibling-native items bound (measured at parent level).
    Three sub-sources: halving errors `ε/2`, subtree stranger accumulation
    `2λεA²/(1-(2εA)²)`, and above-parent items `1/(8A²-2)`. -/
noncomputable def cnativeCoeff (A lam ε : ℝ) : ℝ :=
  ε / 2 + 2 * lam * ε * A ^ 2 / (1 - (2 * ε * A) ^ 2) + 1 / (8 * A ^ 2 - 2)

/-- `cnativeCoeff` is nonneg when `A > 1`, `0 < lam`, `0 ≤ ε`, and `(2εA)² < 1`. -/
theorem cnativeCoeff_nonneg {A lam ε : ℝ}
    (hA : 1 < A) (hlam : 0 ≤ lam) (hε : 0 ≤ ε) (h2εA : (2 * ε * A) ^ 2 < 1) :
    0 ≤ cnativeCoeff A lam ε := by
  unfold cnativeCoeff
  have hA_pos : (0 : ℝ) < A := by linarith
  have hden1 : (0 : ℝ) < 1 - (2 * ε * A) ^ 2 := by linarith
  have hden2 : (0 : ℝ) < 8 * A ^ 2 - 2 := by nlinarith [sq_nonneg A]
  apply add_nonneg (add_nonneg _ _) _
  · exact div_nonneg (by linarith) (by linarith)
  · exact div_nonneg (by positivity) (by linarith)
  · exact div_nonneg (by linarith) (by linarith)

/-- `parentStrangerCoeff × A = lam*ε + cnativeCoeff`: the parent coefficient at child level
    decomposes into the 2-stranger contribution plus sibling-native contribution. -/
theorem parentStrangerCoeff_mul_A {A lam ε : ℝ} (hA : A ≠ 0) :
    parentStrangerCoeff A lam ε * A = lam * ε + cnativeCoeff A lam ε := by
  unfold parentStrangerCoeff cnativeCoeff
  have hA2 : A ^ 2 ≠ 0 := pow_ne_zero 2 hA
  have h8 : 8 * A ^ 3 - 2 * A = (8 * A ^ 2 - 2) * A := by ring
  rw [h8]
  field_simp
  ring

/-- The C4 (j=1) constraint decomposes as children + parent coefficient ≤ λν. -/
theorem c4_eq1_decomposed {A ν lam ε : ℝ} (hC4 : SatisfiesC4_eq1 A ν lam ε) :
    2 * lam * ε * A + parentStrangerCoeff A lam ε ≤ lam * ν := by
  unfold SatisfiesC4_eq1 at hC4; unfold parentStrangerCoeff; linarith

/-- All parameter constraints combined. -/
def SatisfiesConstraints (A ν lam ε : ℝ) : Prop :=
  1 < A ∧ 0 < ν ∧ ν < 1 ∧ 0 < lam ∧ lam < 1/2 ∧ 0 < ε ∧
  SatisfiesC3 A ν lam ∧
  SatisfiesC4_gt1 A ν ε ∧
  SatisfiesC4_eq1 A ν lam ε

/-! **Initial Invariant (t = 0)** -/

/-- The initial bag assignment: all items in the root bag (level 0, idx 0). -/
def initialBags (n : ℕ) : BagAssignment n :=
  fun level idx ↦ if level = 0 ∧ idx = 0 then Finset.univ else ∅

/-- The initial invariant holds at t = 0 when A ≥ 1 and ν ≥ 1.
    (In practice, ν < 1 but the capacity n · ν^0 · A^0 = n ≥ n.) -/
theorem initialInvariant (n : ℕ) (A ν lam ε : ℝ)
    (hA : 1 ≤ A) (hν : 0 < ν) (hlam : 0 < lam) (hε : 0 ≤ ε)
    (perm : Fin n → Fin n) :
    SeifInvariant n A ν lam ε 0 perm (initialBags n) := by
  constructor
  · -- Clause 1: alternating empty
    intro level idx hparity
    simp only [initialBags]
    split_ifs with h
    · obtain ⟨rfl, _⟩ := h; simp at hparity
    · rfl
  · -- Clause 2: uniform size
    intro level idx₁ idx₂ h₁ h₂
    simp only [initialBags]
    -- At level 0 with idx < 1: idx = 0, so both branches are pos
    -- At level > 0: both branches are neg (level ≠ 0)
    by_cases hlev : level = 0
    · subst hlev; simp at h₁ h₂; subst h₁; subst h₂; simp
    · have : ¬(level = 0 ∧ idx₁ = 0) := fun ⟨h, _⟩ ↦ hlev h
      have : ¬(level = 0 ∧ idx₂ = 0) := fun ⟨h, _⟩ ↦ hlev h
      simp [*]
  · -- Clause 3: capacity
    intro level idx
    simp only [initialBags, bagCapacity]
    split_ifs with h
    · obtain ⟨rfl, _⟩ := h; simp
    · simp; positivity
  · -- Clause 4: strangers
    intro level idx j hj
    simp only [initialBags]
    split_ifs with h
    · obtain ⟨rfl, _⟩ := h
      -- At root (level 0), no items are j-strange
      rw [jStrangerCount_zero_gt_level]
      · simp only [Nat.cast_zero]
        exact mul_nonneg (mul_nonneg (le_of_lt hlam) (pow_nonneg hε _))
          (by unfold bagCapacity; positivity)
      · omega
    · rw [jStrangerCount_empty]
      simp only [Nat.cast_zero]
      exact mul_nonneg (mul_nonneg (le_of_lt hlam) (pow_nonneg hε _))
        (by unfold bagCapacity; positivity)
  · -- Clause 5: partition (disjoint bags)
    intro l₁ l₂ i₁ i₂ hne
    simp only [initialBags]
    split_ifs with h₁ h₂
    · obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂; exact absurd rfl hne
    all_goals simp
  · -- Clause 6: bounded depth
    intro level idx hlev
    simp only [initialBags]
    split_ifs with h
    · obtain ⟨rfl, _⟩ := h; omega
    · rfl
  · -- Clause 7: idx bound
    intro level idx hidx
    simp only [initialBags]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; simp at hidx
    · rfl
  · -- Clause 8: small_cap_even (vacuously true at t=0: all bags at level ≥ 1 are empty)
    intro level idx hcap
    simp only [initialBags]
    have : ¬(level + 1 = 0 ∧ idx = 0) := by omega
    rw [if_neg this]; exact ⟨0, by simp⟩

/-! **Invariant Maintenance Theorems (Seiferas Section 5)** -/

/-- Capacity decay: `bagCapacity` at stage `t+1` equals `ν` times capacity at stage `t`. -/
theorem bagCapacity_succ_stage (n : ℕ) (A ν : ℝ) (t level : ℕ) :
    bagCapacity n A ν (t + 1) level = ν * bagCapacity n A ν t level := by
  simp only [bagCapacity, pow_succ]; ring

/-- Child capacity: `bagCapacity` at level `l+1` equals `A` times capacity at level `l`. -/
theorem bagCapacity_child (n : ℕ) (A ν : ℝ) (t level : ℕ) :
    bagCapacity n A ν t (level + 1) = A * bagCapacity n A ν t level := by
  simp only [bagCapacity, pow_succ]; ring

/-- Core arithmetic for the capacity proof: if `b ≥ A > 1` and `ν ≥ 4λA + 5/(2A)`,
    then `4λAb + 2 + b/(2A) ≤ νb`. -/
private theorem capacity_arithmetic {A ν lam b : ℝ}
    (hA : 1 < A) (hb_ge : A ≤ b)
    (hC3 : ν ≥ 4 * lam * A + 5 / (2 * A)) :
    4 * lam * A * b + 2 + b / (2 * A) ≤ ν * b := by
  have hA_pos : (0 : ℝ) < A := by linarith
  have hb_pos : (0 : ℝ) < b := by linarith
  have h2A_pos : (0 : ℝ) < 2 * A := by linarith
  -- Step 1: ν * b ≥ 4*lam*A*b + 5*b/(2*A)
  have h1 : ν * b ≥ 4 * lam * A * b + 5 * b / (2 * A) := by
    have h1a := mul_le_mul_of_nonneg_right hC3 (le_of_lt hb_pos)
    have h1b : (4 * lam * A + 5 / (2 * A)) * b = 4 * lam * A * b + 5 * b / (2 * A) := by
      field_simp
    linarith
  -- Step 2: 5*b/(2*A) ≥ 2 + b/(2*A)
  -- Equivalent to: (4*b - 4*A) / (2*A) ≥ 0
  have h2 : 5 * b / (2 * A) ≥ 2 + b / (2 * A) := by
    rw [ge_iff_le, ← sub_nonneg]
    have : 5 * b / (2 * A) - (2 + b / (2 * A)) = (4 * b - 4 * A) / (2 * A) := by
      field_simp; ring
    rw [this]
    exact div_nonneg (by linarith) (by linarith)
  linarith

/-- Case 2 arithmetic: if `ν ≥ 4λA + 5/(2A)`, then `4λAb ≤ νb`. -/
private theorem capacity_arithmetic_small {A ν lam b : ℝ}
    (hA : 0 < A) (hb : 0 ≤ b) (_ : 0 ≤ lam)
    (hC3 : ν ≥ 4 * lam * A + 5 / (2 * A)) :
    4 * lam * A * b ≤ ν * b := by
  have : 4 * lam * A ≤ ν := by
    have : 0 ≤ 5 / (2 * A) := div_nonneg (by positivity) (by positivity)
    linarith
  exact mul_le_mul_of_nonneg_right this hb

/-- Clause (3) maintenance: capacity bound at stage `t+1`.
    Requires constraint (C3): `ν ≥ 4*lam*A + 5/(2*A)`.
    Two-case proof (Seiferas Section 5):
    - Case 1 (`b ≥ A`): `4λAb + 2 + b/(2A) ≤ νb` — the +2 from children kicks
      and `b/(2A)` from parent are absorbed by the slack in C3.
    - Case 2 (`b < A`): parent capacity `b/A < 1` so parent is empty (no items
      from above). Children have even item counts (divisibility argument), so
      no odd-item kicking. Total kick from children ≤ `4λAb` ≤ `νb`. -/
theorem capacity_maintained {n : ℕ} {A ν lam : ℝ} {t : ℕ}
    (split : ℕ → ℕ → SplitResult n)
    (hC3 : SatisfiesC3 A ν lam)
    (hA : 1 < A) (hν : 0 < ν) (hlam : 0 ≤ lam)
    (hkick : ∀ l i, ((split l i).toParent.card : ℝ) ≤
      2 * lam * bagCapacity n A ν t l + 1)
    (hsend_left : ∀ l i, ((split l i).toLeftChild.card : ℝ) ≤
      bagCapacity n A ν t l / 2)
    (hsend_right : ∀ l i, ((split l i).toRightChild.card : ℝ) ≤
      bagCapacity n A ν t l / 2)
    -- When cap(l) < A, the paired kick from both children has no +2 (even items)
    (hkick_pair : ∀ l i, bagCapacity n A ν t l < A →
      ((split (l + 1) (2 * i)).toParent.card +
       (split (l + 1) (2 * i + 1)).toParent.card : ℝ) ≤
      4 * lam * bagCapacity n A ν t (l + 1))
    -- When cap(l) < A, the parent is empty so fromParent = ∅
    (hfrom_parent_empty : ∀ l i, bagCapacity n A ν t l < A →
      fromParent split l i = ∅) :
    ∀ level idx,
    ((rebag split level idx).card : ℝ) ≤ bagCapacity n A ν (t + 1) level := by
  intro level idx
  have hA_pos : (0 : ℝ) < A := by linarith
  rw [bagCapacity_succ_stage]
  by_cases hb_ge : A ≤ bagCapacity n A ν t level
  · -- Case 1: cap ≥ A (standard argument with +2)
    have hb_pos : (0 : ℝ) < bagCapacity n A ν t level := by linarith
    have hcard := rebag_card_le split level idx
    have ha := hkick (level + 1) (2 * idx)
    have hb' := hkick (level + 1) (2 * idx + 1)
    rw [bagCapacity_child] at ha hb'
    have hparent : ((fromParent split level idx).card : ℝ) ≤
        bagCapacity n A ν t level / (2 * A) := by
      unfold fromParent
      split_ifs with h₁ h₂
      · simp only [card_empty, Nat.cast_zero]
        exact div_nonneg (le_of_lt hb_pos) (by linarith)
      · calc ((split (level - 1) (idx / 2)).toLeftChild.card : ℝ)
            ≤ bagCapacity n A ν t (level - 1) / 2 := hsend_left _ _
          _ = bagCapacity n A ν t level / (2 * A) := by
              simp only [bagCapacity]
              have hpow : A ^ level = A ^ (level - 1) * A := by
                conv_lhs => rw [show level = level - 1 + 1 from by omega]
                exact pow_succ A (level - 1)
              rw [hpow]; field_simp
      · calc ((split (level - 1) (idx / 2)).toRightChild.card : ℝ)
            ≤ bagCapacity n A ν t (level - 1) / 2 := hsend_right _ _
          _ = bagCapacity n A ν t level / (2 * A) := by
              simp only [bagCapacity]
              have hpow : A ^ level = A ^ (level - 1) * A := by
                conv_lhs => rw [show level = level - 1 + 1 from by omega]
                exact pow_succ A (level - 1)
              rw [hpow]; field_simp
    calc ((rebag split level idx).card : ℝ)
        ≤ ↑(split (level + 1) (2 * idx)).toParent.card +
          ↑(split (level + 1) (2 * idx + 1)).toParent.card +
          ↑(fromParent split level idx).card := by exact_mod_cast hcard
      _ ≤ (2 * lam * (A * bagCapacity n A ν t level) + 1) +
          (2 * lam * (A * bagCapacity n A ν t level) + 1) +
          bagCapacity n A ν t level / (2 * A) := by linarith
      _ = 4 * lam * A * bagCapacity n A ν t level + 2 +
          bagCapacity n A ν t level / (2 * A) := by ring
      _ ≤ ν * bagCapacity n A ν t level := capacity_arithmetic hA hb_ge hC3
  · -- Case 2: cap < A (Seiferas Section 5: no +2, no parent contribution)
    push_neg at hb_ge
    have hfp := hfrom_parent_empty level idx hb_ge
    have hpair := hkick_pair level idx hb_ge
    rw [bagCapacity_child] at hpair
    have hcard := rebag_card_le split level idx
    rw [hfp] at hcard; simp only [card_empty] at hcard
    have hkick_sum : ((split (level + 1) (2 * idx)).toParent.card : ℝ) +
        ((split (level + 1) (2 * idx + 1)).toParent.card : ℝ) ≤
        4 * lam * (A * bagCapacity n A ν t level) := by
      exact_mod_cast hpair
    calc ((rebag split level idx).card : ℝ)
        ≤ ↑(split (level + 1) (2 * idx)).toParent.card +
          ↑(split (level + 1) (2 * idx + 1)).toParent.card +
          0 := by exact_mod_cast (by omega : (rebag split level idx).card ≤
            (split (level + 1) (2 * idx)).toParent.card +
            (split (level + 1) (2 * idx + 1)).toParent.card + 0)
      _ ≤ 4 * lam * (A * bagCapacity n A ν t level) + 0 := by linarith
      _ = 4 * lam * A * bagCapacity n A ν t level := by ring
      _ ≤ ν * bagCapacity n A ν t level :=
          capacity_arithmetic_small hA_pos (by unfold bagCapacity; positivity) hlam hC3

/-- Union bound on stranger count of a rebag: sum of three source contributions. -/
theorem rebag_strangerCount_le {n : ℕ} (perm : Fin n → Fin n)
    (split : ℕ → ℕ → SplitResult n) (level idx j : ℕ) :
    jStrangerCount n perm (rebag split level idx) level idx j ≤
    jStrangerCount n perm ((split (level + 1) (2 * idx)).toParent) level idx j +
    jStrangerCount n perm ((split (level + 1) (2 * idx + 1)).toParent) level idx j +
    jStrangerCount n perm (fromParent split level idx) level idx j := by
  unfold rebag
  linarith [jStrangerCount_union_le perm
      ((split (level+1) (2*idx)).toParent ∪ (split (level+1) (2*idx+1)).toParent)
      (fromParent split level idx) level idx j,
    jStrangerCount_union_le perm
      ((split (level+1) (2*idx)).toParent)
      ((split (level+1) (2*idx+1)).toParent) level idx j]

/-- Parent capacity: `bagCapacity` at level `l-1` equals capacity at `l` divided by `A`,
    for `l ≥ 1`. -/
theorem bagCapacity_parent {n : ℕ} {A ν : ℝ} {t level : ℕ} (hA : 0 < A)
    (hlev : 1 ≤ level) :
    bagCapacity n A ν t (level - 1) = bagCapacity n A ν t level / A := by
  simp only [bagCapacity]
  have hpow : A ^ level = A ^ (level - 1) * A := by
    conv_lhs => rw [show level = (level - 1) + 1 from by omega]
    exact pow_succ A (level - 1)
  rw [hpow]; field_simp

/-- Core arithmetic for stranger bound (j ≥ 2): factoring out `lam·ε^(j-1)` and
    applying C4 (`2Aε + 1/A ≤ ν`). -/
private theorem stranger_gt1_arithmetic {A ν lam ε b : ℝ} {j : ℕ}
    (hC4 : SatisfiesC4_gt1 A ν ε)
    (hA : 0 < A) (hlam : 0 ≤ lam) (hε : 0 ≤ ε) (hb : 0 ≤ b)
    (hj : 2 ≤ j) :
    2 * lam * ε ^ j * (A * b) + lam * ε ^ (j - 1) * (b / A) ≤
    lam * ε ^ (j - 1) * (ν * b) := by
  have hpow : ε ^ j = ε ^ (j - 1) * ε := by
    conv_lhs => rw [show j = (j - 1) + 1 from by omega]
    exact pow_succ ε (j - 1)
  rw [hpow]
  suffices h : 0 ≤ lam * ε ^ (j - 1) * b * (ν - (2 * A * ε + 1 / A)) by
    have hfact : lam * ε ^ (j - 1) * (ν * b) -
        (2 * lam * (ε ^ (j - 1) * ε) * (A * b) + lam * ε ^ (j - 1) * (b / A))
      = lam * ε ^ (j - 1) * b * (ν - (2 * A * ε + 1 / A)) := by field_simp
    linarith
  exact mul_nonneg (mul_nonneg (mul_nonneg hlam (pow_nonneg hε _)) hb)
    (by unfold SatisfiesC4_gt1 at hC4; linarith)

/-- Clause (4) maintenance for `j ≥ 2`: stranger bound at stage `t+1`.
    Sources: (j+1)-strangers from children kicked up + (j-1)-strangers from parent.
    Requires constraint (C4, j>1): `2·A·ε + 1/A ≤ ν`.

    Hypotheses on the split (Seiferas Section 5):
    - `hkick_stranger`: j-strangers among items kicked from each child, measured at
      the receiving level, bounded by `lam·ε^j·bagCapacity(child_level)`.
    - `hparent_stranger`: j-strangers among items from parent bounded by
      `lam·ε^(j-1)·bagCapacity(parent_level)` (includes ε filtering factor). -/
theorem stranger_bound_maintained_gt1 {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n}
    (split : ℕ → ℕ → SplitResult n)
    (hC4 : SatisfiesC4_gt1 A ν ε)
    (hA : 1 < A) (hν : 0 < ν) (hlam : 0 < lam) (hε : 0 ≤ ε)
    (hkick_stranger : ∀ l i j, 1 ≤ j →
      (jStrangerCount n perm (split l i).toParent (l - 1) (i / 2) j : ℝ) ≤
      lam * ε ^ j * bagCapacity n A ν t l)
    (hparent_stranger : ∀ level idx j, 2 ≤ j →
      (jStrangerCount n perm (fromParent split level idx) level idx j : ℝ) ≤
      lam * ε ^ (j - 1) * bagCapacity n A ν t (level - 1))
    (level idx j : ℕ) (hj : 2 ≤ j) :
    (jStrangerCount n perm (rebag split level idx) level idx j : ℝ) ≤
    lam * ε ^ (j - 1) * bagCapacity n A ν (t + 1) level := by
  have hA_pos : (0 : ℝ) < A := by linarith
  -- Bound each source
  have hleft : (jStrangerCount n perm ((split (level+1) (2*idx)).toParent)
      level idx j : ℝ) ≤ lam * ε ^ j * (A * bagCapacity n A ν t level) := by
    have := hkick_stranger (level + 1) (2 * idx) j (by omega)
    rwa [show (level + 1) - 1 = level from by omega,
         show 2 * idx / 2 = idx from by omega, bagCapacity_child] at this
  have hright : (jStrangerCount n perm ((split (level+1) (2*idx+1)).toParent)
      level idx j : ℝ) ≤ lam * ε ^ j * (A * bagCapacity n A ν t level) := by
    have := hkick_stranger (level + 1) (2 * idx + 1) j (by omega)
    rwa [show (level + 1) - 1 = level from by omega,
         show (2 * idx + 1) / 2 = idx from by omega, bagCapacity_child] at this
  have hpar : (jStrangerCount n perm (fromParent split level idx) level idx j : ℝ) ≤
      lam * ε ^ (j - 1) * (bagCapacity n A ν t level / A) := by
    by_cases hlev : level = 0
    · subst hlev; simp only [fromParent, ite_true]
      rw [jStrangerCount_empty]; simp only [Nat.cast_zero]
      have hcap : (0 : ℝ) ≤ bagCapacity n A ν t 0 := by unfold bagCapacity; positivity
      exact mul_nonneg (mul_nonneg hlam.le (pow_nonneg hε _))
        (div_nonneg hcap (le_of_lt hA_pos))
    · rw [← bagCapacity_parent hA_pos (by omega)]
      exact hparent_stranger level idx j hj
  -- Assemble via union bound + arithmetic
  calc (jStrangerCount n perm (rebag split level idx) level idx j : ℝ)
      ≤ ↑(jStrangerCount n perm ((split (level+1) (2*idx)).toParent) level idx j) +
        ↑(jStrangerCount n perm ((split (level+1) (2*idx+1)).toParent) level idx j) +
        ↑(jStrangerCount n perm (fromParent split level idx) level idx j) := by
        exact_mod_cast rebag_strangerCount_le perm split level idx j
    _ ≤ lam * ε ^ j * (A * bagCapacity n A ν t level) +
        lam * ε ^ j * (A * bagCapacity n A ν t level) +
        lam * ε ^ (j - 1) * (bagCapacity n A ν t level / A) := by linarith
    _ = 2 * lam * ε ^ j * (A * bagCapacity n A ν t level) +
        lam * ε ^ (j - 1) * (bagCapacity n A ν t level / A) := by ring
    _ ≤ lam * ε ^ (j - 1) * (ν * bagCapacity n A ν t level) :=
        stranger_gt1_arithmetic hC4 hA_pos hlam.le hε
          (by unfold bagCapacity; positivity) hj
    _ = lam * ε ^ (j - 1) * bagCapacity n A ν (t + 1) level := by
        rw [bagCapacity_succ_stage]

/-- Core arithmetic for stranger bound (j = 1): factoring out `bagCapacity` and
    applying C4 (`2·lam·ε·A + parentStrangerCoeff ≤ lam·ν`). -/
private theorem stranger_eq1_arithmetic {A ν lam ε b : ℝ}
    (hC4 : SatisfiesC4_eq1 A ν lam ε) (hb : 0 ≤ b) :
    2 * lam * ε * A * b + parentStrangerCoeff A lam ε * b ≤
    lam * (ν * b) := by
  calc 2 * lam * ε * A * b + parentStrangerCoeff A lam ε * b
      = (2 * lam * ε * A + parentStrangerCoeff A lam ε) * b := by ring
    _ ≤ (lam * ν) * b :=
        mul_le_mul_of_nonneg_right (c4_eq1_decomposed hC4) hb
    _ = lam * (ν * b) := by ring

/-- Clause (4) maintenance for `j = 1`: 1-stranger bound at stage `t+1`.
    This is the hardest case (Seiferas Section 5). Three sources:
    (a) 2-strangers from children kicked up: at most `2·lam·ε·A·b`
    (b)–(e) Parent contributions (1-strangers, halving errors, subtree accumulation,
    above-parent items): combined at most `parentStrangerCoeff·b`
    Requires the master constraint (C4, j=1).

    The two hypotheses `hkick_stranger` and `hparent_1stranger` abstract
    over the separator's behavior:
    - `hkick_stranger`: 1-strangers among items kicked from each child
    - `hparent_1stranger`: 1-strangers among items from parent (all four sub-sources) -/
theorem stranger_bound_maintained_eq1 {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n}
    (split : ℕ → ℕ → SplitResult n)
    (hC4 : SatisfiesC4_eq1 A ν lam ε)
    (hA : 1 < A) (hν : 0 < ν) (hlam : 0 < lam) (_ : 0 ≤ ε)
    (hkick_stranger : ∀ l i,
      (jStrangerCount n perm (split l i).toParent (l - 1) (i / 2) 1 : ℝ) ≤
      lam * ε * bagCapacity n A ν t l)
    (hparent_1stranger : ∀ level idx,
      (jStrangerCount n perm (fromParent split level idx) level idx 1 : ℝ) ≤
      parentStrangerCoeff A lam ε * bagCapacity n A ν t level)
    (level idx : ℕ) :
    (jStrangerCount n perm (rebag split level idx) level idx 1 : ℝ) ≤
    lam * bagCapacity n A ν (t + 1) level := by
  -- Level 0: no 1-strangers (j = 1 > level = 0)
  by_cases hlev : level = 0
  · subst hlev
    rw [jStrangerCount_zero_gt_level perm _ (by omega : 0 < 1)]
    simp only [Nat.cast_zero]
    exact mul_nonneg hlam.le (by unfold bagCapacity; positivity)
  -- Level ≥ 1: union bound + arithmetic
  · have hA_pos : (0 : ℝ) < A := by linarith
    -- Bound left child kicked up
    have hleft : (jStrangerCount n perm ((split (level+1) (2*idx)).toParent)
        level idx 1 : ℝ) ≤ lam * ε * (A * bagCapacity n A ν t level) := by
      have := hkick_stranger (level + 1) (2 * idx)
      rwa [show (level + 1) - 1 = level from by omega,
           show 2 * idx / 2 = idx from by omega, bagCapacity_child] at this
    -- Bound right child kicked up
    have hright : (jStrangerCount n perm ((split (level+1) (2*idx+1)).toParent)
        level idx 1 : ℝ) ≤ lam * ε * (A * bagCapacity n A ν t level) := by
      have := hkick_stranger (level + 1) (2 * idx + 1)
      rwa [show (level + 1) - 1 = level from by omega,
           show (2 * idx + 1) / 2 = idx from by omega, bagCapacity_child] at this
    -- Bound parent contribution
    have hpar := hparent_1stranger level idx
    -- Assemble via union bound + arithmetic
    calc (jStrangerCount n perm (rebag split level idx) level idx 1 : ℝ)
        ≤ ↑(jStrangerCount n perm ((split (level+1) (2*idx)).toParent) level idx 1) +
          ↑(jStrangerCount n perm ((split (level+1) (2*idx+1)).toParent) level idx 1) +
          ↑(jStrangerCount n perm (fromParent split level idx) level idx 1) := by
          exact_mod_cast rebag_strangerCount_le perm split level idx 1
      _ ≤ lam * ε * (A * bagCapacity n A ν t level) +
          lam * ε * (A * bagCapacity n A ν t level) +
          parentStrangerCoeff A lam ε * bagCapacity n A ν t level := by linarith
      _ = 2 * lam * ε * A * bagCapacity n A ν t level +
          parentStrangerCoeff A lam ε * bagCapacity n A ν t level := by ring
      _ ≤ lam * (ν * bagCapacity n A ν t level) :=
          stranger_eq1_arithmetic hC4 (by unfold bagCapacity; positivity)
      _ = lam * bagCapacity n A ν (t + 1) level := by
          rw [bagCapacity_succ_stage]

/-- 1-strangers ≤ 2-strangers + sibling-native (unconditional filter partition bound). -/
private theorem jStrangerCount_one_le_two_plus_sibling {n : ℕ} (perm : Fin n → Fin n)
    (regs : Finset (Fin n)) (level idx : ℕ) :
    jStrangerCount n perm regs level idx 1 ≤
    jStrangerCount n perm regs level idx 2 + siblingNativeCount n perm regs level idx := by
  simp only [jStrangerCount, siblingNativeCount]
  -- filter(isJ 1) ⊆ filter(isJ 2) ∪ filter(isJ 1 ∧ ¬isJ 2)
  calc (regs.filter (fun i ↦ isJStranger n (perm i).val level idx 1)).card
      ≤ (regs.filter (fun i ↦ isJStranger n (perm i).val level idx 2) ∪
         regs.filter (fun i ↦ isJStranger n (perm i).val level idx 1 ∧
           ¬isJStranger n (perm i).val level idx 2)).card := by
        apply Finset.card_le_card
        intro x; simp only [Finset.mem_filter, Finset.mem_union]
        intro ⟨hm, h1⟩
        by_cases h2 : isJStranger n (perm x).val level idx 2
        · exact Or.inl ⟨hm, h2⟩
        · exact Or.inr ⟨hm, h1, h2⟩
    _ ≤ (regs.filter (fun i ↦ isJStranger n (perm i).val level idx 2)).card +
        (regs.filter (fun i ↦ isJStranger n (perm i).val level idx 1 ∧
          ¬isJStranger n (perm i).val level idx 2)).card :=
        Finset.card_union_le _ _

/-- Parent 1-stranger bound: among items sent from parent to child bag B,
    the 1-strangers are bounded by `parentStrangerCoeff × capacity`.
    Decomposes 1-strangers into 2-strangers + sibling-native items, then bounds
    each component separately using the provided hypotheses.
    The 2-stranger bound comes from the invariant's stranger bound at j=2.
    The sibling-native bound requires three sub-sources (Seiferas Section 5):
    (b) Halving errors: C-native items on wrong side of separator
    (c) Excess C-native from subtree stranger accumulation (geometric series)
    (d) C-native items from levels above parent -/
theorem parent_1stranger_bound {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n}
    (split : ℕ → ℕ → SplitResult n)
    (hA : 1 < A) (hν : 0 < ν) (hlam : 0 ≤ lam) (hε : 0 ≤ ε)
    (h2εA : (2 * ε * A) ^ 2 < 1)
    -- Bound on 2-strangers among items from parent
    (hparent_stranger_j2 : ∀ level idx,
      (jStrangerCount n perm (fromParent split level idx) level idx 2 : ℝ) ≤
      lam * ε * bagCapacity n A ν t (level - 1))
    -- Bound on sibling-native items from parent
    (hcnative_bound : ∀ level idx,
      (siblingNativeCount n perm (fromParent split level idx) level idx : ℝ) ≤
      cnativeCoeff A lam ε * bagCapacity n A ν t (level - 1))
    (level idx : ℕ) :
    (jStrangerCount n perm (fromParent split level idx) level idx 1 : ℝ) ≤
    parentStrangerCoeff A lam ε * bagCapacity n A ν t level := by
  have hA_pos : (0 : ℝ) < A := by linarith
  have hA_ne : A ≠ 0 := ne_of_gt hA_pos
  -- Level 0: fromParent = ∅
  by_cases hlev : level = 0
  · subst hlev; simp only [fromParent, ite_true]
    rw [jStrangerCount_empty]; simp only [Nat.cast_zero]
    apply mul_nonneg
    · unfold parentStrangerCoeff
      have hd : (0 : ℝ) < 8 * A ^ 3 - 2 * A := by nlinarith [sq_nonneg A, sq_abs A]
      have hden : (0 : ℝ) < 1 - (2 * ε * A) ^ 2 := by linarith
      apply add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
      · exact div_nonneg (by positivity) (by linarith)
      · exact div_nonneg (by positivity) (by linarith)
      · exact div_nonneg (by positivity) (by linarith)
      · exact div_nonneg (by linarith) (by linarith)
    · unfold bagCapacity; positivity
  -- Level ≥ 1: decompose and bound
  · have hlev1 : 1 ≤ level := by omega
    -- Use partition bound: 1-strangers ≤ 2-strangers + sibling-native
    have hdecomp := jStrangerCount_one_le_two_plus_sibling perm
      (fromParent split level idx) level idx
    -- Combine: ≤ (lam*ε + cnativeCoeff) * cap(parent) = parentStrangerCoeff * cap(level)
    calc (jStrangerCount n perm (fromParent split level idx) level idx 1 : ℝ)
        ≤ (jStrangerCount n perm (fromParent split level idx) level idx 2 : ℝ) +
          (siblingNativeCount n perm (fromParent split level idx) level idx : ℝ) := by
          exact_mod_cast hdecomp
      _ ≤ lam * ε * bagCapacity n A ν t (level - 1) +
          cnativeCoeff A lam ε * bagCapacity n A ν t (level - 1) := by
          linarith [hparent_stranger_j2 level idx, hcnative_bound level idx]
      _ = (lam * ε + cnativeCoeff A lam ε) * bagCapacity n A ν t (level - 1) := by ring
      _ = parentStrangerCoeff A lam ε * A * bagCapacity n A ν t (level - 1) := by
          rw [parentStrangerCoeff_mul_A hA_ne]
      _ = parentStrangerCoeff A lam ε * (A * bagCapacity n A ν t (level - 1)) := by ring
      _ = parentStrangerCoeff A lam ε * bagCapacity n A ν t level := by
          conv_rhs => rw [show level = (level - 1) + 1 from by omega]
          rw [bagCapacity_child]

private lemma split_empty_of_bags_empty {n : ℕ}
    {bags : BagAssignment n}
    {split : ℕ → ℕ → SplitResult n}
    (hsplit_sub : ∀ l i,
      (split l i).toParent ⊆ bags l i ∧
      (split l i).toLeftChild ⊆ bags l i ∧
      (split l i).toRightChild ⊆ bags l i)
    {l i : ℕ} (h : bags l i = ∅) :
    (split l i).toParent = ∅ ∧
    (split l i).toLeftChild = ∅ ∧
    (split l i).toRightChild = ∅ :=
  ⟨Finset.subset_empty.mp (h ▸ (hsplit_sub l i).1),
   Finset.subset_empty.mp (h ▸ (hsplit_sub l i).2.1),
   Finset.subset_empty.mp (h ▸ (hsplit_sub l i).2.2)⟩

private lemma fromParent_empty_of_parent_empty {n : ℕ}
    {bags : BagAssignment n}
    {split : ℕ → ℕ → SplitResult n}
    (hsplit_sub : ∀ l i,
      (split l i).toParent ⊆ bags l i ∧
      (split l i).toLeftChild ⊆ bags l i ∧
      (split l i).toRightChild ⊆ bags l i)
    {level idx : ℕ} (h : level = 0 ∨ bags (level - 1) (idx / 2) = ∅) :
    fromParent split level idx = ∅ := by
  unfold fromParent
  obtain rfl | h := h
  · simp
  · split_ifs with h₁ h₂
    · rfl
    · exact (split_empty_of_bags_empty hsplit_sub h).2.1
    · exact (split_empty_of_bags_empty hsplit_sub h).2.2

/-- Full invariant maintenance: given the invariant on `bags` at stage `t`,
    and hypotheses on the split (components ⊆ bags, cardinality bounds,
    stranger bounds, structural properties), the invariant holds at stage `t+1`
    on `rebag split`. Requires all parameter constraints. -/
theorem invariant_maintained {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n}
    {bags : BagAssignment n}
    (split : ℕ → ℕ → SplitResult n)
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hparams : SatisfiesConstraints A ν lam ε)
    -- Split components are subsets of bags
    (hsplit_sub : ∀ l i,
      (split l i).toParent ⊆ bags l i ∧
      (split l i).toLeftChild ⊆ bags l i ∧
      (split l i).toRightChild ⊆ bags l i)
    -- Leaf bags don't send to children
    (hsplit_leaf : ∀ l i, maxLevel n ≤ l →
      (split l i).toLeftChild = ∅ ∧ (split l i).toRightChild = ∅)
    -- Cardinality bounds on the split
    (hkick : ∀ l i, ((split l i).toParent.card : ℝ) ≤
      2 * lam * bagCapacity n A ν t l + 1)
    (hsend_left : ∀ l i, ((split l i).toLeftChild.card : ℝ) ≤
      bagCapacity n A ν t l / 2)
    (hsend_right : ∀ l i, ((split l i).toRightChild.card : ℝ) ≤
      bagCapacity n A ν t l / 2)
    -- When cap(l) < A, paired kick from both children has no +2 (even items)
    (hkick_pair : ∀ l i, bagCapacity n A ν t l < A →
      ((split (l + 1) (2 * i)).toParent.card +
       (split (l + 1) (2 * i + 1)).toParent.card : ℝ) ≤
      4 * lam * bagCapacity n A ν t (l + 1))
    -- Stranger bounds on kicked items (from separator error)
    (hkick_stranger : ∀ l i j, 1 ≤ j →
      (jStrangerCount n perm (split l i).toParent (l - 1) (i / 2) j : ℝ) ≤
      lam * ε ^ j * bagCapacity n A ν t l)
    -- Parent stranger bounds (j >= 2)
    (hparent_stranger : ∀ level idx j, 2 ≤ j →
      (jStrangerCount n perm (fromParent split level idx) level idx j : ℝ) ≤
      lam * ε ^ (j - 1) * bagCapacity n A ν t (level - 1))
    -- Parent 1-stranger bound
    (hparent_1stranger : ∀ level idx,
      (jStrangerCount n perm (fromParent split level idx) level idx 1 : ℝ) ≤
      parentStrangerCoeff A lam ε * bagCapacity n A ν t level)
    -- Structural properties of rebag
    (hrebag_uniform : ∀ level i₁ i₂,
      i₁ < 2 ^ level → i₂ < 2 ^ level →
      (rebag split level i₁).card = (rebag split level i₂).card)
    (hrebag_disjoint : ∀ l₁ l₂ i₁ i₂,
      (l₁, i₁) ≠ (l₂, i₂) → Disjoint (rebag split l₁ i₁) (rebag split l₂ i₂)) :
    SeifInvariant n A ν lam ε (t + 1) perm (rebag split) := by
  obtain ⟨hA, hν, _, hlam_pos, _, hε_pos, hC3, hC4_gt1, hC4_eq1⟩ := hparams
  have hA_pos : (0 : ℝ) < A := by linarith
  -- Derive: when cap(l) < A, the parent bag is empty so fromParent = ∅
  have hfrom_parent_empty : ∀ l i, bagCapacity n A ν t l < A →
      fromParent split l i = ∅ := by
    intro l i hcap_lt
    apply fromParent_empty_of_parent_empty hsplit_sub
    by_cases hl : l = 0
    · exact Or.inl hl
    · right
      have hcap_parent : bagCapacity n A ν t (l - 1) < 1 := by
        rw [bagCapacity_parent hA_pos (by omega)]
        rwa [div_lt_one hA_pos]
      have hcard := inv.capacity_bound (l - 1) (i / 2)
      have hcard_zero : (bags (l - 1) (i / 2)).card = 0 := by
        by_contra h
        have h1 : 1 ≤ (bags (l - 1) (i / 2)).card := by omega
        have : (1 : ℝ) ≤ ↑(bags (l - 1) (i / 2)).card := by exact_mod_cast h1
        linarith
      exact Finset.card_eq_zero.mp hcard_zero
  exact {
    alternating_empty := by
      intro level idx hparity
      have hpar : (t + (level + 1)) % 2 ≠ 0 := by omega
      have hfp : fromParent split level idx = ∅ :=
        fromParent_empty_of_parent_empty hsplit_sub
          (if h : level = 0 then Or.inl h
           else Or.inr (inv.alternating_empty _ _ (by omega)))
      unfold rebag
      rw [(split_empty_of_bags_empty hsplit_sub
            (inv.alternating_empty _ _ hpar)).1,
          (split_empty_of_bags_empty hsplit_sub
            (inv.alternating_empty _ _ hpar)).1,
          hfp]
      simp
    uniform_size := hrebag_uniform
    capacity_bound :=
      capacity_maintained split hC3 hA hν hlam_pos.le hkick hsend_left hsend_right
        hkick_pair hfrom_parent_empty
    stranger_bound := by
      intro level idx j hj
      by_cases hj1 : j = 1
      · subst hj1
        have h := stranger_bound_maintained_eq1 split hC4_eq1 hA hν hlam_pos hε_pos.le
          (fun l i ↦ by have h := hkick_stranger l i 1 (by omega); rwa [pow_one] at h)
          hparent_1stranger level idx
        simp only [Nat.sub_self, pow_zero, mul_one]; exact h
      · exact stranger_bound_maintained_gt1 split hC4_gt1 hA hν hlam_pos hε_pos.le
          hkick_stranger hparent_stranger level idx j (by omega)
    bags_disjoint := hrebag_disjoint
    bounded_depth := by
      intro level idx hlev
      have hfp : fromParent split level idx = ∅ := by
        unfold fromParent
        split_ifs with h₁ h₂
        · rfl
        · exact (hsplit_leaf _ _ (by omega)).1
        · exact (hsplit_leaf _ _ (by omega)).2
      unfold rebag
      rw [(split_empty_of_bags_empty hsplit_sub
            (inv.bounded_depth _ _ (by omega))).1,
          (split_empty_of_bags_empty hsplit_sub
            (inv.bounded_depth _ _ (by omega))).1,
          hfp]
      simp
    idx_bound := by
      intro level idx hidx
      have hempty_l : bags (level + 1) (2 * idx) = ∅ :=
        inv.idx_bound _ _ (by calc 2 ^ (level + 1) = 2 * 2 ^ level := by ring
                                _ ≤ 2 * idx := by omega)
      have hempty_r : bags (level + 1) (2 * idx + 1) = ∅ :=
        inv.idx_bound _ _ (by calc 2 ^ (level + 1) = 2 * 2 ^ level := by ring
                                _ ≤ 2 * idx + 1 := by omega)
      have hfp : fromParent split level idx = ∅ :=
        fromParent_empty_of_parent_empty hsplit_sub
          (if h : level = 0 then Or.inl h
           else Or.inr (inv.idx_bound _ _ (by
              have : 2 * 2 ^ (level - 1) = 2 ^ level := by
                conv_rhs => rw [show level = (level - 1) + 1 from by omega, pow_succ]
                ring
              omega)))
      unfold rebag
      rw [(split_empty_of_bags_empty hsplit_sub hempty_l).1,
          (split_empty_of_bags_empty hsplit_sub hempty_r).1, hfp]
      simp
    small_cap_even := by
      sorry
  }

/-! **Convergence** -/

/-- Convergence condition: at stage `T`, the maximum (leaf-level) bag capacity
    drops below 2, forcing all bags to have at most 1 item.
    `T` is `O(log n)` because capacity decays as `ν^T`. -/
def converged (n : ℕ) (A ν : ℝ) (t : ℕ) : Prop :=
  bagCapacity n A ν t (maxLevel n) < 2

/-- Capacity is monotone in level when `A ≥ 1`. -/
theorem bagCapacity_mono_level {n : ℕ} {A ν : ℝ} {t : ℕ}
    (hA : 1 ≤ A) (hν : 0 ≤ ν) {l₁ l₂ : ℕ} (h : l₁ ≤ l₂) :
    bagCapacity n A ν t l₁ ≤ bagCapacity n A ν t l₂ := by
  unfold bagCapacity
  have hp : A ^ l₁ ≤ A ^ l₂ := pow_le_pow_right₀ hA h
  have hc : (0 : ℝ) ≤ ↑n * ν ^ t := mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hν t)
  nlinarith
