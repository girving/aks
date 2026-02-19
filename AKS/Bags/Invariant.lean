/-
  # Seiferas's Four-Clause Invariant

  Defines the invariant maintained by the bag-tree sorting network
  (Seiferas 2009, Sections 4–5) and states the maintenance theorems.

  The invariant has four clauses:
  1. Alternating levels empty: `(t + level) % 2 ≠ 0 → empty`
  2. Uniform size: all bags at an active level have equal size
  3. Capacity: items ≤ n · ν^t · A^level
  4. Strangers: j-strangers ≤ lam * eps^(j-1) * capacity

  All definitions validated by Rust simulation (`rust/test-bags.rs`):
  - Invariant holds with adversarial separator for n = 8..16384
  - All four clauses maintained across O(log n) stages
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

/-- Clause (3) maintenance: capacity bound at stage `t+1`.
    Requires constraint (C3): `ν ≥ 4*lam*A + 5/(2*A)`.
    Hypotheses on the split:
    - `hkick`: each bag kicks ≤ `2λ·cap + 1` items to parent
    - `hsend_left`/`hsend_right`: each bag sends ≤ `cap/2` items to each child
    - `hcap_ge`: root capacity ≥ A (ensures the +2 additive term is absorbed) -/
theorem capacity_maintained {n : ℕ} {A ν lam : ℝ} {t : ℕ}
    (split : ℕ → ℕ → SplitResult n)
    (hC3 : SatisfiesC3 A ν lam)
    (hA : 1 < A) (hν : 0 < ν)
    (hcap_ge : A ≤ ↑n * ν ^ t)
    (hkick : ∀ l i, ((split l i).toParent.card : ℝ) ≤
      2 * lam * bagCapacity n A ν t l + 1)
    (hsend_left : ∀ l i, ((split l i).toLeftChild.card : ℝ) ≤
      bagCapacity n A ν t l / 2)
    (hsend_right : ∀ l i, ((split l i).toRightChild.card : ℝ) ≤
      bagCapacity n A ν t l / 2) :
    ∀ level idx,
    ((rebag split level idx).card : ℝ) ≤ bagCapacity n A ν (t + 1) level := by
  intro level idx
  have hA_pos : (0 : ℝ) < A := by linarith
  -- bagCapacity n A ν t level ≥ A (since A^level ≥ 1 and n * ν^t ≥ A)
  have hb_ge : A ≤ bagCapacity n A ν t level := by
    simp only [bagCapacity]
    have h1 : 1 ≤ A ^ level := by
      calc (1 : ℝ) = A ^ 0 := (pow_zero A).symm
        _ ≤ A ^ level := pow_le_pow_right₀ (le_of_lt hA) (Nat.zero_le level)
    nlinarith [mul_nonneg (sub_nonneg.mpr hcap_ge) (sub_nonneg.mpr h1)]
  have hb_pos : (0 : ℝ) < bagCapacity n A ν t level := by linarith
  -- cap(t+1, level) = ν * cap(t, level)
  rw [bagCapacity_succ_stage]
  -- Union bound on card
  have hcard := rebag_card_le split level idx
  -- Bound children kicked up (cap at level+1 = A * cap(t, level))
  have ha := hkick (level + 1) (2 * idx)
  have hb' := hkick (level + 1) (2 * idx + 1)
  rw [bagCapacity_child] at ha hb'
  -- Bound parent contribution ≤ cap(t, level) / (2A)
  have hparent : ((fromParent split level idx).card : ℝ) ≤
      bagCapacity n A ν t level / (2 * A) := by
    unfold fromParent
    split_ifs with h₁ h₂
    · -- level = 0: no parent
      simp only [card_empty, Nat.cast_zero]
      exact div_nonneg (le_of_lt hb_pos) (by linarith)
    · -- level ≥ 1, even: left child from parent
      calc ((split (level - 1) (idx / 2)).toLeftChild.card : ℝ)
          ≤ bagCapacity n A ν t (level - 1) / 2 := hsend_left _ _
        _ = bagCapacity n A ν t level / (2 * A) := by
            simp only [bagCapacity]
            have hpow : A ^ level = A ^ (level - 1) * A := by
              conv_lhs => rw [show level = level - 1 + 1 from by omega]
              exact pow_succ A (level - 1)
            rw [hpow]; field_simp
    · -- level ≥ 1, odd: right child from parent
      calc ((split (level - 1) (idx / 2)).toRightChild.card : ℝ)
          ≤ bagCapacity n A ν t (level - 1) / 2 := hsend_right _ _
        _ = bagCapacity n A ν t level / (2 * A) := by
            simp only [bagCapacity]
            have hpow : A ^ level = A ^ (level - 1) * A := by
              conv_lhs => rw [show level = level - 1 + 1 from by omega]
              exact pow_succ A (level - 1)
            rw [hpow]; field_simp
  -- Combine: card ≤ 4*lam*A*cap + 2 + cap/(2*A) ≤ ν*cap
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
    (hA : 1 < A) (hν : 0 < ν) (hlam : 0 < lam) (hε : 0 ≤ ε)
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

/-- Parent 1-stranger bound: among items sent from parent to child bag B,
    the 1-strangers are bounded by `parentStrangerCoeff × capacity`.
    Combines four sub-sources (Seiferas Section 5):
    (a) ε fraction of parent's 1-strangers escape filtering
    (b) Halving errors: C-native items on wrong side of separator
    (c) Excess C-native from subtree stranger accumulation (geometric series with ratio `(2εA)²`)
    (d) C-native items from levels above parent -/
theorem parent_1stranger_bound {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n}
    (bags : BagAssignment n)
    (split : ℕ → ℕ → SplitResult n)
    (hA : 1 < A) (hlam : 0 < lam) (hε : 0 ≤ ε)
    (h2εA : (2 * ε * A) ^ 2 < 1)
    (hinv : SeifInvariant n A ν lam ε t perm bags)
    (level idx : ℕ) :
    (jStrangerCount n perm (fromParent split level idx) level idx 1 : ℝ) ≤
    parentStrangerCoeff A lam ε * bagCapacity n A ν t level := by
  sorry

/-- Full invariant maintenance: the invariant at stage `t` implies
    the invariant at stage `t+1` after applying the separator and rebagging.
    Requires all parameter constraints. -/
theorem invariant_maintained {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n}
    (split : ℕ → ℕ → SplitResult n)
    (inv : SeifInvariant n A ν lam ε t perm (rebag split))
    (hparams : SatisfiesConstraints A ν lam ε) :
    SeifInvariant n A ν lam ε (t + 1) perm (rebag split) := by
  sorry

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
