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

/-! **Invariant Maintenance Theorems (Seiferas Section 5)** -/

/-- Items received from parent (sent down during rebagging).
    Parent at `(level-1, idx/2)` sends `≤ bagCapacity / (2A)` items to each child. -/
theorem items_from_parent_bound {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hA : 1 < A) (level idx : ℕ) (hlevel : 1 ≤ level) :
    True := by  -- placeholder for the real bound statement
  trivial

/-- Items received from children (kicked up during rebagging).
    Each child at `(level+1, 2*idx)` and `(level+1, 2*idx+1)` kicks up
    at most `2*floor(lam*b_child) + 1` items, for a total of at most `4*lam*b*A + 2`. -/
theorem items_from_children_bound {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hA : 1 < A) (level idx : ℕ) :
    True := by  -- placeholder for the real bound statement
  trivial

/-- Clause (3) maintenance: capacity bound at stage `t+1`.
    Requires constraint (C3): `ν ≥ 4*lam*A + 5/(2*A)`. -/
theorem capacity_maintained {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags bags' : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hC3 : SatisfiesC3 A ν lam) :
    ∀ level idx,
    ((bags' level idx).card : ℝ) ≤ bagCapacity n A ν (t + 1) level := by
  sorry

/-- Clause (4) maintenance for `j ≥ 2`: stranger bound at stage `t+1`.
    Sources: (j+1)-strangers from children kicked up + (j-1)-strangers from parent.
    Requires constraint (C4, j>1): `2·A·ε + 1/A ≤ ν`. -/
theorem stranger_bound_maintained_gt1 {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags bags' : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hC4 : SatisfiesC4_gt1 A ν ε) (level idx j : ℕ) (hj : 2 ≤ j) :
    (jStrangerCount n perm (bags' level idx) level idx j : ℝ) ≤
    lam * ε ^ (j - 1) * bagCapacity n A ν (t + 1) level := by
  sorry

/-- Clause (4) maintenance for `j = 1`: 1-stranger bound at stage `t+1`.
    This is the hardest case (Seiferas Section 5). Three sources:
    (a) 2+-strangers from children kicked up: at most 2*lam*eps*A*b
    (b) 1-strangers from parent sent down: at most eps*lam*b/A
    (c) Sibling leakage via separator error: geometric series in (2εA)²
    Requires the master constraint (C4, j=1). -/
theorem stranger_bound_maintained_eq1 {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags bags' : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hC4 : SatisfiesC4_eq1 A ν lam ε) (level idx : ℕ) :
    (jStrangerCount n perm (bags' level idx) level idx 1 : ℝ) ≤
    lam * bagCapacity n A ν (t + 1) level := by
  sorry

/-- Full invariant maintenance: the invariant at stage `t` implies
    the invariant at stage `t+1` after applying the separator and rebagging.
    Requires all parameter constraints. -/
theorem invariant_maintained {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags bags' : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hparams : SatisfiesConstraints A ν lam ε) :
    SeifInvariant n A ν lam ε (t + 1) perm bags' := by
  sorry

/-! **Convergence** -/

/-- Convergence condition: at stage `T`, leaf capacity drops below `1/lam`,
    forcing zero items at leaves (since items are integers).
    `T` is `O(log n)` because capacity decays as `ν^T`. -/
def converged (n : ℕ) (A ν lam : ℝ) (t : ℕ) : Prop :=
  bagCapacity n A ν t (maxLevel n) < 1 / lam
