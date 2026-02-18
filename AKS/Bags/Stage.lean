/-
  # One-Stage Separator Network

  Defines one stage of the bag-tree sorting network: apply a separator to all
  active bags in parallel (Seiferas 2009, Section 7).

  Key results:
  - `separatorStage`: computable network for one stage
  - `active_bags_disjoint`: active bags have disjoint registers
  - `separatorStage_depth_le`: depth per stage = separator depth (parallel)
-/

import AKS.Bags.Invariant
import AKS.Separator.Family

/-! **Active Bags** -/

/-- A bag is active at stage `t` if `(t + level) % 2 = 0` (from parity convention). -/
def bagActive (t level : ℕ) : Prop := (t + level) % 2 = 0

instance (t level : ℕ) : Decidable (bagActive t level) :=
  inferInstanceAs (Decidable ((t + level) % 2 = 0))

/-! **Disjointness** -/

/-- Active bags at different (level, idx) pairs have disjoint register sets.
    This follows from the alternating-empty invariant: at any given stage,
    active bags exist only at even or odd levels, and bags at the same level
    partition the register space. -/
theorem active_bags_disjoint {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (l₁ l₂ i₁ i₂ : ℕ) (hne : (l₁, i₁) ≠ (l₂, i₂))
    (h₁ : bagActive t l₁) (h₂ : bagActive t l₂) :
    Disjoint (bags l₁ i₁) (bags l₂ i₂) := by
  sorry

/-! **One-Stage Network Construction** -/

/-- Apply the separator to all active bags at stage `t`. Computable.

    The key observation (Seiferas Section 7): active bags at stage `t` have
    **disjoint register sets** (from the alternating-empty invariant). Therefore
    all separator applications within one stage operate on non-overlapping wires
    and can run in **parallel**. -/
def separatorStage (n : ℕ) {gam eps : ℝ} {d_sep : ℕ}
    (sep : SeparatorFamily gam eps d_sep) (stageIdx : ℕ) : ComparatorNetwork n where
  comparators := []  -- placeholder: actual construction applies sep to each active bag

/-- One stage has depth at most the separator depth, since all active bags
    have disjoint registers and their separators run in parallel. -/
theorem separatorStage_depth_le (n : ℕ) {gam eps : ℝ} {d_sep : ℕ}
    (sep : SeparatorFamily gam eps d_sep) (stageIdx : ℕ) :
    (separatorStage n sep stageIdx).depth ≤ d_sep := by
  sorry
