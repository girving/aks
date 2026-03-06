module
/-
  # Split Cardinality Arithmetic

  Pure arithmetic for splitting `s` items into a parent part and two
  equal child parts, parameterised by a "fringe" count `f`.
  Used by `AKS/Bags/Sizes.lean` and `AKS/Bags/Strange.lean`.

  Key definitions:
  - `splitParentCard s f`: items kept by the parent
  - `splitChildCard s f`: items sent to each child
-/

public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Data.Rat.Cast.Order

@[expose] public section

/-! **Split Cardinalities** -/

/-- Number of items sent to parent when splitting `s` items with fringe `f`.
    Equals `2 * f + s % 2` when `f ≤ s / 2`, else `s`. -/
def splitParentCard (s f : ℕ) : ℕ := s - 2 * (s / 2 - f)

/-- Number of items sent to each child when splitting `s` items with fringe `f`.
    Equals `s / 2 - f` when `f ≤ s / 2`, else `0`. -/
def splitChildCard (s f : ℕ) : ℕ := s / 2 - f

/-- The three parts of a split account for all items. -/
theorem splitParentCard_add_two_childCard (s f : ℕ) :
    splitParentCard s f + 2 * splitChildCard s f = s := by
  simp only [splitParentCard, splitChildCard]; omega

/-- `splitParentCard` when fringe is 0: just the parity remainder. -/
theorem splitParentCard_zero (s : ℕ) : splitParentCard s 0 = s % 2 := by
  simp only [splitParentCard]; omega

/-- `splitChildCard` when fringe is 0: half the items. -/
theorem splitChildCard_zero (s : ℕ) : splitChildCard s 0 = s / 2 := by
  simp only [splitChildCard]; omega

/-- When fringe ≥ s/2, everything goes to parent. -/
theorem splitParentCard_ge (s f : ℕ) (hf : s / 2 ≤ f) :
    splitParentCard s f = s := by
  simp only [splitParentCard]; omega

/-- When fringe ≥ s/2, nothing goes to children. -/
theorem splitChildCard_ge (s f : ℕ) (hf : s / 2 ≤ f) :
    splitChildCard s f = 0 := by
  simp only [splitChildCard]; omega

/-- `splitParentCard 0 f = 0`: no items to split means nothing sent to parent. -/
theorem splitParentCard_zero_left (f : ℕ) : splitParentCard 0 f = 0 := by
  simp [splitParentCard]

/-- `splitChildCard 0 f = 0`: no items to split means nothing sent to children. -/
theorem splitChildCard_zero_left (f : ℕ) : splitChildCard 0 f = 0 := by
  simp [splitChildCard]

/-- `splitParentCard s f ≤ 2 * f + 1`, always.
    When `f ≤ s/2`: `= 2f + s%2 ≤ 2f + 1`.
    When `f > s/2`: `= s ≤ 2f ≤ 2f + 1`. -/
theorem splitParentCard_le_two_f_add_one (s f : ℕ) :
    splitParentCard s f ≤ 2 * f + 1 := by
  simp only [splitParentCard]; omega

/-- When `s` is even, `splitParentCard s f ≤ 2 * f` (no rounding).
    This is the key to Seiferas's Clause 3 small-capacity case. -/
theorem splitParentCard_le_two_f_of_even (s f : ℕ) (hs : 2 ∣ s) :
    splitParentCard s f ≤ 2 * f := by
  simp only [splitParentCard]; omega

/-- `splitChildCard` as ℚ is at most `s / 2`. -/
theorem splitChildCard_le_half_cast (s f : ℕ) :
    (splitChildCard s f : ℚ) ≤ (s : ℚ) / 2 := by
  simp only [splitChildCard]
  exact_mod_cast le_trans (Nat.cast_le.mpr (Nat.sub_le _ _)) (by exact Nat.cast_div_le)

/-- `splitParentCard s f` as ℚ is at most `2 * f + 1`. -/
theorem splitParentCard_le_cast (s f : ℕ) :
    (splitParentCard s f : ℚ) ≤ 2 * (f : ℚ) + 1 := by
  exact_mod_cast splitParentCard_le_two_f_add_one s f

end
