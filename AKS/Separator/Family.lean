/-
  # Separator Family

  Families of (γ, ε)-separator networks with bounded depth, analogous
  to `HalverFamily` in `Halver/Defs.lean`.

  Key definitions:
  • `SeparatorFamily` — structure bundling computable networks + proofs
  • `SeparatorFamily.size_le` — size bound derived from depth bound
-/

import AKS.Separator.Defs
import AKS.Sort.Depth

open Finset BigOperators


/-! **Separator Family** -/

/-- A family of (γ, ε)-separator networks, one per input size,
    with depth bounded by `d`. Analogous to `HalverFamily`.

    The `valid` predicate specifies which input sizes have the separator
    property. For halver-based separators, `valid n ↔ 2^t ∣ n`
    (divisibility by the recursion depth). The sorting network only uses
    the separator at valid sizes (bag sizes are powers of 2).

    The depth bound is fundamental: `2 * size ≤ n * d` follows from
    `size_le_half_n_mul_depth`. -/
structure SeparatorFamily (γ ε : ℝ) (d : ℕ) where
  /-- The separator network for each input size `n`. -/
  net : (n : ℕ) → ComparatorNetwork n
  /-- Which input sizes satisfy the separator property. -/
  valid : ℕ → Prop
  /-- Each network at a valid size is a (γ, ε)-separator. -/
  isSep : ∀ n, valid n → IsSeparator (net n) γ ε
  /-- Each network has depth at most `d`. -/
  depth_le : ∀ n, (net n).depth ≤ d

/-- Size bound derived from depth: `2 * size ≤ n * d`. -/
theorem SeparatorFamily.twice_size_le {γ ε : ℝ} {d : ℕ}
    (family : SeparatorFamily γ ε d) (n : ℕ) :
    2 * (family.net n).size ≤ n * d :=
  calc 2 * (family.net n).size
      ≤ n * (family.net n).depth := size_le_half_n_mul_depth (family.net n)
    _ ≤ n * d := Nat.mul_le_mul_left _ (family.depth_le n)
