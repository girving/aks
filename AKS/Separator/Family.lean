module
/-
  # Separator Family

  Families of (γ, ε)-separator networks with bounded depth, analogous
  to `HalverFamily` in `Halver/Defs.lean`.

  Key definitions:
  • `SeparatorFamily` — structure bundling computable networks + proofs
  • `SeparatorFamily.twice_size_le` — size bound derived from depth bound
  • `SeparatorFamily.forWireCount` — bridge to arbitrary wire-count consumers
-/

public import AKS.Separator.Defs
public import AKS.Sort.Depth
public import AKS.Halver.Defs  -- for ComparatorNetwork.cast

@[expose] public section


open Finset BigOperators


/-! **Separator Family** -/

/-- A family of (γ, ε)-separator networks at all even sizes, with bounded
    depth. Mirrors `HalverFamily`: `net m` operates on `2 * m` wires.

    The type encodes which sizes exist: `net m` always operates on `2 * m`
    wires — no junk values, no validity threading. The depth bound is
    fundamental: `2 * (net m).size ≤ (2 * m) * depth` follows from
    `size_le_half_n_mul_depth`. -/
structure SeparatorFamily (γ ε : ℚ) where
  /-- Uniform depth bound for all networks in the family. -/
  depth : ℕ
  /-- The separator network for each index `m`. Operates on `2 * m` wires. -/
  net : (m : ℕ) → ComparatorNetwork (2 * m)
  /-- Each network is a (γ, ε)-separator. -/
  isSeparator : ∀ m, IsSeparator (net m) ↑γ ↑ε
  /-- Each network is an ε-halver (halving property).
      The separator is built from halvers, so it halves at the midpoint
      as well as separating at the γ-boundary. Used for the source-3
      halving error bound in `Bags/Strange.lean` (Seiferas 2009, Section 5). -/
  isHalver : ∀ m, IsEpsilonHalver (net m) ↑ε
  /-- Each network has depth at most `depth`. -/
  depth_le : ∀ m, (net m).depth ≤ depth

/-- Size bound derived from depth: `2 * size ≤ (2 * m) * sep.depth`. -/
theorem SeparatorFamily.twice_size_le {γ ε : ℚ}
    (family : SeparatorFamily γ ε) (m : ℕ) :
    2 * (family.net m).size ≤ (2 * m) * family.depth :=
  calc 2 * (family.net m).size
      ≤ (2 * m) * (family.net m).depth := size_le_half_n_mul_depth (family.net m)
    _ ≤ (2 * m) * family.depth := Nat.mul_le_mul_left _ (family.depth_le m)


/-! **Wire Count Bridge** -/

/-- Bridge a `SeparatorFamily` to an arbitrary wire count `n`.
    If `n` is even (`2 * (n / 2) = n`), uses `sep.net (n / 2)` cast to `n` wires.
    Otherwise returns the empty network. -/
def SeparatorFamily.forWireCount {γ ε : ℚ}
    (sep : SeparatorFamily γ ε) (n : ℕ) :
    ComparatorNetwork n :=
  if h : 2 * (n / 2) = n
  then (sep.net (n / 2)).cast h
  else ⟨[]⟩

/-- `forWireCount` has depth at most `sep.depth`. -/
theorem SeparatorFamily.forWireCount_depth_le {γ ε : ℚ}
    (sep : SeparatorFamily γ ε) (n : ℕ) :
    (sep.forWireCount n).depth ≤ sep.depth := by
  unfold forWireCount; split
  · simp [ComparatorNetwork.cast_depth, sep.depth_le]
  · simp [ComparatorNetwork.depth]

end
