/-
  # (γ, ε)-Separator Definitions

  Defines ε-approximate γ-separation (Seiferas 2009, Section 6), the
  separator-based reformulation of the AKS sorting network correctness proof.

  Key definitions:
  - `SepInitial`, `SepFinal`: one-sided separation properties
  - `IsApproxSep`: both-sided separation
  - `IsSeparator`: network-level separator property (quantified over permutations)

  For γ = 1/2, this reduces to ε-halving (`IsEpsilonHalver` in `Halver/Defs.lean`).
-/

import AKS.Sort.Defs
import AKS.Misc.Fin

open Finset BigOperators

/-! **ε-Approximate γ-Separation (Seiferas 2009, Section 6)** -/

/-- ε-approximate γ-separation, initial direction (Seiferas 2009, Section 6).
    For each γ' ≤ γ, at most ε·γ'·n of the ⌊γ'·n⌋ smallest output values
    are NOT placed among the first ⌊γ·n⌋ positions.

    In the filter, `pos` is an output position and `w pos` is the value there:
    • `rank (w pos) < ⌊γ' * n⌋₊` selects the ⌊γ'n⌋ smallest elements (by value)
    • `⌊γ * n⌋₊ ≤ rank pos` selects positions outside the first ⌊γn⌋ (by index) -/
def SepInitial {α : Type*} [Fintype α] [LinearOrder α]
    (w : α → α) (γ ε : ℝ) : Prop :=
  let n := Fintype.card α
  ∀ γ' : ℝ, 0 ≤ γ' → γ' ≤ γ →
    ((Finset.univ.filter (fun pos : α ↦
        ⌊γ * ↑n⌋₊ ≤ rank pos ∧ rank (w pos) < ⌊γ' * ↑n⌋₊)).card : ℝ) ≤ ε * γ' * ↑n

/-- ε-approximate γ-separation, final direction: dual via order reversal. -/
def SepFinal {α : Type*} [Fintype α] [LinearOrder α]
    (w : α → α) (γ ε : ℝ) : Prop :=
  SepInitial (α := αᵒᵈ) w γ ε

/-- ε-approximate γ-separation (Seiferas 2009, Section 6): both directions. -/
def IsApproxSep {α : Type*} [Fintype α] [LinearOrder α]
    (w : α → α) (γ ε : ℝ) : Prop :=
  SepInitial w γ ε ∧ SepFinal w γ ε

/-- A comparator network is a (γ, ε)-separator if for every permutation input,
    the output satisfies ε-approximate γ-separation. -/
def IsSeparator {n : ℕ} (net : ComparatorNetwork n) (γ ε : ℝ) : Prop :=
  ∀ (v : Equiv.Perm (Fin n)), IsApproxSep (net.exec v) γ ε
