/-
  # Halver → Separator Construction

  Constructs (γ, ε)-separator networks from ε-halver families by
  iterated halving (Seiferas 2009, Section 6, Lemma 1).

  Key definitions:
  • `halverToSeparator` — computable construction reusing `halverNetwork`
  • `halverToSeparatorFamily` — bundles into a `SeparatorFamily`

  Key results:
  • `halver_isSeparator_half` — base case: ε-halver → (1/2, ε)-separator (proved)
  • `separator_halving_step` — halving refines γ → γ/2
  • `halverToSeparator_isSeparator` — t levels → (1/2^t, 2tε)-separation
  • `halverToSeparator_depth_le` — depth ≤ t · d
-/

import AKS.Separator.Family
import AKS.Nearsort.Construction
import Mathlib.Algebra.Order.Floor.Semifield

open Finset BigOperators


/-! **Construction** -/

/-- Build a separator from a halver family by iterating `t` levels of
    recursive halving. Reuses `halverNetwork` from `Nearsort/Construction.lean`. -/
def halverToSeparator {ε : ℝ} {d : ℕ} (n : ℕ) (family : HalverFamily ε d)
    (t : ℕ) : ComparatorNetwork n :=
  halverNetwork n family.net t


/-! **Floor/division bridging lemmas** -/

/-- `⌊(1/2) * ↑n⌋₊ = n / 2` for natural `n`. -/
private lemma floor_half_eq_div2 (n : ℕ) : ⌊(1 / 2 : ℝ) * ↑n⌋₊ = n / 2 := by
  rw [show (1 / 2 : ℝ) * ↑n = ↑n / 2 from by ring]
  exact Nat.floor_div_eq_div n 2

/-- For `0 ≤ γ' ≤ 1/2`, `⌊γ' * n⌋₊ ≤ n / 2`. -/
private lemma floor_gamma_le_div2 (n : ℕ) (γ' : ℝ) (_hγ' : 0 ≤ γ') (hle : γ' ≤ 1 / 2) :
    ⌊γ' * ↑n⌋₊ ≤ n / 2 := by
  calc ⌊γ' * ↑n⌋₊
      ≤ ⌊(1 / 2 : ℝ) * ↑n⌋₊ := by
        apply Nat.floor_le_floor
        exact mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)
    _ = n / 2 := floor_half_eq_div2 n


/-! **Base case: ε-halver is a (1/2, ε)-separator** -/

/-- Bridge: `EpsilonInitialHalved` implies `SepInitial` at γ = 1/2.
    Generalized over any linearly ordered finite type (handles both
    `Fin n` for the initial direction and `(Fin n)ᵒᵈ` for the final). -/
private lemma epsilonInitialHalved_implies_sepInitial
    {α : Type*} [Fintype α] [LinearOrder α]
    {w : α → α} {ε : ℝ} (hε : 0 ≤ ε)
    (h : EpsilonInitialHalved w ε) : SepInitial w (1 / 2) ε := by
  set N := Fintype.card α with hN_def
  show ∀ γ' : ℝ, 0 ≤ γ' → γ' ≤ 1 / 2 →
    ((Finset.univ.filter (fun pos : α ↦
        ⌊(1 / 2 : ℝ) * ↑N⌋₊ ≤ rank pos ∧ rank (w pos) < ⌊γ' * ↑N⌋₊)).card : ℝ) ≤
      ε * γ' * ↑N
  intro γ' hγ' hγ'_le
  set k := ⌊γ' * ↑N⌋₊ with hk_def
  rw [floor_half_eq_div2]
  have hk_le : k ≤ N / 2 := floor_gamma_le_div2 N γ' hγ' hγ'_le
  calc ((Finset.univ.filter (fun pos : α ↦
          N / 2 ≤ rank pos ∧ rank (w pos) < k)).card : ℝ)
      ≤ ε * ↑k := h k hk_le
    _ ≤ ε * (γ' * ↑N) := by
        apply mul_le_mul_of_nonneg_left _ hε
        exact_mod_cast Nat.floor_le (mul_nonneg hγ' (Nat.cast_nonneg _))
    _ = ε * γ' * ↑N := by ring

/-- An ε-halver provides ε-approximate (1/2)-separation (Seiferas Lemma 1 base).

    The halver bounds `EpsilonInitialHalved` quantify over `k ≤ n/2` and count
    elements with `rank pos ≥ n/2 ∧ rank (w pos) < k`. The separator bounds
    `SepInitial` at γ = 1/2 quantify over `γ' ≤ 1/2` and count elements with
    `rank pos ≥ ⌊(1/2)·n⌋₊ ∧ rank (w pos) < ⌊γ'·n⌋₊`.

    The bridge: `⌊(1/2)·n⌋₊ = n/2` (nat division) and setting `k = ⌊γ'·n⌋₊`
    gives `k ≤ n/2`. The error bound `ε·k ≤ ε·γ'·n` since `k ≤ γ'·n`. -/
theorem halver_isSeparator_half {n : ℕ} (net : ComparatorNetwork n) (ε : ℝ)
    (hε : 0 ≤ ε) (h : IsEpsilonHalver net ε) :
    IsSeparator net (1 / 2) ε := by
  intro v
  obtain ⟨h_init, h_final⟩ := h v
  exact ⟨epsilonInitialHalved_implies_sepInitial hε h_init,
         epsilonInitialHalved_implies_sepInitial hε h_final⟩


/-! **Induction step** -/

/-- Halving refines separation: applying ε₁-halvers to both halves of a
    (γ, ε')-separated sequence gives (γ/2, ε' + 2·ε₁)-separation.

    Elements correctly in the γ-fringe stay correct. Elements that were
    ε'-displaced gain at most ε₁ additional displacement from the halver.
    (Seiferas 2009, Section 6, proof of Lemma 1) -/
theorem separator_halving_step {n : ℕ} {γ ε' ε₁ : ℝ}
    {net : ComparatorNetwork n}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)}
    (_hγ : 0 < γ) (_hγ1 : γ ≤ 1)
    (_hsep : IsSeparator net γ ε')
    (_hhalver : ∀ m, IsEpsilonHalver (halvers m) ε₁)
    (level : ℕ) :
    IsSeparator
      { comparators := net.comparators ++ (halverAtLevel n halvers level).comparators }
      (γ / 2)
      (ε' + 2 * ε₁) := by
  sorry


/-! **Iterated halving** -/

/-- `t` levels of iterated ε-halving give (2·t·ε)-approximate (1/2^t)-separation.

    Proof: induction on `t` using `halver_isSeparator_half` (base) and
    `separator_halving_step` (step). At each level, errors accumulate:
    the halver introduces ε per application (initial + final), giving +2ε per level.
    (Seiferas 2009, Section 6, Lemma 1) -/
theorem halverToSeparator_isSeparator {ε : ℝ} {d : ℕ}
    (n : ℕ) (family : HalverFamily ε d) (t : ℕ) (hε : 0 ≤ ε) :
    IsSeparator (halverToSeparator n family t) (1 / 2 ^ t) (2 * ↑t * ε) := by
  sorry


/-! **Depth bound** -/

/-- Per-level depth bound: halvers at one tree level operate on disjoint
    wire ranges (different sub-intervals), so they run in parallel. -/
theorem halverAtLevel_depth_le {ε : ℝ} {d : ℕ}
    (n : ℕ) (family : HalverFamily ε d) (level : ℕ) :
    (halverAtLevel n family.net level).depth ≤ d := by
  sorry

/-- Iterated separator depth ≤ t · d. At each of `t` levels, halvers at the
    same level operate on disjoint wire ranges, giving depth ≤ d per level.
    Levels are sequential (concatenated), so total depth ≤ t · d. -/
theorem halverToSeparator_depth_le {ε : ℝ} {d : ℕ}
    (n : ℕ) (family : HalverFamily ε d) (t : ℕ) :
    (halverToSeparator n family t).depth ≤ t * d := by
  sorry


/-! **Bundle into SeparatorFamily** -/

/-- Build a `SeparatorFamily` from a `HalverFamily` with `t` iteration levels.
    (Seiferas 2009, Section 6, Lemma 1) -/
def halverToSeparatorFamily {ε : ℝ} {d : ℕ} (family : HalverFamily ε d)
    (t : ℕ) (hε : 0 ≤ ε) :
    SeparatorFamily (1 / 2 ^ t) (2 * ↑t * ε) (t * d) where
  net n := halverToSeparator n family t
  isSep n := halverToSeparator_isSeparator n family t hε
  depth_le n := halverToSeparator_depth_le n family t
