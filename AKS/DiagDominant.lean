/-
  # Diagonal Dominance → Positive Semidefiniteness

  Two results connecting diagonal dominance to matrix invertibility and PSD:

  1. `diagDominant_isUnit`: strict row diagonal dominance → `IsUnit` (invertible)
  2. `diagDominant_posSemidef`: strict row diagonal dominance → `PosSemidef`

  These are used in the certificate bridge: the PSD certificate produces a
  diagonally dominant congruence factor, which implies the spectral matrix is PSD.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Field

open Matrix BigOperators Finset


/-! **Diagonal dominance → invertibility** -/

/-- A strictly row-diagonally-dominant matrix is invertible.
    Chain: Gershgorin → `det ≠ 0` → `IsUnit det` → `IsUnit M`. -/
theorem diagDominant_isUnit {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ}
    (hdom : ∀ k, ∑ j ∈ Finset.univ.erase k, ‖M k j‖ < ‖M k k‖) :
    IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det]
  apply IsUnit.mk0
  exact det_ne_zero_of_sum_row_lt_diag hdom


/-! **Diagonal dominance → positive semidefiniteness** -/

/-- Swapping summation order over off-diagonal pairs:
    `∑ᵢ ∑_{j≠i} g(i,j) = ∑ⱼ ∑_{i≠j} g(i,j)`. -/
private theorem sum_erase_comm {n : ℕ} (g : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j ∈ univ.erase i, g i j = ∑ j, ∑ i ∈ univ.erase j, g i j := by
  suffices h : ∀ (f : Fin n → Fin n → ℝ),
      ∑ i, ∑ j ∈ univ.erase i, f i j = (∑ i, ∑ j, f i j) - ∑ i, f i i by
    rw [h g, h (fun i j ↦ g j i), Finset.sum_comm (f := fun j i ↦ g j i)]
  intro f
  have herase : ∀ i : Fin n,
      ∑ j ∈ univ.erase i, f i j = (∑ j, f i j) - f i i := by
    intro i
    have := Finset.sum_erase_add univ (f i) (Finset.mem_univ i)
    linarith
  simp_rw [herase, Finset.sum_sub_distrib]

/-- A Hermitian, strictly row-diagonally-dominant matrix is positive semidefinite.

    The quadratic form `xᵀMx ≥ ∑ᵢ (Mᵢᵢ - ∑ⱼ≠ᵢ |Mᵢⱼ|) xᵢ² ≥ 0`
    by AM-GM regrouping of off-diagonal terms. -/
theorem diagDominant_posSemidef {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hH : M.IsHermitian)
    (hdom : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖M i j‖ < M i i) :
    M.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro x
  simp only [star_trivial, dotProduct, mulVec, dotProduct]
  simp_rw [mul_sum]
  -- M is real symmetric
  have hM_symm : ∀ a b : Fin n, M a b = M b a := by
    intro a b
    have h1 : (Mᴴ) a b = M a b := congr_fun (congr_fun hH a) b
    rw [conjTranspose_apply, star_trivial] at h1
    exact h1.symm
  -- Decompose using add_sum_erase: separate diagonal from off-diagonal
  have herase : ∀ i : Fin n, ∑ j, x i * (M i j * x j) =
      M i i * x i ^ 2 + ∑ j ∈ univ.erase i, x i * (M i j * x j) := by
    intro i
    have h := Finset.add_sum_erase univ (fun j ↦ x i * (M i j * x j)) (Finset.mem_univ i)
    linarith [show x i * (M i i * x i) = M i i * x i ^ 2 from by ring]
  simp_rw [herase, Finset.sum_add_distrib]
  -- Goal: 0 ≤ ∑ᵢ Mᵢᵢ xᵢ² + ∑ᵢ ∑_{j≠i} xᵢ Mᵢⱼ xⱼ
  suffices hbound : ∑ i, ∑ j ∈ univ.erase i, x i * (M i j * x j) ≥
      -(∑ i, (∑ j ∈ univ.erase i, ‖M i j‖) * x i ^ 2) by
    have hgap : ∀ i : Fin n,
        0 ≤ (M i i - ∑ j ∈ univ.erase i, ‖M i j‖) * x i ^ 2 :=
      fun i ↦ mul_nonneg (by linarith [hdom i]) (sq_nonneg _)
    have hfact : ∑ i : Fin n, (M i i - ∑ j ∈ univ.erase i, ‖M i j‖) * x i ^ 2 =
        ∑ i, M i i * x i ^ 2 - ∑ i, (∑ j ∈ univ.erase i, ‖M i j‖) * x i ^ 2 := by
      simp only [sub_mul, Finset.sum_sub_distrib]
    have hnn : 0 ≤ ∑ i : Fin n, (M i i - ∑ j ∈ univ.erase i, ‖M i j‖) * x i ^ 2 :=
      Finset.sum_nonneg (fun i _ ↦ hgap i)
    linarith
  -- Bound off-diagonal: offdiag ≥ -∑ Rᵢ xᵢ²
  rw [ge_iff_le, neg_le_iff_add_nonneg]
  -- Goal: 0 ≤ ∑ Rᵢxᵢ² + offdiag. Suffices: 0 ≤ 2 * (sum).
  suffices h2 : 0 ≤ 2 * (∑ i, (∑ j ∈ univ.erase i, ‖M i j‖) * x i ^ 2 +
      ∑ i, ∑ j ∈ univ.erase i, x i * (M i j * x j)) by linarith
  -- Combine A+B into a double sum of f(i,j) = ‖Mij‖*xi² + xi*(Mij*xj)
  set f : Fin n → Fin n → ℝ := fun i j ↦ ‖M i j‖ * x i ^ 2 + x i * (M i j * x j) with hf
  have hAB : ∑ i, (∑ j ∈ univ.erase i, ‖M i j‖) * x i ^ 2 +
      ∑ i, ∑ j ∈ univ.erase i, x i * (M i j * x j) =
      ∑ i, ∑ j ∈ univ.erase i, f i j := by
    rw [← Finset.sum_add_distrib]
    congr 1; ext i; rw [Finset.sum_mul _ _ _, ← Finset.sum_add_distrib]
  -- 2*∑∑ f(i,j) = ∑∑ f(i,j) + ∑∑ f(j,i) [by sum_erase_comm]
  --             = ∑∑ (f(i,j) + f(j,i)) ≥ 0 [pointwise by AM-GM]
  rw [hAB, two_mul]
  conv_rhs => arg 1; rw [sum_erase_comm f]
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_nonneg; intro a _; apply Finset.sum_nonneg; intro b _
  -- Goal: 0 ≤ f b a + f a b
  -- Using M b a = M a b: = ‖M a b‖*(xa² + xb²) + 2*(M a b*xa*xb) ≥ 0
  simp only [hf]
  rw [hM_symm b a]
  have key : ‖M a b‖ * x b ^ 2 + x b * (M a b * x a) +
      (‖M a b‖ * x a ^ 2 + x a * (M a b * x b)) =
      ‖M a b‖ * (x a ^ 2 + x b ^ 2) + 2 * (M a b * (x a * x b)) := by ring
  rw [key]
  have h_amgm : 2 * |x a * x b| ≤ x a ^ 2 + x b ^ 2 := by
    rw [abs_mul]; have := two_mul_le_add_sq (|x a|) (|x b|)
    rw [sq_abs, sq_abs] at this; linarith
  have h_bound : |M a b * (x a * x b)| ≤ ‖M a b‖ * (x a ^ 2 + x b ^ 2) / 2 := by
    rw [abs_mul, Real.norm_eq_abs]
    calc |M a b| * |x a * x b|
        ≤ |M a b| * ((x a ^ 2 + x b ^ 2) / 2) := by gcongr; linarith [h_amgm]
      _ = |M a b| * (x a ^ 2 + x b ^ 2) / 2 := by ring
  linarith [neg_abs_le (M a b * (x a * x b)), norm_nonneg (M a b)]
