/-
  # Spectral Matrix and PSD → Walk Bound

  Defines the spectral matrix `M = c₁I - c₂A² + c₃J` where `A = d · adjMatrix G`
  is the **unnormalized** adjacency matrix, and proves that if this matrix is PSD,
  then the walk operator satisfies `c₂ · d² · ‖Wf‖² ≤ c₁ · ‖f‖²` for mean-zero `f`.

  The unnormalized adjacency is used because the certificate checker (`mulAdj` in
  `Certificate.lean`) sums neighbors without dividing by `d`. This ensures the PSD
  condition directly yields the `d²` factor needed for spectral gap estimation.

  This is Layer 1 of the bridge decomposition:
  ```
  M PSD on 1⊥  →  walk bound  (this file)
  K diag-dominant + Z invertible  →  M PSD  (DiagDominant.lean)
  checkCertificateSlow = true  →  K diag-dominant  (proved in CertificateBridge.lean)
  ```
-/

import AKS.Graph.Regular
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix BigOperators Finset


/-! **Spectral matrix definition** -/

/-- The spectral matrix `M = c₁I - c₂A² + c₃J` where `A = d · adjMatrix G`
    (unnormalized adjacency) and `J = Matrix.of (fun _ _ ↦ 1)` (all-ones matrix).

    When `M` is PSD, the `c₃J` term vanishes on mean-zero vectors, giving
    `c₂ · d² · ‖Wf‖² ≤ c₁ · ‖f‖²` — the walk bound. -/
noncomputable def spectralMatrix {n d : ℕ} (G : RegularGraph n d)
    (c₁ c₂ c₃ : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  let A := (d : ℝ) • adjMatrix G
  c₁ • (1 : Matrix (Fin n) (Fin n) ℝ) - c₂ • (A * A)
    + c₃ • Matrix.of (fun (_ _ : Fin n) ↦ (1 : ℝ))


/-! **Hermitian property** -/

/-- The spectral matrix is Hermitian (real symmetric). -/
theorem spectralMatrix_isHermitian {n d : ℕ} (G : RegularGraph n d)
    (c₁ c₂ c₃ : ℝ) : Matrix.IsHermitian (spectralMatrix G c₁ c₂ c₃) := by
  unfold spectralMatrix
  set A := (d : ℝ) • adjMatrix G with hA_def
  have hB := adjMatrix_isHermitian G
  have hA : A.IsHermitian := by
    show Aᴴ = A
    rw [hA_def, conjTranspose_smul, star_trivial, hB.eq]
  have hAA : (A * A).IsHermitian := by
    have h := conjTranspose_mul A A
    rw [hA.eq] at h; exact h
  have smul_herm : ∀ (c : ℝ) (M : Matrix (Fin n) (Fin n) ℝ),
      M.IsHermitian → (c • M).IsHermitian := by
    intro c M hM
    show (c • M)ᴴ = c • M
    rw [conjTranspose_smul, star_trivial, hM.eq]
  have hJ : (Matrix.of (fun (_ _ : Fin n) ↦ (1 : ℝ))).IsHermitian := by
    show (Matrix.of fun _ _ ↦ (1 : ℝ))ᴴ = Matrix.of fun _ _ ↦ 1
    ext i j
    simp [conjTranspose_apply, star_trivial]
  exact ((smul_herm c₁ _ isHermitian_one).sub (smul_herm c₂ _ hAA)).add (smul_herm c₃ _ hJ)


/-! **Helper lemmas for the walk bound** -/

/-- Fiberwise sum identity: ∑ u, card{i | nbr v i = u} * x u = ∑ i, x(nbr v i). -/
private theorem sum_card_mul_eq {n d : ℕ} (G : RegularGraph n d)
    (x : Fin n → ℝ) (v : Fin n) :
    ∑ u : Fin n, ↑(univ.filter (fun i : Fin d ↦ G.neighbor v i = u)).card * x u =
    ∑ i : Fin d, x (G.neighbor v i) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := G.neighbor v)
    (fun i _ ↦ Finset.mem_univ _) (fun i ↦ x (G.neighbor v i))]
  congr 1; ext u
  rw [show ∑ i ∈ univ.filter (fun i ↦ G.neighbor v i = u), x (G.neighbor v i) =
      ∑ i ∈ univ.filter (fun i ↦ G.neighbor v i = u), x u from
    Finset.sum_congr rfl (fun i hi ↦ by
      simp only [Finset.mem_filter] at hi; rw [hi.2])]
  rw [Finset.sum_const, nsmul_eq_mul]

/-- The unnormalized adjacency matrix times a vector gives the neighbor sum:
    `(d • adjMatrix G *ᵥ x)(v) = ∑ i, x (G.neighbor v i)`. -/
theorem unnorm_adj_mulVec {n d : ℕ} (G : RegularGraph n d)
    (x : Fin n → ℝ) (v : Fin n) :
    (((d : ℝ) • adjMatrix G) *ᵥ x) v = ∑ i : Fin d, x (G.neighbor v i) := by
  rw [smul_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, adjMatrix_apply]
  -- Goal: d * ∑ u, (card / d) * x u = ∑ i, x(nbr v i)
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hd_ne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, mul_div_cancel₀ _ hd_ne]
    exact sum_card_mul_eq G x v

/-- For a symmetric real matrix, `x ⬝ᵥ (A *ᵥ y) = (A *ᵥ x) ⬝ᵥ y`. -/
private theorem dotProduct_mulVec_symm {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (x y : Fin n → ℝ) :
    x ⬝ᵥ (A *ᵥ y) = (A *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec]
  congr 1
  -- x ᵥ* A = A *ᵥ x for symmetric A
  have := vecMul_transpose A x  -- x ᵥ* Aᵀ = A *ᵥ x
  rwa [hA.eq] at this


/-! **PSD → walk bound** -/

/-- If the spectral matrix is PSD, mean-zero vectors satisfy the walk bound.

    **Proof sketch:**
    1. PSD: `0 ≤ xᵀMx` for all `x`
    2. Mean-zero `f` ⟹ `Jf = 0` ⟹ `xᵀMx = c₁‖x‖² - c₂‖Ax‖²`
    3. Therefore `c₂‖Ax‖² ≤ c₁‖x‖²`
    4. `‖Ax‖² = d² · ‖Wf‖²` (since `A(v,u) = d · adjMatrix(v,u)`,
       and `∑_u A(v,u) x(u) = ∑_i x(nbr v i) = d · walkCLM f v`) -/
theorem spectralMatrix_posSemidef_implies_walk_bound
    {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (G : RegularGraph n d) (c₁ c₂ c₃ : ℝ)
    (hpsd : Matrix.PosSemidef (spectralMatrix G c₁ c₂ c₃))
    (f : EuclideanSpace ℝ (Fin n)) (hf : meanCLM n f = 0) :
    c₂ * (d : ℝ) ^ 2 * ‖G.walkCLM f‖ ^ 2 ≤ c₁ * ‖f‖ ^ 2 := by
  have hd_ne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hd_sq_ne : (d : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hd_ne
  -- Mean-zero implies ∑ f v = 0
  have hsum : ∑ v : Fin n, f v = 0 := by
    have : (∑ i : Fin n, f i) / ↑n = 0 := by
      calc (∑ i : Fin n, f i) / ↑n
          = meanCLM n f ⟨0, hn⟩ := (meanCLM_apply n f _).symm
        _ = (0 : EuclideanSpace ℝ (Fin n)) ⟨0, hn⟩ := by rw [hf]
        _ = 0 := rfl
    exact (div_eq_zero_iff.mp this).elim id
      (fun h ↦ absurd (Nat.cast_eq_zero.mp h) (by omega))
  -- Reduce to core sum inequality:
  -- c₂ * ∑ v, (∑ i, f(nbr v i))² ≤ c₁ * ∑ v, (f v)²
  suffices key : c₂ * ∑ v : Fin n, (∑ i : Fin d, f (G.neighbor v i)) ^ 2 ≤
      c₁ * ∑ v : Fin n, (f v) ^ 2 by
    -- Bridge: norms to sums
    rw [show c₁ * ‖f‖ ^ 2 = c₁ * ∑ v : Fin n, (f v) ^ 2 from by
      rw [EuclideanSpace.norm_sq_eq]; simp_rw [Real.norm_eq_abs, sq_abs]]
    rw [show c₂ * (d : ℝ) ^ 2 * ‖G.walkCLM f‖ ^ 2 =
        c₂ * ∑ v : Fin n, (∑ i : Fin d, f (G.neighbor v i)) ^ 2 from by
      rw [EuclideanSpace.norm_sq_eq]
      simp_rw [Real.norm_eq_abs, sq_abs, RegularGraph.walkCLM_apply, div_pow]
      rw [← Finset.sum_div, mul_assoc]
      congr 1; rw [mul_comm, div_mul_cancel₀ _ hd_sq_ne]]
    exact key
  -- From PSD: the quadratic form is nonneg
  set x : Fin n → ℝ := fun v ↦ f v with hx_def
  have hqf := hpsd.dotProduct_mulVec_nonneg x
  simp only [star_trivial] at hqf
  -- Decompose the mulVec using linearity
  set A := (d : ℝ) • adjMatrix G with hA_def
  have hMvx : spectralMatrix G c₁ c₂ c₃ *ᵥ x =
      c₁ • x - c₂ • ((A * A) *ᵥ x) +
      c₃ • ((Matrix.of fun _ _ ↦ (1 : ℝ)) *ᵥ x) := by
    change (c₁ • (1 : Matrix (Fin n) (Fin n) ℝ) - c₂ • (A * A) +
        c₃ • Matrix.of (fun (_ _ : Fin n) ↦ (1 : ℝ))) *ᵥ x = _
    simp only [add_mulVec, sub_mulVec, smul_mulVec, one_mulVec]
  rw [hMvx] at hqf
  -- Distribute dotProduct over +, -, •
  simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hqf
  -- Identify the three terms
  -- Term 1: x ⬝ᵥ x = ∑ (f v)²
  have hI : x ⬝ᵥ x = ∑ v : Fin n, (f v) ^ 2 := by
    simp only [dotProduct, hx_def, sq]
  -- Term 2: x ⬝ᵥ ((A * A) *ᵥ x) = ∑ (∑ f(nbr))²
  have hA_symm : A.IsSymm := by
    show Aᵀ = A
    rw [hA_def, transpose_smul, (adjMatrix_isSymm G).eq]
  have hAA_quad : x ⬝ᵥ ((A * A) *ᵥ x) =
      ∑ v : Fin n, (∑ i : Fin d, f (G.neighbor v i)) ^ 2 := by
    rw [← mulVec_mulVec]
    rw [dotProduct_mulVec_symm hA_symm x (A *ᵥ x)]
    simp only [dotProduct, sq]
    congr 1; ext v
    rw [hA_def, unnorm_adj_mulVec G x v]
  -- Term 3: x ⬝ᵥ (J *ᵥ x) = (∑ f v)² = 0
  have hJ_quad : x ⬝ᵥ ((Matrix.of fun _ _ ↦ (1 : ℝ)) *ᵥ x) = 0 := by
    simp only [dotProduct, mulVec, dotProduct, Matrix.of_apply, one_mul, hx_def]
    rw [← Finset.sum_mul, hsum, zero_mul]
  -- Combine
  rw [hI, hAA_quad, hJ_quad, mul_zero, add_zero] at hqf
  linarith
