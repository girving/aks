/-
  # General Graph Walk Operator and Spectral Gap

  The normalized walk operator for general (irregular) graphs, defined via
  the self-adjoint operator `D^{-1/2} A D^{-1/2}` on `EuclideanSpace`.

  For a `Graph n` with half-edge representation:
  - Walk operator: `(Nf)(v) = (1/√deg(v)) · ∑_{e: src(e)=v} f(target(e)) / √deg(target(e))`
  - Mean projection: onto `u(v) = √deg(v) / √halfs`
  - Spectral gap: `‖N - P‖`

  Self-adjointness follows from the rotation bijection (same trick as `RegularGraph`).
  Division by zero is harmless: `Real.sqrt 0 = 0` and `a / 0 = 0` in Lean.
-/

import AKS.Graph.Graph

open Finset BigOperators

noncomputable section


/-! **Walk Operator** -/

/-- The normalized walk function on plain vectors:
    `(Nf)(v) = (1/√deg(v)) · ∑_{e: src(e)=v} f(target(e)) / √deg(target(e))`. -/
def Graph.normalizedWalkFun {n : ℕ} (G : Graph n) (f : Fin n → ℝ) : Fin n → ℝ :=
  fun v ↦ (1 / Real.sqrt (G.deg v)) *
    ∑ e ∈ univ.filter (G.src · = v), f (G.target e) / Real.sqrt (G.deg (G.target e))

/-- The normalized walk operator as a linear map on `EuclideanSpace`. -/
def Graph.normalizedWalkLM {n : ℕ} (G : Graph n) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun f := WithLp.toLp 2 (G.normalizedWalkFun (WithLp.ofLp f))
  map_add' f g := by
    apply PiLp.ext; intro v
    show G.normalizedWalkFun (WithLp.ofLp f + WithLp.ofLp g) v =
      G.normalizedWalkFun (WithLp.ofLp f) v + G.normalizedWalkFun (WithLp.ofLp g) v
    simp only [Graph.normalizedWalkFun, Pi.add_apply, add_div,
      Finset.sum_add_distrib, mul_add]
  map_smul' r f := by
    apply PiLp.ext; intro v
    show G.normalizedWalkFun (r • WithLp.ofLp f) v =
      r • G.normalizedWalkFun (WithLp.ofLp f) v
    simp only [Graph.normalizedWalkFun, Pi.smul_apply, smul_eq_mul]
    have : ∀ e, r * (WithLp.ofLp f) (G.target e) / Real.sqrt ↑(G.deg (G.target e)) =
        r * ((WithLp.ofLp f) (G.target e) / Real.sqrt ↑(G.deg (G.target e))) :=
      fun e ↦ mul_div_assoc _ _ _
    simp_rw [this, ← Finset.mul_sum]; ring

/-- The normalized walk operator as a continuous linear map on `EuclideanSpace`. -/
def Graph.normalizedWalkCLM {n : ℕ} (G : Graph n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  G.normalizedWalkLM.toContinuousLinearMap

@[simp]
theorem Graph.normalizedWalkCLM_apply {n : ℕ} (G : Graph n)
    (f : EuclideanSpace ℝ (Fin n)) (v : Fin n) :
    G.normalizedWalkCLM f v = (1 / Real.sqrt (G.deg v)) *
      ∑ e ∈ univ.filter (G.src · = v), f (G.target e) / Real.sqrt (G.deg (G.target e)) :=
  rfl


/-! **Mean Projection** -/

/-- The degree-weighted mean function: projects onto the `√deg` direction.
    `(Pf)(v) = √deg(v) · (∑_w f(w) · √deg(w)) / halfs`. -/
def Graph.degreeMeanFun {n : ℕ} (G : Graph n) (f : Fin n → ℝ) : Fin n → ℝ :=
  fun v ↦ Real.sqrt (G.deg v) * (∑ w, f w * Real.sqrt (G.deg w)) / G.halfs

/-- The degree-weighted mean projection as a linear map on `EuclideanSpace`. -/
def Graph.degreeMeanLM {n : ℕ} (G : Graph n) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun f := WithLp.toLp 2 (G.degreeMeanFun (WithLp.ofLp f))
  map_add' f g := by
    apply PiLp.ext; intro v
    show G.degreeMeanFun (WithLp.ofLp f + WithLp.ofLp g) v =
      G.degreeMeanFun (WithLp.ofLp f) v + G.degreeMeanFun (WithLp.ofLp g) v
    simp only [Graph.degreeMeanFun, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' r f := by
    apply PiLp.ext; intro v
    show G.degreeMeanFun (r • WithLp.ofLp f) v =
      r • G.degreeMeanFun (WithLp.ofLp f) v
    simp only [Graph.degreeMeanFun, Pi.smul_apply, smul_eq_mul]
    have : ∀ w, r * (WithLp.ofLp f) w * Real.sqrt ↑(G.deg w) =
        r * ((WithLp.ofLp f) w * Real.sqrt ↑(G.deg w)) := fun w ↦ by ring
    simp_rw [this, ← Finset.mul_sum]; ring

/-- The degree-weighted mean projection as a continuous linear map on `EuclideanSpace`. -/
def Graph.degreeMeanCLM {n : ℕ} (G : Graph n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  G.degreeMeanLM.toContinuousLinearMap

@[simp]
theorem Graph.degreeMeanCLM_apply {n : ℕ} (G : Graph n)
    (f : EuclideanSpace ℝ (Fin n)) (v : Fin n) :
    G.degreeMeanCLM f v =
      Real.sqrt (G.deg v) * (∑ w, f w * Real.sqrt (G.deg w)) / G.halfs :=
  rfl


/-! **Spectral Gap** -/

/-- The spectral gap of a general graph: `‖N - P‖` where `N` is the normalized
    walk operator and `P` is the projection onto the `√deg` direction.
    Generalizes `spectralGap` for `RegularGraph`. -/
def Graph.spectralGap {n : ℕ} (G : Graph n) : ℝ :=
  ‖G.normalizedWalkCLM - G.degreeMeanCLM‖


/-! **Self-Adjointness** -/

/-- The normalized walk operator is self-adjoint, via the rotation bijection. -/
theorem Graph.normalizedWalkCLM_isSelfAdjoint {n : ℕ} (G : Graph n) :
    IsSelfAdjoint G.normalizedWalkCLM := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  change @inner ℝ _ _ (G.normalizedWalkCLM f) g = @inner ℝ _ _ f (G.normalizedWalkCLM g)
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, normalizedWalkCLM_apply]
  -- Both sides reduce to ∑_e g(src e) · f(target e) / (√deg(src e) · √deg(target e))
  -- via expanding the filtered sums
  sorry

/-- The degree-weighted mean projection is self-adjoint. -/
theorem Graph.degreeMeanCLM_isSelfAdjoint {n : ℕ} (G : Graph n) :
    IsSelfAdjoint G.degreeMeanCLM := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  change @inner ℝ _ _ (G.degreeMeanCLM f) g = @inner ℝ _ _ f (G.degreeMeanCLM g)
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, degreeMeanCLM_apply]
  -- Both sides equal S_g · S_f / halfs where S_x = ∑_v x(v) · √deg(v)
  set sf := ∑ w, (WithLp.ofLp f) w * Real.sqrt ↑(G.deg w)
  set sg := ∑ w, (WithLp.ofLp g) w * Real.sqrt ↑(G.deg w)
  have lhs : ∀ v, (WithLp.ofLp g) v *
      (Real.sqrt ↑(G.deg v) * sf / ↑G.halfs) =
      (WithLp.ofLp g) v * Real.sqrt ↑(G.deg v) * (sf / ↑G.halfs) :=
    fun v ↦ by ring
  have rhs : ∀ v, Real.sqrt ↑(G.deg v) * sg / ↑G.halfs *
      (WithLp.ofLp f) v =
      (WithLp.ofLp f) v * Real.sqrt ↑(G.deg v) * (sg / ↑G.halfs) :=
    fun v ↦ by ring
  simp_rw [lhs, rhs, ← Finset.sum_mul]; ring


/-! **Idempotency and Eigenvector** -/

/-- The degree-weighted mean projection is idempotent: `P² = P`. -/
theorem Graph.degreeMeanCLM_idempotent {n : ℕ} (G : Graph n) :
    G.degreeMeanCLM * G.degreeMeanCLM = G.degreeMeanCLM := by
  sorry

/-- The walk operator preserves the mean projection: `N(Pf) = Pf`. -/
theorem Graph.normalizedWalkCLM_comp_degreeMean {n : ℕ} (G : Graph n) :
    ∀ f : EuclideanSpace ℝ (Fin n),
      G.normalizedWalkCLM (G.degreeMeanCLM f) = G.degreeMeanCLM f := by
  sorry


/-! **Norm Bounds** -/

/-- The normalized walk operator is a contraction: `‖N‖ ≤ 1`. -/
theorem Graph.normalizedWalkCLM_norm_le_one {n : ℕ} (G : Graph n) :
    ‖G.normalizedWalkCLM‖ ≤ 1 := by
  sorry

/-- The spectral gap is nonnegative. -/
theorem Graph.spectralGap_nonneg {n : ℕ} (G : Graph n) :
    0 ≤ G.spectralGap :=
  norm_nonneg _

/-- The spectral gap is at most 1. -/
theorem Graph.spectralGap_le_one {n : ℕ} (G : Graph n) :
    G.spectralGap ≤ 1 := by
  sorry


/-! **Contraction Bound** -/

/-- The spectral gap can only decrease under contraction. -/
theorem Graph.spectralGap_contract {n : ℕ} (G : Graph n) {m : ℕ}
    (s : Fin n → Fin m) :
    (G.contract s).spectralGap ≤ G.spectralGap := by
  sorry


/-! **Regular Graph Compatibility** -/

/-- For a regular graph, `Graph.spectralGap` agrees with `spectralGap`. -/
theorem spectralGap_toGraph {n d : ℕ} (G : RegularGraph n d) :
    G.toGraph.spectralGap = spectralGap G := by
  sorry

end
