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

/-- The inner product `⟨Nf, g⟩` equals a symmetric sum over half-edges.
    Stated with `g * walk` order to match `simp` output of `PiLp.inner_apply`. -/
private theorem Graph.inner_normalizedWalk_eq {n : ℕ} (G : Graph n)
    (f g : Fin n → ℝ) :
    ∑ v, g v *
      (1 / Real.sqrt ↑(G.deg v) *
        ∑ e ∈ univ.filter (G.src · = v), f (G.target e) / Real.sqrt ↑(G.deg (G.target e))) =
    ∑ e : Fin G.halfs,
      f (G.target e) * g (G.src e) /
      (Real.sqrt ↑(G.deg (G.src e)) * Real.sqrt ↑(G.deg (G.target e))) := by
  -- Distribute g(v)/√deg(v) into the filtered sum
  have factor : ∀ v : Fin n,
      g v * (1 / Real.sqrt ↑(G.deg v) *
        ∑ e ∈ univ.filter (G.src · = v), f (G.target e) / Real.sqrt ↑(G.deg (G.target e))) =
      ∑ e ∈ univ.filter (G.src · = v),
        f (G.target e) * g v / (Real.sqrt ↑(G.deg v) * Real.sqrt ↑(G.deg (G.target e))) := by
    intro v
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro e _; ring
  simp_rw [factor]
  -- Collapse: ∑_v ∑_{e:src=v} h(e) = ∑_e h(e) via fiberwise
  rw [← Finset.sum_fiberwise_of_maps_to (g := G.src) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ ↦ Finset.mem_univ _)]
  -- In the fiber where src(e) = v, replace g(v) with g(src e) and √deg(v) with √deg(src e)
  apply Finset.sum_congr rfl; intro e _
  apply Finset.sum_congr rfl; intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [hi]

/-- The normalized walk operator is self-adjoint, via the rotation bijection. -/
theorem Graph.normalizedWalkCLM_isSelfAdjoint {n : ℕ} (G : Graph n) :
    IsSelfAdjoint G.normalizedWalkCLM := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  change @inner ℝ _ _ (G.normalizedWalkCLM f) g = @inner ℝ _ _ f (G.normalizedWalkCLM g)
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, normalizedWalkCLM_apply]
  -- Both sides: ∑_v (something) = half-edge sum via inner_normalizedWalk_eq
  -- LHS has g * (walk applied to f), RHS has f * (walk applied to g)
  -- Commute RHS terms: f(v) * (Ng)(v) → (Ng)(v) * f(v) so inner_normalizedWalk_eq matches
  conv_rhs => arg 2; ext v; rw [mul_comm]
  rw [G.inner_normalizedWalk_eq (WithLp.ofLp f) (WithLp.ofLp g),
      G.inner_normalizedWalk_eq (WithLp.ofLp g) (WithLp.ofLp f)]
  -- LHS: ∑_e f(target e) · g(src e) / (√deg(src) · √deg(target))
  -- RHS: ∑_e g(target e) · f(src e) / (√deg(src) · √deg(target))
  -- Apply rotation bijection: reindex e ↦ rot(e)
  rw [← G.rotEquiv.sum_comp (fun e ↦
    (WithLp.ofLp g) (G.target e) * (WithLp.ofLp f) (G.src e) /
    (Real.sqrt ↑(G.deg (G.src e)) * Real.sqrt ↑(G.deg (G.target e))))]
  -- After reindexing: src(rot e) = target e, rot(rot e) = e
  apply Finset.sum_congr rfl; intro e _
  simp only [Graph.target]
  dsimp [Graph.rotEquiv]
  rw [G.rot_involution]; ring

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

/-- The sum of `√deg(v) * √deg(v)` equals `halfs` (since `√x * √x = x`). -/
theorem Graph.sum_sqrt_deg_sq {n : ℕ} (G : Graph n) :
    ∑ w : Fin n, Real.sqrt ↑(G.deg w) * Real.sqrt ↑(G.deg w) = ↑G.halfs := by
  have h : ∀ w : Fin n, Real.sqrt ↑(G.deg w) * Real.sqrt ↑(G.deg w) = ↑(G.deg w) :=
    fun w ↦ Real.mul_self_sqrt (Nat.cast_nonneg _)
  simp_rw [h, ← Nat.cast_sum]
  exact_mod_cast G.sum_deg

/-- The degree-weighted mean projection is idempotent: `P² = P`. -/
theorem Graph.degreeMeanCLM_idempotent {n : ℕ} (G : Graph n) :
    G.degreeMeanCLM * G.degreeMeanCLM = G.degreeMeanCLM := by
  ext f : 1; apply PiLp.ext; intro v
  show G.degreeMeanCLM (G.degreeMeanCLM f) v = G.degreeMeanCLM f v
  simp only [degreeMeanCLM_apply]
  -- Inner sum: ∑_w (√deg(w) · S / halfs) · √deg(w) = S · (∑ deg) / halfs = S
  set S := ∑ w, f w * Real.sqrt ↑(G.deg w)
  -- Factor: (√deg(w) · S / halfs) · √deg(w) = √deg(w) · √deg(w) · (S / halfs)
  have factor : ∀ w : Fin n, Real.sqrt ↑(G.deg w) * S / ↑G.halfs *
      Real.sqrt ↑(G.deg w) = Real.sqrt ↑(G.deg w) * Real.sqrt ↑(G.deg w) *
      (S / ↑G.halfs) := fun w ↦ by ring
  simp_rw [factor, ← Finset.sum_mul, G.sum_sqrt_deg_sq]
  rcases Nat.eq_zero_or_pos G.halfs with hh | hh
  · simp [hh]
  · have hne : (G.halfs : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [mul_div_cancel₀ S hne]

/-- Any half-edge `e` witnesses that `deg(src e) > 0`. -/
private theorem Graph.deg_src_pos {n : ℕ} (G : Graph n) (e : Fin G.halfs) :
    0 < G.deg (G.src e) :=
  Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

/-- The walk operator preserves the mean projection: `N(Pf) = Pf`. -/
theorem Graph.normalizedWalkCLM_comp_degreeMean {n : ℕ} (G : Graph n) :
    ∀ f : EuclideanSpace ℝ (Fin n),
      G.normalizedWalkCLM (G.degreeMeanCLM f) = G.degreeMeanCLM f := by
  intro f; ext v
  simp only [normalizedWalkCLM_apply, degreeMeanCLM_apply]
  set S := ∑ w, f w * Real.sqrt ↑(G.deg w)
  -- Each summand: (√deg(t) · S / halfs) / √deg(t) = S / halfs
  -- since deg(target e) > 0 for any half-edge e (rot(e) witnesses this)
  have cancel : ∀ e ∈ univ.filter (G.src · = v),
      Real.sqrt ↑(G.deg (G.target e)) * S / ↑G.halfs /
        Real.sqrt ↑(G.deg (G.target e)) = S / ↑G.halfs := by
    intro e _
    have h : Real.sqrt ↑(G.deg (G.target e)) ≠ 0 := by
      rw [Real.sqrt_ne_zero']
      exact Nat.cast_pos.mpr (G.deg_src_pos (G.rot e))
    rw [mul_div_assoc, mul_div_cancel_left₀ _ h]
  rw [Finset.sum_congr rfl cancel, Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
  -- Goal: (1/√deg(v) * ↑card) * (S/halfs) = √deg(v) * S / halfs
  -- card = G.deg v (defeq), so key identity: 1/√d * d = √d
  conv_rhs => rw [mul_div_assoc]
  congr 1
  show 1 / Real.sqrt ↑(G.deg v) * ↑(G.deg v) = Real.sqrt ↑(G.deg v)
  rcases Nat.eq_zero_or_pos (G.deg v) with h | h
  · simp [h]
  · rw [one_div, inv_mul_eq_div, div_eq_iff (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr h))]
    exact (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm


/-! **Norm Bounds** -/

/-- The normalized walk operator is a contraction: `‖N‖ ≤ 1`.
    Proof: Cauchy-Schwarz per vertex + rotation bijection. -/
theorem Graph.normalizedWalkCLM_norm_le_one {n : ℕ} (G : Graph n) :
    ‖G.normalizedWalkCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f; rw [one_mul]
  rw [← Real.sqrt_sq (norm_nonneg (G.normalizedWalkCLM f)),
      ← Real.sqrt_sq (norm_nonneg f)]
  apply Real.sqrt_le_sqrt
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs, normalizedWalkCLM_apply]
  -- ∑_v (Nf(v))² ≤ ∑_v (f v)²
  -- Step 1: Cauchy-Schwarz per vertex: (1/√d · ∑ g)² ≤ ∑ g²
  have per_v : ∀ v : Fin n,
      (1 / Real.sqrt ↑(G.deg v) *
        ∑ e ∈ univ.filter (G.src · = v),
          f (G.target e) / Real.sqrt ↑(G.deg (G.target e))) ^ 2 ≤
      ∑ e ∈ univ.filter (G.src · = v),
        (f (G.target e) / Real.sqrt ↑(G.deg (G.target e))) ^ 2 := by
    intro v
    rcases Nat.eq_zero_or_pos (G.deg v) with h | h
    · have : univ.filter (G.src · = v) = ∅ :=
        Finset.card_eq_zero.mp (show _ = 0 from h ▸ rfl)
      simp [this]
    · have hd : (0 : ℝ) < ↑(G.deg v) := Nat.cast_pos.mpr h
      rw [mul_pow, div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg _),
          one_div, inv_mul_eq_div, div_le_iff₀ hd]
      have cs := @sq_sum_le_card_mul_sum_sq _ ℝ _ _ _ _
        (univ.filter (G.src · = v))
        (fun e ↦ f (G.target e) / Real.sqrt ↑(G.deg (G.target e)))
      rw [show (univ.filter (G.src · = v)).card = G.deg v from rfl] at cs
      linarith
  -- Step 2: Chain: CS per vertex → fiberwise collapse → rotation → fiberwise cancel
  calc ∑ v, _ ≤ ∑ v, ∑ e ∈ univ.filter (G.src · = v),
          (f (G.target e) / Real.sqrt ↑(G.deg (G.target e))) ^ 2 :=
        Finset.sum_le_sum (fun v _ ↦ per_v v)
    _ = ∑ e : Fin G.halfs,
          (f (G.target e) / Real.sqrt ↑(G.deg (G.target e))) ^ 2 := by
        rw [← Finset.sum_fiberwise_of_maps_to (g := G.src) (fun _ _ ↦ mem_univ _)]
    _ = ∑ e : Fin G.halfs,
          (f (G.src e) / Real.sqrt ↑(G.deg (G.src e))) ^ 2 :=
        G.sum_target_eq_sum_src (fun v ↦ (f v / Real.sqrt ↑(G.deg v)) ^ 2)
    _ ≤ ∑ v, f v ^ 2 := by
        rw [← Finset.sum_fiberwise_of_maps_to (g := G.src) (fun _ _ ↦ mem_univ _)]
        apply Finset.sum_le_sum; intro v _
        rw [Finset.sum_congr rfl (fun e he ↦ by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he; rw [he])]
        rw [Finset.sum_const, nsmul_eq_mul,
            show (univ.filter (G.src · = v)).card = G.deg v from rfl,
            div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        rcases Nat.eq_zero_or_pos (G.deg v) with h | h
        · simp [h]; exact sq_nonneg _
        · exact le_of_eq (mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (by omega)))

/-- The spectral gap is nonnegative. -/
theorem Graph.spectralGap_nonneg {n : ℕ} (G : Graph n) :
    0 ≤ G.spectralGap :=
  norm_nonneg _

/-- Subtracting the degree-weighted mean doesn't increase the norm: `‖f - Pf‖ ≤ ‖f‖`. -/
private theorem Graph.norm_sub_degreeMeanCLM_le {n : ℕ} (G : Graph n)
    (f : EuclideanSpace ℝ (Fin n)) :
    ‖f - G.degreeMeanCLM f‖ ≤ ‖f‖ := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg f)]
  apply Real.sqrt_le_sqrt
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs]
  have hfv : ∀ v : Fin n, (f - G.degreeMeanCLM f) v =
      f v - Real.sqrt ↑(G.deg v) * (∑ w, f w * Real.sqrt ↑(G.deg w)) / ↑G.halfs := by
    intro v; simp [degreeMeanCLM_apply]
  simp_rw [hfv]
  set S := ∑ w : Fin n, f w * Real.sqrt ↑(G.deg w)
  have expand : ∀ v : Fin n,
      (f v - Real.sqrt ↑(G.deg v) * S / ↑G.halfs) ^ 2 =
      f v ^ 2 - 2 * (S / ↑G.halfs) * (f v * Real.sqrt ↑(G.deg v)) +
      (S / ↑G.halfs) ^ 2 * (Real.sqrt ↑(G.deg v) * Real.sqrt ↑(G.deg v)) :=
    fun v ↦ by ring
  simp_rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, G.sum_sqrt_deg_sq]
  have key : 2 * (S / ↑G.halfs) * S - (S / ↑G.halfs) ^ 2 * ↑G.halfs ≥ 0 := by
    rcases Nat.eq_zero_or_pos G.halfs with hh | hh
    · simp [hh]
    · have : 2 * (S / ↑G.halfs) * S - (S / ↑G.halfs) ^ 2 * ↑G.halfs =
          S ^ 2 / ↑G.halfs := by
        field_simp; ring
      linarith [div_nonneg (sq_nonneg S) (Nat.cast_nonneg G.halfs)]
  linarith

/-- The spectral gap is at most 1: `‖N - P‖ ≤ 1`.
    Proof: factor `(N-P)f = N(f-Pf)`, then `‖N‖ ≤ 1` and `‖f-Pf‖ ≤ ‖f‖`. -/
theorem Graph.spectralGap_le_one {n : ℕ} (G : Graph n) :
    G.spectralGap ≤ 1 := by
  unfold Graph.spectralGap
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f; rw [one_mul]
  have hNP := G.normalizedWalkCLM_comp_degreeMean f
  calc ‖(G.normalizedWalkCLM - G.degreeMeanCLM) f‖
      = ‖G.normalizedWalkCLM f - G.degreeMeanCLM f‖ := by
        simp [ContinuousLinearMap.sub_apply]
    _ = ‖G.normalizedWalkCLM f - G.normalizedWalkCLM (G.degreeMeanCLM f)‖ := by rw [hNP]
    _ = ‖G.normalizedWalkCLM (f - G.degreeMeanCLM f)‖ := by rw [map_sub]
    _ ≤ ‖G.normalizedWalkCLM‖ * ‖f - G.degreeMeanCLM f‖ := G.normalizedWalkCLM.le_opNorm _
    _ ≤ 1 * ‖f - G.degreeMeanCLM f‖ := by
        apply mul_le_mul_of_nonneg_right G.normalizedWalkCLM_norm_le_one (norm_nonneg _)
    _ = ‖f - G.degreeMeanCLM f‖ := one_mul _
    _ ≤ ‖f‖ := G.norm_sub_degreeMeanCLM_le f


/-! **Contraction Bound** -/

/-- The spectral gap can only decrease under contraction. -/
theorem Graph.spectralGap_contract {n : ℕ} (G : Graph n) {m : ℕ}
    (s : Fin n → Fin m) :
    (G.contract s).spectralGap ≤ G.spectralGap := by
  sorry


/-! **Regular Graph Compatibility** -/

/-- For a regular graph, `Graph.spectralGap` agrees with `spectralGap` (when `d > 0`).
    When `d = 0`, isolated vertices have degree-weighted mean 0 but uniform mean is nonzero. -/
theorem spectralGap_toGraph {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d) :
    G.toGraph.spectralGap = spectralGap G := by
  have hdeg : ∀ w : Fin n, G.toGraph.deg w = d := fun w ↦ G.toGraph_deg hd w
  -- Walk operator: normalizedWalkCLM = walkCLM
  have hw : G.toGraph.normalizedWalkCLM = G.walkCLM := by
    refine ContinuousLinearMap.ext (fun f ↦ ?_); apply PiLp.ext; intro v
    show G.toGraph.normalizedWalkCLM f v = G.walkCLM f v
    simp only [Graph.normalizedWalkCLM_apply, RegularGraph.walkCLM_apply, hdeg]
    -- (1/√d) * ∑_{e:src=v} f(target e) / √d = (∑_i f(nbr v i)) / d
    -- Factor 1/√d out of each summand
    have rw_div : ∀ e ∈ Finset.univ.filter (G.toGraph.src · = v),
        f (G.toGraph.target e) / Real.sqrt ↑d =
        f (G.toGraph.target e) * (1 / Real.sqrt ↑d) := fun e _ ↦ by ring
    rw [Finset.sum_congr rfl rw_div, ← Finset.sum_mul,
      G.toGraph_sum_target hd v (fun w ↦ f w)]
    -- (√d)⁻¹ * (S * (√d)⁻¹) = S / d
    have hsd : Real.sqrt (d : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hd)
    field_simp; rw [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)]; ring
  -- Mean projection: degreeMeanCLM = meanCLM n
  have hm : G.toGraph.degreeMeanCLM = meanCLM n := by
    refine ContinuousLinearMap.ext (fun f ↦ ?_); apply PiLp.ext; intro v
    show G.toGraph.degreeMeanCLM f v = meanCLM n f v
    simp only [Graph.degreeMeanCLM_apply, meanCLM_apply, hdeg, RegularGraph.toGraph_halfs]
    -- √d * (∑_w f(w) * √d) / (n*d) = (∑ f) / n
    rw [← Finset.sum_mul, mul_comm (∑ w, f w) (Real.sqrt ↑d), ← mul_assoc,
      Real.mul_self_sqrt (Nat.cast_nonneg _)]
    push_cast; rw [mul_comm (↑n : ℝ) ↑d, mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr (by omega) : (d : ℝ) ≠ 0)]
  unfold Graph.spectralGap spectralGap; rw [hw, hm]

end
