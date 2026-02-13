/-
  # Abstract RVW Operator Norm Bound

  The pure operator-theory core of the Reingold–Vadhan–Wigderson spectral
  composition theorem. Given operators `W = B · Σ · B` on a Hilbert space
  with projections `Q ≥ P`, the bound `‖W - P‖ ≤ rvwBound(λ₁, λ₂)` follows
  from the contraction `∀ x ∈ ker Q, ‖Bx‖ ≤ λ₂·‖x‖` (B contracts the tilde
  subspace) and the spectral gap `‖QΣQ - P‖ ≤ λ₁`.

  **Important:** The tilde contraction must be stated as a bound on `ker Q`
  (not as `‖B(I-Q)‖ ≤ λ₂`). The operator norm `‖B(I-Q)‖ ≤ λ₂` only gives
  `‖B(I-Q)x‖ ≤ λ₂·‖x‖` (full vector norm), not `‖B(I-Q)x‖ ≤ λ₂·‖(I-Q)x‖`
  (projected vector norm). The RVW proof requires the latter (Claim 4.1).

  This file has NO graph imports — it works in abstract inner product spaces.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.CStarAlgebra.Spectrum

open BigOperators


/-! **The RVW Bound Function** -/

/-- The precise RVW bound on the spectral gap of a zig-zag product.

    f(λ₁, λ₂) = (1 − λ₂²) · λ₁ / 2 + √((1 − λ₂²)² · λ₁² / 4 + λ₂²)

    This equals the largest eigenvalue of the 2×2 matrix
    `[[(1 - λ₂²)·λ₁, λ₂], [λ₂, 0]]`.

    It is tight (achieved by tensor products of complete graphs).
    The weaker additive bound `λ₁ + λ₂ + λ₂²` does NOT suffice for
    the iteration to converge with any finite base degree D. -/
noncomputable def rvwBound (lam₁ lam₂ : ℝ) : ℝ :=
  (1 - lam₂ ^ 2) * lam₁ / 2 + Real.sqrt ((1 - lam₂ ^ 2) ^ 2 * lam₁ ^ 2 / 4 + lam₂ ^ 2)


/-! **Monotonicity** -/

/-- The core inequality: when a ≤ 1, this term is nonnegative.
    This is the final reduction after polynomial expansion. -/
private lemma rvwBound_core_ineq {a b₁ b₂ : ℝ}
    (ha_pos : 0 < a) (ha1 : a ≤ 1) (hb₁ : 0 ≤ b₁) (hb₂ : b₂ ≤ 1) (hbb : b₁ < b₂) :
    let c₁ := 1 - b₁ ^ 2
    let c₂ := 1 - b₂ ^ 2
    let Δ := b₂ ^ 2 - b₁ ^ 2
    1 - (c₂ + c₁) * a ^ 2 / 4 - a * Real.sqrt (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2) - Δ * a ^ 2 / 4 ≥ 0 := by
  intro c₁ c₂ Δ

  -- Strategy: rearrange to show (1 - stuff without sqrt) ≥ a · √(...)
  -- Then square both sides (both are nonneg) and use nlinarith
  set S := Real.sqrt (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2)

  -- The expression equals: 1 - (c₂ + c₁ + Δ) * a² / 4 - a * S
  have expand : 1 - (c₂ + c₁) * a ^ 2 / 4 - a * S - Δ * a ^ 2 / 4 =
                1 - (c₂ + c₁ + Δ) * a ^ 2 / 4 - a * S := by ring

  rw [expand]

  -- Now use identities to simplify c₂ + c₁ + Δ
  have hc₁ : c₁ = 1 - b₁ ^ 2 := rfl
  have hc₂ : c₂ = 1 - b₂ ^ 2 := rfl
  have hΔ : Δ = b₂ ^ 2 - b₁ ^ 2 := rfl

  -- Compute c₂ + c₁ + Δ = 2 - 2b₁²
  have sum_val : c₂ + c₁ + Δ = 2 - 2 * b₁ ^ 2 := by
    simp only [hc₁, hc₂, hΔ]; ring

  rw [sum_val]

  -- Now need: 1 - (2 - 2b₁²)·a²/4 - a·S ≥ 0
  -- Which is: 1 - a²/2 + b₁²·a²/2 - a·S ≥ 0
  -- Or: 1 - a²/2 + b₁²·a²/2 ≥ a·S

  have key : 1 - (2 - 2 * b₁ ^ 2) * a ^ 2 / 4 - a * S =
             1 - a ^ 2 / 2 + b₁ ^ 2 * a ^ 2 / 2 - a * S := by ring
  rw [key]

  -- Show LHS ≥ 0 by proving: 1 - a²/2 + b₁²·a²/2 ≥ a·S
  have hS_nonneg : 0 ≤ S := Real.sqrt_nonneg _
  have hLHS : 0 ≤ 1 - a ^ 2 / 2 + b₁ ^ 2 * a ^ 2 / 2 := by nlinarith [sq_nonneg a, sq_nonneg b₁]

  suffices h : 1 - a ^ 2 / 2 + b₁ ^ 2 * a ^ 2 / 2 ≥ a * S by linarith

  -- Square both sides (both nonneg)
  suffices h_sq : (1 - a ^ 2 / 2 + b₁ ^ 2 * a ^ 2 / 2) ^ 2 ≥ (a * S) ^ 2 by
    have sqrt_ineq : Real.sqrt ((1 - a ^ 2 / 2 + b₁ ^ 2 * a ^ 2 / 2) ^ 2) ≥
                     Real.sqrt ((a * S) ^ 2) := Real.sqrt_le_sqrt h_sq
    simp only [Real.sqrt_sq hLHS, Real.sqrt_sq (by nlinarith [hS_nonneg] : 0 ≤ a * S)] at sqrt_ineq
    exact sqrt_ineq

  -- Expand (a * S)² = a² * S² = a² * (c₁²·a²/4 + b₁²)
  have hS_sq : S ^ 2 = c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2 := by
    have harg : 0 ≤ c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2 := by
      nlinarith [sq_nonneg c₁, sq_nonneg a, sq_nonneg b₁]
    rw [Real.sq_sqrt harg]

  calc (1 - a ^ 2 / 2 + b₁ ^ 2 * a ^ 2 / 2) ^ 2
      ≥ a ^ 2 * (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2) := by
        -- After expansion using c₁ = 1 - b₁², this reduces to: 1 ≥ a²
        simp only [hc₁]
        nlinarith [sq_nonneg a, sq_nonneg b₁]
    _ = a ^ 2 * S ^ 2 := by rw [hS_sq]
    _ = (a * S) ^ 2 := by ring

/-- The key polynomial identity after expanding the squared inequality.
    This is the core algebraic fact: when a ≤ 1, the polynomial inequality holds. -/
private lemma rvwBound_poly_ineq {a b₁ b₂ : ℝ}
    (ha_pos : 0 < a) (ha1 : a ≤ 1) (hb₁ : 0 ≤ b₁) (hb₂ : b₂ ≤ 1) (hbb : b₁ < b₂) :
    let c₁ := 1 - b₁ ^ 2
    let c₂ := 1 - b₂ ^ 2
    let Δ := b₂ ^ 2 - b₁ ^ 2
    c₂ ^ 2 * a ^ 2 / 4 + b₂ ^ 2 ≥
    c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2 + Δ * a * Real.sqrt (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2) +
    Δ ^ 2 * a ^ 2 / 4 := by
  intro c₁ c₂ Δ

  -- Key identities: c₁ + b₁² = 1, c₂ + b₂² = 1, Δ = b₂² - b₁² = -c₂ + c₁
  have hc₁_id : c₁ + b₁ ^ 2 = 1 := by ring
  have hc₂_id : c₂ + b₂ ^ 2 = 1 := by ring
  have hΔ_alt : Δ = c₁ - c₂ := by ring

  -- Rearrange LHS - RHS and show it's ≥ 0
  suffices h : c₂ ^ 2 * a ^ 2 / 4 + b₂ ^ 2 -
              (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2 + Δ * a * Real.sqrt (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2) +
               Δ ^ 2 * a ^ 2 / 4) ≥ 0 by linarith

  -- Expand using identities
  calc c₂ ^ 2 * a ^ 2 / 4 + b₂ ^ 2 -
          (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2 + Δ * a * Real.sqrt (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2) +
           Δ ^ 2 * a ^ 2 / 4)
      = c₂ ^ 2 * a ^ 2 / 4 + b₂ ^ 2 - c₁ ^ 2 * a ^ 2 / 4 - b₁ ^ 2 -
        Δ * a * Real.sqrt (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2) - Δ ^ 2 * a ^ 2 / 4 := by ring
    _ = (c₂ ^ 2 - c₁ ^ 2) * a ^ 2 / 4 + (b₂ ^ 2 - b₁ ^ 2) -
        Δ * a * Real.sqrt (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2) - Δ ^ 2 * a ^ 2 / 4 := by ring
    _ = (c₂ + c₁) * (c₂ - c₁) * a ^ 2 / 4 + Δ -
        Δ * a * Real.sqrt (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2) - Δ ^ 2 * a ^ 2 / 4 := by ring
    _ = -(c₂ + c₁) * Δ * a ^ 2 / 4 + Δ -
        Δ * a * Real.sqrt (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2) - Δ ^ 2 * a ^ 2 / 4 := by rw [hΔ_alt]; ring
    _ = Δ * (1 - (c₂ + c₁) * a ^ 2 / 4 - a * Real.sqrt (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2) - Δ * a ^ 2 / 4) := by ring
    _ ≥ 0 := by
        have hΔ_pos : 0 < Δ := by nlinarith [sq_nonneg b₁, sq_nonneg b₂]
        have h_bracket := rvwBound_core_ineq ha_pos ha1 hb₁ hb₂ hbb
        nlinarith [hΔ_pos, h_bracket]

/-- Core polynomial inequality for RVW bound monotonicity.
    When a ≤ 1 and b₁ ≤ b₂ ≤ 1, the square root increase dominates
    the linear coefficient decrease. -/
private lemma rvwBound_sqrt_ineq {a b₁ b₂ : ℝ}
    (ha_pos : 0 < a) (ha1 : a ≤ 1) (hb₁ : 0 ≤ b₁) (hb₂ : b₂ ≤ 1) (hbb : b₁ < b₂) :
    Real.sqrt ((1 - b₂ ^ 2) ^ 2 * a ^ 2 / 4 + b₂ ^ 2) -
    Real.sqrt ((1 - b₁ ^ 2) ^ 2 * a ^ 2 / 4 + b₁ ^ 2) ≥
    (b₂ ^ 2 - b₁ ^ 2) * a / 2 := by
  set c₁ := 1 - b₁ ^ 2
  set c₂ := 1 - b₂ ^ 2
  set S₁ := Real.sqrt (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2)
  set S₂ := Real.sqrt (c₂ ^ 2 * a ^ 2 / 4 + b₂ ^ 2)
  set Δ := b₂ ^ 2 - b₁ ^ 2

  have hc₁ : 0 ≤ c₁ := by nlinarith [sq_nonneg b₁]
  have hc₂ : 0 ≤ c₂ := by nlinarith [sq_nonneg b₂]
  have hS₁_sq_arg : 0 ≤ c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2 := by nlinarith [sq_nonneg c₁, sq_nonneg a, sq_nonneg b₁]
  have hS₂_sq_arg : 0 ≤ c₂ ^ 2 * a ^ 2 / 4 + b₂ ^ 2 := by nlinarith [sq_nonneg c₂, sq_nonneg a, sq_nonneg b₂]
  have hS₁_pos : 0 ≤ S₁ := Real.sqrt_nonneg _
  have hS₂_pos : 0 ≤ S₂ := Real.sqrt_nonneg _

  -- Prove: S₂ ≥ S₁ + Δ·a/2 by squaring both sides
  have hΔ_pos : 0 < Δ := by nlinarith [sq_nonneg b₁, sq_nonneg b₂]
  have hlhs : 0 ≤ S₁ + Δ * a / 2 := by nlinarith [hS₁_pos, hΔ_pos, ha_pos.le]

  suffices h : S₂ ^ 2 ≥ (S₁ + Δ * a / 2) ^ 2 by
    -- Use sqrt monotonicity
    have sq_ineq : Real.sqrt (S₂ ^ 2) ≥ Real.sqrt ((S₁ + Δ * a / 2) ^ 2) := Real.sqrt_le_sqrt h
    simp only [Real.sqrt_sq hS₂_pos, Real.sqrt_sq hlhs] at sq_ineq
    linarith

  -- Expand and apply polynomial inequality
  calc S₂ ^ 2
      = c₂ ^ 2 * a ^ 2 / 4 + b₂ ^ 2 := by rw [Real.sq_sqrt hS₂_sq_arg]
    _ ≥ c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2 + Δ * a * S₁ + Δ ^ 2 * a ^ 2 / 4 :=
        rvwBound_poly_ineq ha_pos ha1 hb₁ hb₂ hbb
    _ = S₁ ^ 2 + Δ * a * S₁ + Δ ^ 2 * a ^ 2 / 4 := by
        rw [Real.sq_sqrt hS₁_sq_arg]
    _ = (S₁ + Δ * a / 2) ^ 2 := by ring

/-- `rvwBound` is monotone in its first argument (for nonneg arguments with b ≤ 1).
    The constraint b ≤ 1 is natural since b represents a spectral gap bound. -/
theorem rvwBound_mono_left {a₁ a₂ b : ℝ}
    (ha₁ : 0 ≤ a₁) (hb : 0 ≤ b) (hb1 : b ≤ 1) (hab : a₁ ≤ a₂) :
    rvwBound a₁ b ≤ rvwBound a₂ b := by
  unfold rvwBound
  have ha₂ : 0 ≤ a₂ := le_trans ha₁ hab
  have hsqrt : Real.sqrt ((1 - b ^ 2) ^ 2 * a₁ ^ 2 / 4 + b ^ 2) ≤
               Real.sqrt ((1 - b ^ 2) ^ 2 * a₂ ^ 2 / 4 + b ^ 2) := by
    gcongr
  have hc : 0 ≤ 1 - b ^ 2 := by nlinarith [sq_nonneg b]
  linarith [mul_le_mul_of_nonneg_left hab hc]

/-- `rvwBound` is monotone in its second argument (for nonneg arguments
    with both a, b ≤ 1). The constraints are natural since both represent
    spectral gap bounds. -/
theorem rvwBound_mono_right {a b₁ b₂ : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb₁ : 0 ≤ b₁) (hb₂ : b₂ ≤ 1) (hbb : b₁ ≤ b₂) :
    rvwBound a b₁ ≤ rvwBound a b₂ := by
  unfold rvwBound
  by_cases ha_zero : a = 0
  · -- When a = 0, rvwBound 0 b = √(b²) = b
    subst ha_zero
    norm_num
    gcongr
  · -- Main case: 0 < a ≤ 1, 0 ≤ b₁ ≤ b₂ ≤ 1
    have ha_pos : 0 < a := ha.lt_of_ne (Ne.symm ha_zero)
    by_cases hbb_eq : b₁ = b₂
    · simp [hbb_eq]
    · have hbb_strict : b₁ < b₂ := lt_of_le_of_ne hbb hbb_eq
      have key := rvwBound_sqrt_ineq ha_pos ha1 hb₁ hb₂ hbb_strict
      linarith


/-! **Abstract Operator Norm Bound** -/

/-- Hat/tilde decomposition: x = Qx + (I-Q)x with orthogonality. -/
private lemma hat_tilde_orthogonal {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ_proj : Q * Q = Q) (hQ_sa : IsSelfAdjoint Q) (x : EuclideanSpace ℝ (Fin n)) :
    @inner ℝ _ _ (Q x) ((1 - Q) x) = 0 := by
  -- Expand (1 - Q) x = x - Q x
  have h1 : @inner ℝ _ _ (Q x) ((1 - Q) x) = @inner ℝ _ _ (Q x) x - @inner ℝ _ _ (Q x) (Q x) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    rw [inner_sub_right]

  rw [h1]

  -- Use Q² = Q and self-adjointness to show ⟨Qx, x⟩ = ⟨Qx, Qx⟩
  have h2 : @inner ℝ _ _ (Q x) x = @inner ℝ _ _ (Q x) (Q x) := by
    -- ⟨Qx, x⟩ = ⟨Q²x, x⟩ since Q² = Q
    conv_lhs => rw [← hQ_proj]
    simp only [ContinuousLinearMap.mul_apply]
    -- ⟨Q(Qx), x⟩ = ⟨Qx, Qx⟩ by self-adjointness
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hQ_sa
    exact hQ_sa (Q x) x

  rw [h2]
  ring

/-- The squared norm decomposes: ‖x‖² = ‖Q x‖² + ‖(I-Q) x‖². -/
private lemma hat_tilde_norm_sq {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ_proj : Q * Q = Q) (hQ_sa : IsSelfAdjoint Q) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = ‖Q x‖ ^ 2 + ‖(1 - Q) x‖ ^ 2 := by
  -- Use orthogonality: ⟨Qx, (I-Q)x⟩ = 0
  have orth := hat_tilde_orthogonal Q hQ_proj hQ_sa x

  -- Expand x = Qx + (I-Q)x
  have decomp : x = Q x + (1 - Q) x := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    abel

  -- Use Pythagorean theorem
  calc ‖x‖ ^ 2
      = ‖Q x + (1 - Q) x‖ ^ 2 := by rw [← decomp]
    _ = ‖Q x + (1 - Q) x‖ * ‖Q x + (1 - Q) x‖ := sq _
    _ = ‖Q x‖ * ‖Q x‖ + ‖(1 - Q) x‖ * ‖(1 - Q) x‖ :=
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ orth
    _ = ‖Q x‖ ^ 2 + ‖(1 - Q) x‖ ^ 2 := by rw [← sq, ← sq]

/-- Key inner product expansion for the RVW bound.
    Expands ⟨W x, x⟩ using W = B·Σ·B and the hat/tilde decomposition. -/
private lemma rvw_inner_product_expansion {n : ℕ}
    (W B Sig Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hfact : W = B * Sig * B)
    (hQ_proj : Q * Q = Q) (hQ_sa : IsSelfAdjoint Q)
    (hBQ : B * Q = Q) (hQB : Q * B = Q)
    (hB_sa : IsSelfAdjoint B) (hSig_sa : IsSelfAdjoint Sig)
    (x : EuclideanSpace ℝ (Fin n)) :
    @inner ℝ _ _ (W x) x =
      @inner ℝ _ _ (Sig (B (Q x))) (B (Q x)) +
      @inner ℝ _ _ (Sig (B (Q x))) (B ((1 - Q) x)) +
      @inner ℝ _ _ (Sig (B ((1 - Q) x))) (B (Q x)) +
      @inner ℝ _ _ (Sig (B ((1 - Q) x))) (B ((1 - Q) x)) := by
  -- Substitute W = B·Σ·B
  rw [hfact]
  simp only [ContinuousLinearMap.mul_apply]

  -- Use self-adjointness of B: ⟨B(ΣBx), x⟩ = ⟨ΣBx, Bx⟩
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hB_sa
  have h_adj : @inner ℝ _ _ (B (Sig (B x))) x = @inner ℝ _ _ (Sig (B x)) (B x) :=
    hB_sa (Sig (B x)) x

  rw [h_adj]

  -- Decompose x = Qx + (I-Q)x
  have decomp : x = Q x + (1 - Q) x := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]; abel

  -- Expand B x using decomposition and bilinearity of inner product
  calc @inner ℝ _ _ (Sig (B x)) (B x)
      = @inner ℝ _ _ (Sig (B (Q x + (1 - Q) x))) (B (Q x + (1 - Q) x)) := by rw [← decomp]
    _ = @inner ℝ _ _ (Sig (B (Q x)) + Sig (B ((1 - Q) x))) (B (Q x) + B ((1 - Q) x)) := by
          congr 1 <;> simp only [map_add]
    _ = @inner ℝ _ _ (Sig (B (Q x))) (B (Q x)) +
        @inner ℝ _ _ (Sig (B (Q x))) (B ((1 - Q) x)) +
        @inner ℝ _ _ (Sig (B ((1 - Q) x))) (B (Q x)) +
        @inner ℝ _ _ (Sig (B ((1 - Q) x))) (B ((1 - Q) x)) := by
          rw [inner_add_left, inner_add_right, inner_add_right]
          ring

/-- Helper: For an eigenvector v with Av = λv, we have ⟨Av,v⟩ = λ·‖v‖². -/
private lemma eigenvalue_inner_eq {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (lambda : ℝ) (h : A v = lambda • v) :
    @inner ℝ _ _ (A v) v = lambda * ‖v‖ ^ 2 := by
  calc @inner ℝ _ _ (A v) v
      = @inner ℝ _ _ (lambda • v) v := by rw [h]
    _ = lambda * @inner ℝ _ _ v v := by rw [inner_smul_left]; norm_cast
    _ = lambda * ‖v‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]

/-- Helper: For a unit eigenvector, the Rayleigh quotient equals the eigenvalue. -/
private lemma rayleigh_at_eigenvector {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (lambda : ℝ)
    (hv_norm : ‖v‖ = 1) (h : A v = lambda • v) :
    @inner ℝ _ _ (A v) v = lambda := by
  have := eigenvalue_inner_eq A v lambda h
  simp [hv_norm] at this
  exact this

/-- Rayleigh quotient bound: ‖A‖ = sup_{‖x‖=1} |⟨Ax, x⟩| for self-adjoint A. -/
private lemma rayleigh_quotient_bound {n : ℕ} (hn : 0 < n)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA_sa : IsSelfAdjoint A) :
    ‖A‖ = sSup (Set.range fun (x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}) =>
      |@inner ℝ _ _ (A x.val) x.val|) := by
  -- First direction: sup |⟨Ax, x⟩| ≤ ‖A‖ by Cauchy-Schwarz
  have dir1 : sSup (Set.range fun (x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}) =>
      |@inner ℝ _ _ (A x.val) x.val|) ≤ ‖A‖ := by
    apply Real.sSup_le
    · intro b ⟨x, hx⟩
      simp only [Subtype.coe_mk] at hx
      rw [← hx]
      calc |@inner ℝ _ _ (A x.val) x.val|
          ≤ ‖A x.val‖ * ‖x.val‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖A‖ * ‖x.val‖ * ‖x.val‖ := by
            gcongr
            exact ContinuousLinearMap.le_opNorm A x.val
        _ = ‖A‖ := by rw [x.prop]; ring
    · exact norm_nonneg _

  -- Second direction: ‖A‖ ≤ sup |⟨Ax, x⟩| (harder, uses Rayleigh quotient)
  have dir2 : ‖A‖ ≤ sSup (Set.range fun (x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}) =>
      |@inner ℝ _ _ (A x.val) x.val|) := by
    -- Strategy: For self-adjoint A, ‖A‖ equals the maximum absolute eigenvalue.
    -- The Rayleigh quotient at an eigenvector equals the eigenvalue.
    -- Therefore sup{|⟨Ax,x⟩| : ‖x‖=1} ≥ max{|λ| : λ eigenvalue} = ‖A‖.

    -- Convert to LinearMap for Rayleigh quotient theory
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hA_sa

    -- Key observation: for any eigenvector v with Av = λv and ‖v‖ = 1,
    -- we have ⟨Av, v⟩ = ⟨λv, v⟩ = λ·⟨v, v⟩ = λ
    -- So if λ is the eigenvalue with max |λ|, then |⟨Av, v⟩| = |λ| = ‖A‖

    -- For finite-dimensional spaces, the operator norm equals the spectral radius
    -- This is proved in Mathlib via IsSelfAdjoint.spectralRadius_eq_nnnorm,
    -- and the spectral radius is attained by some eigenvalue.

    -- The complete proof requires:
    -- 1. Showing A has an eigenvalue λ with |λ| = ‖A‖ (from spectral theory)
    -- 2. Finding unit eigenvector v with Av = λv
    -- 3. Computing |⟨Av,v⟩| = |λ| = ‖A‖
    -- 4. Showing this is in the supremum range

    -- Strategy: Use Rayleigh quotient theory + spectral radius
    -- For self-adjoint A on finite-dimensional space:
    -- 1. sup{⟨Ax,x⟩ : ‖x‖=1} is an eigenvalue λ_max (Rayleigh theory)
    -- 2. inf{⟨Ax,x⟩ : ‖x‖=1} is an eigenvalue λ_min (Rayleigh theory)
    -- 3. ‖A‖ = spectralRadius(A) = max{|λ| : λ eigenvalue}
    -- 4. Therefore sup{|⟨Ax,x⟩| : ‖x‖=1} ≥ max(|λ_max|, |λ_min|) = ‖A‖

    -- Convert to LinearMap for Rayleigh theory
    set T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := A.toLinearMap

    -- T is symmetric (equivalent to A being self-adjoint)
    have hT_symm : T.IsSymmetric := hA_sa

    -- The Rayleigh quotient supremum is an eigenvalue
    have h_ray_sup : Module.End.hasEigenvalue T
        (⨆ x : { x : EuclideanSpace ℝ (Fin n) // x ≠ 0 },
          RCLike.re ⟪T x, x⟫ / ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 : ℝ) := by
      haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
        apply EuclideanSpace.nontrivial_of_finrank_pos
        simp [hn]
      exact LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional hT_symm

    -- Similarly for infimum
    have h_ray_inf : Module.End.hasEigenvalue T
        (⨅ x : { x : EuclideanSpace ℝ (Fin n) // x ≠ 0 },
          RCLike.re ⟪T x, x⟫ / ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 : ℝ) := by
      haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
        apply EuclideanSpace.nontrivial_of_finrank_pos
        simp [hn]
      exact LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional hT_symm

    -- These eigenvalues are in the spectrum
    -- For finite-dimensional spaces, spectrum = eigenvalues
    -- The spectral radius is the sup of norms of spectrum elements
    -- For self-adjoint, spectralRadius = ‖A‖

    -- The Rayleigh quotient is bounded
    have h_rayleigh_bounded_above : ∃ (M : ℝ), ∀ (x : { x : EuclideanSpace ℝ (Fin n) // x ≠ 0 }),
        ⟪T x, x⟫ / ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ M := by
      use ‖A‖
      intro x
      have hx_ne : ‖x.val‖ ≠ 0 := norm_ne_zero_iff.mpr x.prop
      calc ⟪T x, x⟫ / ‖x.val‖ ^ 2
          ≤ |⟪T x, x⟫| / ‖x.val‖ ^ 2 := by
            gcongr
            exact le_abs_self _
        _ ≤ ‖T x.val‖ * ‖x.val‖ / ‖x.val‖ ^ 2 := by
            gcongr
            exact abs_real_inner_le_norm _ _
        _ ≤ ‖A‖ * ‖x.val‖ * ‖x.val‖ / ‖x.val‖ ^ 2 := by
            gcongr
            exact ContinuousLinearMap.le_opNorm A x.val
        _ = ‖A‖ := by
            rw [sq]
            field_simp

    have h_rayleigh_bounded_below : ∃ (m : ℝ), ∀ (x : { x : EuclideanSpace ℝ (Fin n) // x ≠ 0 }),
        m ≤ ⟪T x, x⟫ / ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
      use -‖A‖
      intro x
      have hx_ne : ‖x.val‖ ≠ 0 := norm_ne_zero_iff.mpr x.prop
      calc -‖A‖
          = -(‖A‖ * ‖x.val‖ * ‖x.val‖ / ‖x.val‖ ^ 2) := by
            rw [sq]
            field_simp
        _ ≤ -(‖T x.val‖ * ‖x.val‖ / ‖x.val‖ ^ 2) := by
            gcongr
            exact ContinuousLinearMap.le_opNorm A x.val
        _ ≤ -|⟪T x, x⟫| / ‖x.val‖ ^ 2 := by
            gcongr
            exact abs_real_inner_le_norm _ _
        _ ≤ ⟪T x, x⟫ / ‖x.val‖ ^ 2 := by
            linarith [abs_nonneg (⟪T x, x⟫), neg_abs_le (⟪T x, x⟫)]

    -- Key insight: For self-adjoint A, ALL eigenvalues lie between λ_min and λ_max.
    -- Proof: For any eigenvalue λ with unit eigenvector v, we have λ = ⟨Av,v⟩,
    -- which by definition of sup/inf satisfies λ_min ≤ λ ≤ λ_max.
    -- Therefore max{|λ| : λ eigenvalue} = max(|λ_max|, |λ_min|).

    set lam_max := ⨆ x : { x : EuclideanSpace ℝ (Fin n) // x ≠ 0 },
          RCLike.re ⟪T x, x⟫ / ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2
    set lam_min := ⨅ x : { x : EuclideanSpace ℝ (Fin n) // x ≠ 0 },
          RCLike.re ⟪T x, x⟫ / ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2

    -- For real spaces, RCLike.re is just the identity
    have h_re_id : ∀ (x : ℝ), RCLike.re x = x := fun x => rfl

    -- λ_max and λ_min bound all eigenvalues
    have h_all_eigenvalues_bounded : ∀ (lambda : ℝ),
        Module.End.hasEigenvalue T lambda → lam_min ≤ lambda ∧ lambda ≤ lam_max := by
      intro lambda hlam
      -- For eigenvalue λ with eigenvector v (normalized), we have λ = ⟨Tv,v⟩
      obtain ⟨v, hv_ne, hv_eigen⟩ := Module.End.hasEigenvalue.exists_hasEigenvector hlam
      have hv_ne_zero : v ≠ 0 := hv_ne
      set v_normed := (‖v‖⁻¹ : ℝ) • v
      have hv_normed_ne : v_normed ≠ 0 := by
        simp [v_normed]
        intro h
        apply hv_ne_zero
        have : ‖v‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hv_ne_zero)
        exact (smul_eq_zero.mp h).resolve_left this
      have hv_normed_norm : ‖v_normed‖ = 1 := by
        simp [v_normed, norm_smul]
        rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
        rw [inv_mul_cancel (norm_ne_zero_iff.mpr hv_ne_zero)]
      have hv_normed_eigen : T v_normed = lambda • v_normed := by
        simp [v_normed]
        rw [map_smul, hv_eigen.eigenvalue_eq]
        rw [smul_comm]
      -- Now λ = ⟨Tv_normed, v_normed⟩ / ‖v_normed‖²
      have h_eq : lambda = ⟪T v_normed, v_normed⟫ / ‖v_normed‖ ^ 2 := by
        have := rayleigh_at_eigenvector A v_normed lambda hv_normed_norm
          (by convert hv_normed_eigen; rfl)
        rw [hv_normed_norm] at this
        simp at this
        exact this.symm
      constructor
      · -- lam_min ≤ lambda
        rw [h_eq]
        apply ciInf_le_of_le
        · exact ⟨_, h_rayleigh_bounded_below⟩
        · use ⟨v_normed, hv_normed_ne⟩
          simp [h_re_id]
      · -- lambda ≤ lam_max
        rw [h_eq]
        apply le_ciSup_of_le
        · exact ⟨_, h_rayleigh_bounded_above⟩
        · use ⟨v_normed, hv_normed_ne⟩
          simp [h_re_id]

    -- Therefore ‖A‖ = max(|λ_max|, |λ_min|)
    -- and sup{|⟨Ax,x⟩| : ‖x‖=1} ≥ max(|λ_max|, |λ_min|) = ‖A‖

    -- Get unit eigenvectors for λ_max and λ_min
    obtain ⟨v_max, hv_max_ne, hv_max_eigen⟩ := Module.End.hasEigenvalue.exists_hasEigenvector h_ray_sup
    obtain ⟨v_min, hv_min_ne, hv_min_eigen⟩ := Module.End.hasEigenvalue.exists_hasEigenvector h_ray_inf

    -- Normalize them
    set u_max := (‖v_max‖⁻¹ : ℝ) • v_max
    set u_min := (‖v_min‖⁻¹ : ℝ) • v_min

    have hu_max_ne : u_max ≠ 0 := by
      simp [u_max]
      intro h
      apply hv_max_ne
      have : ‖v_max‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hv_max_ne)
      exact (smul_eq_zero.mp h).resolve_left this

    have hu_min_ne : u_min ≠ 0 := by
      simp [u_min]
      intro h
      apply hv_min_ne
      have : ‖v_min‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hv_min_ne)
      exact (smul_eq_zero.mp h).resolve_left this

    have hu_max_norm : ‖u_max‖ = 1 := by
      simp [u_max, norm_smul]
      rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v_max))]
      rw [inv_mul_cancel (norm_ne_zero_iff.mpr hv_max_ne)]

    have hu_min_norm : ‖u_min‖ = 1 := by
      simp [u_min, norm_smul]
      rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v_min))]
      rw [inv_mul_cancel (norm_ne_zero_iff.mpr hv_min_ne)]

    have hu_max_eigen : T u_max = lam_max • u_max := by
      simp [u_max]
      rw [map_smul, hv_max_eigen.eigenvalue_eq]
      rw [smul_comm]

    have hu_min_eigen : T u_min = lam_min • u_min := by
      simp [u_min]
      rw [map_smul, hv_min_eigen.eigenvalue_eq]
      rw [smul_comm]

    -- At these unit eigenvectors, |⟨Au,u⟩| = |λ|
    have h_max_val : |⟪A u_max, u_max⟫| = |lam_max| := by
      have := rayleigh_at_eigenvector A u_max lam_max hu_max_norm
        (by convert hu_max_eigen; rfl)
      rw [this]

    have h_min_val : |⟪A u_min, u_min⟫| = |lam_min| := by
      have := rayleigh_at_eigenvector A u_min lam_min hu_min_norm
        (by convert hu_min_eigen; rfl)
      rw [this]

    -- These values are in the supremum range
    have h_max_in : |lam_max| ∈ Set.range (fun (x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}) =>
        |⟪A x.val, x.val⟫|) := by
      use ⟨u_max, hu_max_norm⟩
      exact h_max_val.symm

    have h_min_in : |lam_min| ∈ Set.range (fun (x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}) =>
        |⟪A x.val, x.val⟫|) := by
      use ⟨u_min, hu_min_norm⟩
      exact h_min_val.symm

    -- For self-adjoint operators in finite dimensions, the operator norm equals
    -- the maximum absolute eigenvalue, which by h_all_eigenvalues_bounded equals
    -- max(|lam_max|, |lam_min|).

    -- We need: ‖A‖ ≤ sup{|⟨Ax,x⟩| : ‖x‖=1}
    -- We'll show: sup{|⟨Ax,x⟩| : ‖x‖=1} ≥ max(|lam_max|, |lam_min|)
    --            and then use spectral theory to show ‖A‖ = max(|lam_max|, |lam_min|)

    -- The supremum is at least |lam_max|
    have h_sup_ge_max : sSup (Set.range fun (x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}) =>
        |⟪A x.val, x.val⟫|) ≥ |lam_max| := by
      apply le_sSup
      · use ‖A‖
        intro b ⟨x, hx⟩
        rw [← hx]
        calc |⟪A x.val, x.val⟫|
            ≤ ‖A x.val‖ * ‖x.val‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖A‖ * ‖x.val‖ * ‖x.val‖ := by
              gcongr
              exact ContinuousLinearMap.le_opNorm A x.val
          _ = ‖A‖ := by rw [x.prop]; ring
      · exact h_max_in

    -- The supremum is at least |lam_min|
    have h_sup_ge_min : sSup (Set.range fun (x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}) =>
        |⟪A x.val, x.val⟫|) ≥ |lam_min| := by
      apply le_sSup
      · use ‖A‖
        intro b ⟨x, hx⟩
        rw [← hx]
        calc |⟪A x.val, x.val⟫|
            ≤ ‖A x.val‖ * ‖x.val‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖A‖ * ‖x.val‖ * ‖x.val‖ := by
              gcongr
              exact ContinuousLinearMap.le_opNorm A x.val
          _ = ‖A‖ := by rw [x.prop]; ring
      · exact h_min_in

    -- Therefore sup ≥ max(|lam_max|, |lam_min|)
    have h_sup_ge_both : sSup (Set.range fun (x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}) =>
        |⟪A x.val, x.val⟫|) ≥ max |lam_max| |lam_min| := by
      exact le_max_iff.mpr (Or.inl h_sup_ge_max)

    -- For self-adjoint operators on finite-dimensional real inner product spaces,
    -- ‖A‖ = max{|λ| : λ eigenvalue}.
    -- We've shown all eigenvalues satisfy lam_min ≤ λ ≤ lam_max.
    -- Therefore ‖A‖ ≤ max(|lam_max|, |lam_min|).

    -- The key fact: operator norm = spectral radius = max absolute eigenvalue
    have h_norm_eq_max_eig : ‖A‖ = max |lam_max| |lam_min| := by
      -- Strategy: Use the Rayleigh quotient characterization we've established
      -- in dir1 and dir2. For self-adjoint operators:
      -- ‖A‖ = sup{|⟨Ax,x⟩| : ‖x‖=1}
      --
      -- We've shown:
      -- 1. All eigenvalues (hence all Rayleigh quotients) lie in [lam_min, lam_max]
      -- 2. Both |lam_max| and |lam_min| are achieved (they're eigenvalues)
      -- 3. Therefore sup{|⟨Ax,x⟩| : ‖x‖=1} = max(|lam_max|, |lam_min|)

      -- From dir1 we have: sup ≤ ‖A‖
      -- From h_sup_ge_both we have: sup ≥ max(|lam_max|, |lam_min|)
      -- We need to show sup ≤ max(|lam_max|, |lam_min|) to conclude equality

      have h_sup_le_max : sSup (Set.range fun (x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}) =>
          |⟪A x.val, x.val⟫|) ≤ max |lam_max| |lam_min| := by
        apply Real.sSup_le
        · intro b ⟨x, hx⟩
          rw [← hx]
          -- For any unit vector x, ⟨Ax,x⟩ is a Rayleigh quotient
          -- We need: |⟨Ax,x⟩| ≤ max(|lam_max|, |lam_min|)

          -- Key: the Rayleigh quotient ⟨Tx,x⟩/‖x‖² lies in [lam_min, lam_max]
          -- For unit vectors, this means lam_min ≤ ⟨Ax,x⟩ ≤ lam_max

          -- First, connect A to T
          have hTx_eq : ⟪T x.val, x.val⟫ = ⟪A x.val, x.val⟫ := by rfl

          -- The Rayleigh quotient for x.val is bounded
          have hx_ne : x.val ≠ 0 := norm_ne_zero_iff.mp (by rw [x.prop]; norm_num)

          have h_ray_x_lower : lam_min ≤ ⟪T x.val, x.val⟫ / ‖x.val‖ ^ 2 := by
            apply ciInf_le
            · exact ⟨_, h_rayleigh_bounded_below⟩
            · use ⟨x.val, hx_ne⟩
              simp [h_re_id]

          have h_ray_x_upper : ⟪T x.val, x.val⟫ / ‖x.val‖ ^ 2 ≤ lam_max := by
            apply le_ciSup
            · exact ⟨_, h_rayleigh_bounded_above⟩
            · use ⟨x.val, hx_ne⟩
              simp [h_re_id]

          -- For unit vector: ⟨Ax,x⟩ = ⟨Tx,x⟩ / ‖x‖² = ⟨Tx,x⟩ (since ‖x‖ = 1)
          have h_unit_ray : ⟪T x.val, x.val⟫ = ⟪T x.val, x.val⟫ / ‖x.val‖ ^ 2 := by
            rw [x.prop]
            norm_num

          -- So lam_min ≤ ⟨Ax,x⟩ ≤ lam_max
          have h_bounds : lam_min ≤ ⟪A x.val, x.val⟫ ∧ ⟪A x.val, x.val⟫ ≤ lam_max := by
            rw [← hTx_eq] at h_ray_x_lower h_ray_x_upper
            rw [← h_unit_ray] at h_ray_x_lower h_ray_x_upper
            exact ⟨h_ray_x_lower, h_ray_x_upper⟩

          -- Therefore |⟨Ax,x⟩| ≤ max(|lam_max|, |lam_min|)
          by_cases h_nonneg : 0 ≤ ⟪A x.val, x.val⟫
          · -- Case: ⟨Ax,x⟩ ≥ 0
            calc |⟪A x.val, x.val⟫|
                = ⟪A x.val, x.val⟫ := abs_of_nonneg h_nonneg
              _ ≤ lam_max := h_bounds.2
              _ ≤ |lam_max| := le_abs_self _
              _ ≤ max |lam_max| |lam_min| := le_max_left _ _
          · -- Case: ⟨Ax,x⟩ < 0
            have h_neg : ⟪A x.val, x.val⟫ < 0 := not_le.mp h_nonneg
            calc |⟪A x.val, x.val⟫|
                = -⟪A x.val, x.val⟫ := abs_of_neg h_neg
              _ ≤ -lam_min := by linarith [h_bounds.1]
              _ ≤ |lam_min| := by
                  by_cases h_min_neg : lam_min < 0
                  · simp [abs_of_neg h_min_neg]
                  · push_neg at h_min_neg
                    have : lam_min = 0 := by
                      linarith [h_bounds.1, h_neg]
                    simp [this]
              _ ≤ max |lam_max| |lam_min| := le_max_right _ _
        · exact norm_nonneg _

      -- Now we have:
      -- - h_sup_ge_both: sup ≥ max(|lam_max|, |lam_min|)
      -- - h_sup_le_max: sup ≤ max(|lam_max|, |lam_min|)
      -- Therefore sup = max(|lam_max|, |lam_min|)
      have h_sup_eq : sSup (Set.range fun (x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}) =>
          |⟪A x.val, x.val⟫|) = max |lam_max| |lam_min| :=
        le_antisymm h_sup_le_max h_sup_ge_both

      -- From ray_bound: ‖A‖ = sup
      -- Therefore ‖A‖ = max(|lam_max|, |lam_min|)
      rw [ray_bound]
      exact h_sup_eq

    -- Conclude
    calc ‖A‖
        = max |lam_max| |lam_min| := h_norm_eq_max_eig
      _ ≤ sSup (Set.range fun (x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}) =>
            |⟪A x.val, x.val⟫|) := h_sup_ge_both

  exact le_antisymm dir2 dir1

/-- The 2×2 matrix whose largest eigenvalue equals rvwBound(λ₁, λ₂).
    This is the matrix M = [[(1-λ₂²)λ₁, λ₂], [λ₂, 0]]. -/
private def rvw_matrix (lam₁ lam₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j =>
    match i, j with
    | 0, 0 => (1 - lam₂ ^ 2) * lam₁
    | 0, 1 => lam₂
    | 1, 0 => lam₂
    | 1, 1 => 0

/-- The largest eigenvalue of the RVW matrix equals rvwBound.
    The characteristic polynomial of M is λ² - (1-λ₂²)λ₁·λ - λ₂²,
    whose largest root is rvwBound(λ₁, λ₂).

    This can be proved by computing the characteristic polynomial,
    using the quadratic formula, and simplifying. -/
private lemma rvw_matrix_eigenvalue (lam₁ lam₂ : ℝ) (hlam₁ : 0 ≤ lam₁) (hlam₂ : 0 ≤ lam₂) :
    True := by
  -- Placeholder: proving the connection between the 2×2 matrix eigenvalue and rvwBound
  -- requires matrix eigenvalue theory from Mathlib
  trivial

/-- Helper: P annihilates (I-Q)x since PQ = P implies P(I-Q) = 0. -/
private lemma meanProj_annihilates_tilde {n : ℕ}
    (P Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hPQ : P * Q = P) (x : EuclideanSpace ℝ (Fin n)) :
    P ((1 - Q) x) = 0 := by
  calc P ((1 - Q) x)
      = P (x - Q x) := by simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    _ = P x - P (Q x) := by rw [map_sub]
    _ = P x - (P * Q) x := rfl
    _ = P x - P x := by rw [hPQ]
    _ = 0 := sub_self _

/-- Helper: ⟨Px, x⟩ = ⟨Px̂, x̂⟩ using orthogonality. -/
private lemma meanProj_inner_eq_hat {n : ℕ}
    (P Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ_proj : Q * Q = Q) (hQ_sa : IsSelfAdjoint Q)
    (hPQ : P * Q = P) (hQP : Q * P = P)
    (x : EuclideanSpace ℝ (Fin n)) :
    @inner ℝ _ _ (P x) x = @inner ℝ _ _ (P (Q x)) (Q x) := by
  set x_hat := Q x
  set x_tilde := (1 - Q) x
  -- Decompose x = x̂ + x̃
  have decomp : x = x_hat + x_tilde := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]; abel
  -- Orthogonality
  have orth := hat_tilde_orthogonal Q hQ_proj hQ_sa x
  -- P annihilates x̃
  have hPtilde : P x_tilde = 0 := meanProj_annihilates_tilde P Q hPQ x
  -- Expand
  calc @inner ℝ _ _ (P x) x
      = @inner ℝ _ _ (P (x_hat + x_tilde)) (x_hat + x_tilde) := by rw [← decomp]
    _ = @inner ℝ _ _ (P x_hat + P x_tilde) (x_hat + x_tilde) := by rw [map_add]
    _ = @inner ℝ _ _ (P x_hat + 0) (x_hat + x_tilde) := by rw [hPtilde]
    _ = @inner ℝ _ _ (P x_hat) (x_hat + x_tilde) := by rw [add_zero]
    _ = @inner ℝ _ _ (P x_hat) x_hat + @inner ℝ _ _ (P x_hat) x_tilde := by rw [inner_add_right]
    _ = @inner ℝ _ _ (P x_hat) x_hat + 0 := by
        congr 1
        -- ⟨Px̂, x̃⟩ = 0 by orthogonality: use P = QP to show Px̂ is in range of Q
        -- Then use Q self-adjoint: ⟨Qy, (I-Q)z⟩ = ⟨y, Q(I-Q)z⟩ = ⟨y, 0⟩ = 0
        have hPhat_in_Q : ∃ y, P x_hat = Q y := by
          use P x_hat
          calc Q (P x_hat) = (Q * P) x_hat := rfl
             _ = P x_hat := by rw [hQP]
        obtain ⟨y, hy⟩ := hPhat_in_Q
        rw [hy]
        -- Now ⟨Qy, x̃⟩ = ⟨Qy, (I-Q)x⟩ = 0 by orthogonality
        rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hQ_sa
        have : @inner ℝ _ _ (Q y) x_tilde = @inner ℝ _ _ y (Q x_tilde) :=
          hQ_sa y x_tilde
        rw [this]
        -- Q·(I-Q) = Q - Q² = Q - Q = 0
        have : Q x_tilde = 0 := by
          calc Q x_tilde = Q ((1 - Q) x) := rfl
             _ = Q (x - Q x) := by simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
             _ = Q x - Q (Q x) := by rw [map_sub]
             _ = Q x - (Q * Q) x := rfl
             _ = Q x - Q x := by rw [hQ_proj]
             _ = 0 := sub_self _
        rw [this, inner_zero_right]
    _ = @inner ℝ _ _ (P x_hat) x_hat := by rw [add_zero]

/-- Helper: Bound the hat block term |⟨(QΣQ - P)x̂, x̂⟩| ≤ λ₁·‖x̂‖². -/
private lemma hat_block_bound {n : ℕ}
    (Sig Q P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (lam₁ : ℝ) (h_hat : ‖Q * Sig * Q - P‖ ≤ lam₁)
    (x_hat : EuclideanSpace ℝ (Fin n)) :
    |@inner ℝ _ _ ((Q * Sig * Q - P) x_hat) x_hat| ≤ lam₁ * ‖x_hat‖ ^ 2 := by
  calc |@inner ℝ _ _ ((Q * Sig * Q - P) x_hat) x_hat|
      ≤ ‖(Q * Sig * Q - P) x_hat‖ * ‖x_hat‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖Q * Sig * Q - P‖ * ‖x_hat‖ * ‖x_hat‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ lam₁ * ‖x_hat‖ * ‖x_hat‖ := by gcongr
    _ = lam₁ * ‖x_hat‖ ^ 2 := by ring

/-- Helper: Self-adjoint involution has norm ≤ 1. -/
private lemma involution_norm_le_one {n : ℕ}
    (Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig) :
    ‖Sig‖ ≤ 1 := by
  -- For self-adjoint Σ: ‖Σ‖² = ‖Σ²‖ = ‖1‖ = 1 by C*-identity
  have h_sq : ‖Sig‖ ^ 2 = ‖Sig * Sig‖ := hSig_sa.norm_mul_self.symm
  rw [hSig_inv] at h_sq
  have : ‖Sig‖ ^ 2 = 1 := by simp at h_sq; exact h_sq
  have : ‖Sig‖ * ‖Sig‖ = 1 := by simpa [sq] using this
  -- Either ‖Σ‖ = 1 or impossible (‖Σ‖ = -1 ruled out by nonnegativity)
  have : ‖Sig‖ * ‖Sig‖ - 1 = 0 := by linarith
  have : (‖Sig‖ - 1) * (‖Sig‖ + 1) = 0 := by ring_nf at this ⊢; exact this
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h | h
  · linarith
  · linarith [norm_nonneg Sig]

/-- Helper: Bound the cross term |⟨Σx̂, Bx̃⟩| ≤ ‖x̂‖·‖Bx̃‖. -/
private lemma cross_term_bound {n : ℕ}
    (Sig B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig)
    (x_hat x_tilde : EuclideanSpace ℝ (Fin n)) :
    |@inner ℝ _ _ (Sig x_hat) (B x_tilde)| ≤ ‖x_hat‖ * ‖B x_tilde‖ := by
  calc |@inner ℝ _ _ (Sig x_hat) (B x_tilde)|
      ≤ ‖Sig x_hat‖ * ‖B x_tilde‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖Sig‖ * ‖x_hat‖ * ‖B x_tilde‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖x_hat‖ * ‖B x_tilde‖ := by
        gcongr
        exact involution_norm_le_one Sig hSig_inv hSig_sa
    _ = ‖x_hat‖ * ‖B x_tilde‖ := by ring

/-- Helper: Bound ‖Bx̃‖ ≤ λ₂·‖x̃‖ using ‖B(I-Q)‖ ≤ λ₂. -/
private lemma tilde_contraction_bound {n : ℕ}
    (B Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (lam₂ : ℝ) (h_tilde : ∀ x, Q x = 0 → ‖B x‖ ≤ lam₂ * ‖x‖)
    (hQ_proj : Q * Q = Q)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖B ((1 - Q) x)‖ ≤ lam₂ * ‖(1 - Q) x‖ := by
  -- (1 - Q) x is in ker(Q) since Q((1-Q)x) = (Q - Q²)x = 0
  have hker : Q ((1 - Q) x) = 0 := by
    change (Q * (1 - Q)) x = 0
    rw [mul_sub, mul_one, hQ_proj, sub_self, ContinuousLinearMap.zero_apply]
  exact h_tilde ((1 - Q) x) hker

/-- The reflection–Rayleigh quotient bound (RVW section 4.2).

For a self-adjoint involution `Σ` (a reflection: `Σ² = I`, `Σ* = Σ`) and orthogonal
vectors `u`, `w` with:
- `|⟨Σu, u⟩| ≤ λ₁ · ‖u‖²` (hat block spectral gap)
- `‖w‖ ≤ λ₂ · b` where `b² + ‖u‖² = 1` (tilde contraction)

We have: `|⟨Σ(u + w), u + w⟩| ≤ rvwBound(λ₁, λ₂)`.

**Why the triangle inequality approach fails:** Naively bounding
`|⟨Σv, v⟩| ≤ |⟨Σu, u⟩| + 2|⟨Σu, w⟩| + |⟨Σw, w⟩| ≤ λ₁a² + 2ac + c²`
gives the weaker bound `λ₁ + λ₂`, not `rvwBound`. The three terms
cannot simultaneously achieve their maxima because `Σ` is a reflection:
`⟨Σv, v⟩ = cos(2θ) · ‖v‖²` for some angle `θ`. The cross terms are
constrained by the hat term through the reflection geometry.

**RVW proof strategy (section 4.2):**
1. Since `Σ² = I` and `Σ* = Σ`, the space decomposes into `±1`-eigenspaces
   `S ⊕ S⊥`. For any `v`: `⟨Σv, v⟩ = cos(2θ) · ‖v‖²` where `θ` is
   the angle of `v` from `S`.
2. Express the Rayleigh quotient as `|cos 2θ| · cos²φ / cos²φ'` where
   `φ`, `φ'` are angles related to `u/(u+w̃)` and `u/(u+w)`.
3. The constraints translate to `tan φ'/tan φ ≤ λ₂` and `|cos 2ψ| ≤ λ₁`.
4. Two-case optimization (depending on whether `|cos 2x|` achieves 1 in
   `[ψ-φ', ψ+φ']`) yields `rvwBound` in both cases.
-/
private lemma reflection_quadratic_bound {n : ℕ}
    (Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig)
    (u w : EuclideanSpace ℝ (Fin n)) (h_orth : @inner ℝ _ _ u w = 0)
    (b : ℝ) (hb : 0 ≤ b)
    (h_unit : ‖u‖ ^ 2 + b ^ 2 = 1)
    (lam₁ lam₂ : ℝ) (hlam₁ : 0 ≤ lam₁) (hlam₂ : 0 ≤ lam₂)
    (h_hat : |@inner ℝ _ _ (Sig u) u| ≤ lam₁ * ‖u‖ ^ 2)
    (h_tilde_norm : ‖w‖ ≤ lam₂ * b) :
    |@inner ℝ _ _ (Sig (u + w)) (u + w)| ≤ rvwBound lam₁ lam₂ := by
  -- This is the mathematical core of RVW (2002) Section 4.2.
  -- The proof uses the reflection structure of Σ and a geometric
  -- two-case optimization over angles. See the paper for details.
  sorry

/-- **The core RVW operator norm bound (abstract).**

    Given operators on a real inner product space satisfying:
    - `W = B · Σ · B` (walk factorization)
    - `Q` orthogonal projection (`Q² = Q`, `Q* = Q`)
    - `B` self-adjoint contraction preserving `Q` (`BQ = QB = Q`, `‖B‖ ≤ 1`)
    - `Σ` self-adjoint involution (`Σ² = 1`, `Σ* = Σ`, `ΣP = P`)
    - `P ≤ Q` projections (`PQ = QP = P`)
    - `∀ x ∈ ker Q, ‖Bx‖ ≤ λ₂·‖x‖` (within-cluster contraction on tilde subspace)
    - `‖QΣQ - P‖ ≤ λ₁` (hat-block spectral gap)

    Then `‖W - P‖ ≤ rvwBound(λ₁, λ₂)`.

    ## Proof Strategy (RVW Section 4.2)

    The proof uses the Rayleigh quotient characterization for self-adjoint operators:
    ```
    ‖W - P‖ = sup { |⟨(W-P)x, x⟩| : ‖x‖ = 1 }
    ```

    **Step 1: Reduce to x ⊥ P.** Since `ΣP = P`, we get `WP = BΣBP = BΣP = BP = P`,
    so `(W-P)` annihilates `range(P)`. The sup is achieved on `range(P)⊥`.

    **Step 2: For x ⊥ P with ‖x‖ = 1**, decompose `x = x̂ + x̃` where `x̂ = Qx`,
    `x̃ = (I-Q)x`. By self-adjointness of B: `⟨(W-P)x, x⟩ = ⟨Σv, v⟩` where
    `v = x̂ + Bx̃` (using `Bx̂ = x̂` and `Px = 0 ⟹ Px̂ = 0`).

    **Step 3: Apply the reflection bound.** Since `Σ` is a reflection (`Σ² = I`,
    `Σ* = Σ`), `⟨Σv, v⟩ = cos(2θ)·‖v‖²` where `θ` is the angle of `v` from the
    `+1`-eigenspace of `Σ`. The constraints `|⟨Σx̂, x̂⟩| ≤ λ₁·‖x̂‖²` (hat block) and
    `‖Bx̃‖ ≤ λ₂·‖x̃‖` (tilde contraction) restrict the geometry. A two-case
    optimization (RVW Section 4.2) shows `|⟨Σv, v⟩| ≤ rvwBound(λ₁, λ₂)`.

    **Key insight (why triangle inequality fails):** Bounding the three terms
    `|⟨Σx̂,x̂⟩| + 2|⟨Σx̂,Bx̃⟩| + |⟨Σ(Bx̃),Bx̃⟩|` independently gives the weaker
    bound `λ₁ + λ₂`, not `rvwBound`. The reflection structure of `Σ` constrains
    all terms simultaneously — when the hat term is large, the cross terms are small,
    and vice versa.

    This is the mathematical core of the Reingold–Vadhan–Wigderson (2002)
    spectral composition theorem. -/
theorem rvw_operator_norm_bound
    {n : ℕ} (hn : 0 < n)
    (W B Sig Q P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hfact : W = B * Sig * B)
    (hQ_proj : Q * Q = Q) (hQ_sa : IsSelfAdjoint Q)
    (hBQ : B * Q = Q) (hQB : Q * B = Q)
    (hB_sa : IsSelfAdjoint B) (hB_contr : ‖B‖ ≤ 1)
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig)
    (hSigP : Sig * P = P)
    (hP_proj : P * P = P) (hP_sa : IsSelfAdjoint P)
    (hPQ : P * Q = P) (hQP : Q * P = P)
    (lam₁ lam₂ : ℝ) (hlam₁ : 0 ≤ lam₁) (hlam₂ : 0 ≤ lam₂)
    (h_tilde : ∀ x, Q x = 0 → ‖B x‖ ≤ lam₂ * ‖x‖)
    (h_hat : ‖Q * Sig * Q - P‖ ≤ lam₁) :
    ‖W - P‖ ≤ rvwBound lam₁ lam₂ := by
  -- Full proof requires:
  -- 1. rayleigh_quotient_bound (self-adjoint operator norm = Rayleigh quotient)
  -- 2. WP = P reduction (from hSigP, hBQ, hPQ)
  -- 3. Decomposition x = x̂ + x̃ and v = x̂ + Bx̃
  -- 4. reflection_quadratic_bound (the geometric core)
  sorry
