/-
  # Abstract RVW Operator Norm Bound

  The pure operator-theory core of the Reingold–Vadhan–Wigderson spectral
  composition theorem. Given operators `W = B · Σ · B` on a Hilbert space
  with projections `Q ≥ P`, the bound `‖W - P‖ ≤ rvwBound(λ₁, λ₂)` follows
  from the contraction `‖B(I-Q)‖ ≤ λ₂` and the spectral gap `‖QΣQ - P‖ ≤ λ₁`.

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
    -- spectralRadius = sup{‖k‖ : k ∈ spectrum}
    -- For self-adjoint A on EuclideanSpace ℝ (Fin n):
    -- - spectrum consists of real eigenvalues (Matrix.IsHermitian.eigenvalues_mem_spectrum_real)
    -- - eigenvalues achieved by Rayleigh quotient extrema (Rayleigh.lean)
    -- - spectralRadius ℂ A = ‖A‖ for self-adjoint (IsSelfAdjoint.spectralRadius_eq_nnnorm)
    -- - Therefore: ‖A‖ = spectralRadius = max |eigenvalue| = max Rayleigh extremum
    --
    -- The connection requires bridging:
    -- (a) CLM ↔ Matrix ↔ LinearMap representations
    -- (b) spectrum ↔ eigenvalues ↔ Rayleigh extrema
    --
    -- Components in Mathlib:
    -- - spectralRadius 𝕜 a = ⨆ k ∈ spectrum 𝕜 a, ‖k‖₊ (Normed/Algebra/Spectrum.lean)
    -- - Matrix.spectrum_toEuclideanLin: spectrum match (Matrix/Spectrum.lean:39)
    -- - IsHermitian.eigenvalues_mem_spectrum_real (Matrix/Spectrum.lean:77)
    -- - hasEigenvalue_iSup_of_finiteDimensional (InnerProductSpace/Rayleigh.lean:230)
    --
    -- Missing: explicit proof that for EuclideanSpace ℝ (Fin n):
    --   max{|⟨Ax,x⟩| : ‖x‖=1} = max{|λ| : λ eigenvalue of A}
    sorry

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

/-- **The core RVW operator norm bound (abstract).**

    Given operators on a real inner product space satisfying:
    - `W = B · Σ · B` (walk factorization)
    - `Q` orthogonal projection (`Q² = Q`, `Q* = Q`)
    - `B` self-adjoint contraction preserving `Q` (`BQ = QB = Q`, `‖B‖ ≤ 1`)
    - `Σ` self-adjoint involution (`Σ² = 1`, `Σ* = Σ`)
    - `P ≤ Q` projections (`PQ = QP = P`)
    - `‖B(I-Q)‖ ≤ λ₂` (within-cluster contraction on tilde subspace)
    - `‖QΣQ - P‖ ≤ λ₁` (hat-block spectral gap)

    Then `‖W - P‖ ≤ rvwBound(λ₁, λ₂)`.

    The proof decomposes the Rayleigh quotient `⟨Wx, x⟩` via the hat/tilde
    decomposition `x = Qx + (I-Q)x` and bounds the resulting expression
    by the largest eigenvalue of the 2×2 matrix `[[(1-λ₂²)λ₁, λ₂], [λ₂, 0]]`.

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
    (hP_proj : P * P = P) (hP_sa : IsSelfAdjoint P)
    (hPQ : P * Q = P) (hQP : Q * P = P)
    (lam₁ lam₂ : ℝ) (hlam₁ : 0 ≤ lam₁) (hlam₂ : 0 ≤ lam₂)
    (h_tilde : ‖B * (1 - Q)‖ ≤ lam₂)
    (h_hat : ‖Q * Sig * Q - P‖ ≤ lam₁) :
    ‖W - P‖ ≤ rvwBound lam₁ lam₂ := by
  -- Proof outline:
  -- 1. Use Rayleigh quotient characterization: ‖W - P‖ = sup_{‖x‖=1} |⟨(W-P)x, x⟩|
  -- 2. For any unit vector x, decompose x = x̂ + x̃ where x̂ = Qx, x̃ = (I-Q)x
  -- 3. Expand ⟨W x, x⟩ using the factorization W = B·Σ·B
  -- 4. Bound the cross terms using h_tilde (‖B(I-Q)‖ ≤ λ₂) and orthogonality
  -- 5. Bound the hat term using h_hat (‖QΣQ - P‖ ≤ λ₁)
  -- 6. The Rayleigh quotient reduces to a 2×2 optimization whose maximum is rvwBound

  -- W - P is self-adjoint (since W = B·Σ·B and all operators are self-adjoint)
  have hWP_sa : IsSelfAdjoint (W - P) := by
    sorry

  -- Use Rayleigh quotient bound
  have ray_bound := rayleigh_quotient_bound hn (W - P) hWP_sa

  -- Bound the Rayleigh quotient for each unit vector
  have key : ∀ (x : EuclideanSpace ℝ (Fin n)), ‖x‖ = 1 →
      |@inner ℝ _ _ ((W - P) x) x| ≤ rvwBound lam₁ lam₂ := by
    intro x hx
    -- Decompose x = Q x + (I-Q) x
    -- Use orthogonality: ⟨Q x, (I-Q) x⟩ = 0
    have orth := hat_tilde_orthogonal Q hQ_proj hQ_sa x
    -- Norm decomposition: ‖x‖² = ‖Q x‖² + ‖(I-Q) x‖²
    have norm_decomp := hat_tilde_norm_sq Q hQ_proj hQ_sa x
    -- This gives us ‖Q x‖² + ‖(I-Q) x‖² = 1

    -- Expand the inner product
    -- The detailed calculation reduces to bounding by rvwBound
    sorry

  -- Conclude using the Rayleigh quotient characterization
  sorry
