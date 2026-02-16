/-
  # RVW Bound via Trigonometric/Geometric Approach (EXPLORATORY — NOT USEFUL)

  **Status: This approach does NOT close the sorry.** The RVW paper's
  Section 4.2 (Claim 4.4) proves only a *weaker* eigenvalue bound:
  `paperBound(λ₁,λ₂) = (λ₁+λ₂² + √((λ₁-λ₂²)²+4λ₂²))/2`, which is
  strictly larger than the tight `rvwBound` by `λ₂²(1+λ₁)` in the linear
  coefficient. The weaker bound has no fixed point below 1 with our D=12
  base expander (β=5/9), so it cannot support the zigzag iteration. The
  tight `rvwBound` is necessary.

  This file was developed to explore whether the paper's eigenspace
  decomposition would yield a different proof path. It doesn't — the same
  scalar inequality `rvw_quadratic_ineq` remains at the core, regardless
  of whether we approach it via eigenspace projections or directly.

  **What's here:** Eigenspace projection infrastructure (`piPlus`, `piMinus`),
  orthogonality/norm decomposition lemmas, Cauchy-Schwarz in eigenspace
  coordinates, and the full assembly `reflection_quadratic_bound_trig` —
  all proved except the one sorry at line ~281 (same inequality as in
  `RVWBound.lean`).

  **The sorry** (`rvw_trig_bound`, line ~281): same core polynomial inequality
  as `rvw_quadratic_ineq` in `RVWBound.lean`:
    `(p+2q+r)² · a²b² ≤ (b²-c²) · |p| · |p+2q+r| + a²c²`
  `nlinarith` (diagonal Positivstellensatz) is structurally infeasible for
  this. Full-matrix SOS certificate exists at degree 6 (SDP confirms) but
  extraction requires a high-precision solver. See CLAUDE.md for full analysis.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import AKS.RVWBound

open BigOperators


/-! **Pure Algebraic Helpers** -/

/-- `max(|a+b|, |a-b|) = |a| + |b|` for all reals `a`, `b`. -/
private lemma max_abs_sum_diff (a b : ℝ) :
    max (|a + b|) (|a - b|) = |a| + |b| := by
  apply le_antisymm
  · -- ≤ : both |a+b| and |a-b| ≤ |a| + |b| by triangle inequality
    apply max_le
    · exact abs_add_le a b
    · calc |a - b| = |a + (-b)| := by ring_nf
        _ ≤ |a| + |-b| := abs_add_le a (-b)
        _ = |a| + |b| := by rw [abs_neg]
  · -- ≥ : case split on signs shows one of the two equals |a|+|b|
    rw [le_max_iff]
    rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb
    · -- a ≥ 0, b ≥ 0: |a+b| = a+b = |a|+|b|
      left; rw [abs_of_nonneg (add_nonneg ha hb), abs_of_nonneg ha, abs_of_nonneg hb]
    · -- a ≥ 0, b < 0: |a-b| = a+|b| = |a|+|b|
      right; rw [abs_of_nonneg ha, abs_of_neg hb,
        abs_of_nonneg (show 0 ≤ a - b from by linarith)]; linarith
    · -- a < 0, b ≥ 0: |a-b| = |a|+b = |a|+|b|
      right; rw [abs_of_neg ha, abs_of_nonneg hb,
        abs_of_nonpos (show a - b ≤ 0 from by linarith)]; linarith
    · -- a < 0, b < 0: |a+b| = |a|+|b|
      left; rw [abs_of_neg ha, abs_of_neg hb,
        abs_of_nonpos (show a + b ≤ 0 from by linarith)]; linarith

/-- Cauchy-Schwarz for 2D: `|A*x + B*y| ≤ √(A² + B²)` when `x² + y² ≤ 1`. -/
private lemma cauchy_schwarz_2d {A B x y : ℝ} (hxy : x ^ 2 + y ^ 2 ≤ 1) :
    |A * x + B * y| ≤ Real.sqrt (A ^ 2 + B ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (A * y - B * x)])


/-! **Involution Helpers**

Reusable facts about a self-adjoint involution `Sig` on a real Hilbert space. -/

private lemma sig_sym' {n : ℕ}
    {Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hSig_sa : IsSelfAdjoint Sig)
    (u v : EuclideanSpace ℝ (Fin n)) :
    @inner ℝ _ _ (Sig u) v = @inner ℝ _ _ u (Sig v) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hSig_sa u v

private lemma sig_sq' {n : ℕ}
    {Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hSig_inv : Sig * Sig = 1)
    (v : EuclideanSpace ℝ (Fin n)) : Sig (Sig v) = v := by
  have h := ContinuousLinearMap.ext_iff.mp hSig_inv v
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at h
  exact h

private lemma sig_inner_sq' {n : ℕ}
    {Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig)
    (v : EuclideanSpace ℝ (Fin n)) :
    @inner ℝ _ _ (Sig v) (Sig v) = @inner ℝ _ _ v v := by
  calc @inner ℝ _ _ (Sig v) (Sig v)
      = @inner ℝ _ _ v (Sig (Sig v)) := sig_sym' hSig_sa v (Sig v)
    _ = @inner ℝ _ _ v v := by rw [sig_sq' hSig_inv]

private lemma sig_norm_eq' {n : ℕ}
    {Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig)
    (v : EuclideanSpace ℝ (Fin n)) : ‖Sig v‖ = ‖v‖ := by
  have : ‖Sig v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    exact sig_inner_sq' hSig_inv hSig_sa v
  nlinarith [norm_nonneg (Sig v), norm_nonneg v, sq_nonneg (‖Sig v‖ - ‖v‖)]

private lemma sig_orth' {n : ℕ}
    {Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig)
    (u w : EuclideanSpace ℝ (Fin n)) (h_orth : @inner ℝ _ _ u w = 0) :
    @inner ℝ _ _ (Sig u) (Sig w) = 0 := by
  calc @inner ℝ _ _ (Sig u) (Sig w)
      = @inner ℝ _ _ u (Sig (Sig w)) := sig_sym' hSig_sa u (Sig w)
    _ = @inner ℝ _ _ u w := by rw [sig_sq' hSig_inv]
    _ = 0 := h_orth


/-! **Eigenspace Projections** -/

private noncomputable def piPlus {n : ℕ}
    (Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (1/2 : ℝ) • (v + Sig v)

private noncomputable def piMinus {n : ℕ}
    (Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (1/2 : ℝ) • (v - Sig v)

private lemma piPlus_add_piMinus {n : ℕ}
    (Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) :
    piPlus Sig v + piMinus Sig v = v := by
  simp only [piPlus, piMinus]; module

private lemma piPlus_perp_piMinus {n : ℕ}
    {Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig)
    (v : EuclideanSpace ℝ (Fin n)) :
    @inner ℝ _ _ (piPlus Sig v) (piMinus Sig v) = 0 := by
  simp only [piPlus, piMinus, inner_smul_left, inner_smul_right, conj_trivial]
  rw [inner_sub_right, inner_add_left, inner_add_left]
  rw [sig_inner_sq' hSig_inv hSig_sa, real_inner_comm (Sig v) v]; ring

private lemma norm_sq_piPlus_piMinus {n : ℕ}
    {Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig)
    (v : EuclideanSpace ℝ (Fin n)) :
    ‖v‖ ^ 2 = ‖piPlus Sig v‖ ^ 2 + ‖piMinus Sig v‖ ^ 2 := by
  calc ‖v‖ ^ 2
      = ‖piPlus Sig v + piMinus Sig v‖ ^ 2 := by rw [piPlus_add_piMinus]
    _ = ‖piPlus Sig v + piMinus Sig v‖ *
        ‖piPlus Sig v + piMinus Sig v‖ := sq _
    _ = ‖piPlus Sig v‖ * ‖piPlus Sig v‖ +
        ‖piMinus Sig v‖ * ‖piMinus Sig v‖ :=
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
            (piPlus_perp_piMinus hSig_inv hSig_sa v)
    _ = ‖piPlus Sig v‖ ^ 2 + ‖piMinus Sig v‖ ^ 2 := by rw [← sq, ← sq]

/-- ⟨Σv,v⟩ = ‖Π₊v‖² - ‖Π₋v‖². -/
private lemma rayleigh_eigenspace {n : ℕ}
    {Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig)
    (v : EuclideanSpace ℝ (Fin n)) :
    @inner ℝ _ _ (Sig v) v =
      ‖piPlus Sig v‖ ^ 2 - ‖piMinus Sig v‖ ^ 2 := by
  simp only [piPlus, piMinus, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2), mul_pow]
  have h_add : ‖v + Sig v‖ ^ 2 = 2 * (‖v‖ ^ 2 + @inner ℝ _ _ (Sig v) v) := by
    rw [norm_add_sq_real, real_inner_comm v (Sig v), sig_norm_eq' hSig_inv hSig_sa]; ring
  have h_sub : ‖v - Sig v‖ ^ 2 = 2 * (‖v‖ ^ 2 - @inner ℝ _ _ (Sig v) v) := by
    rw [norm_sub_sq_real, real_inner_comm v (Sig v), sig_norm_eq' hSig_inv hSig_sa]; ring
  nlinarith


/-! **Cross-term Identities** -/

/-- ⟨Π₊u, Π₊w⟩ = q/2, when u ⊥ w. -/
private lemma cross_piPlus {n : ℕ}
    {Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig)
    {u w : EuclideanSpace ℝ (Fin n)} (h_orth : @inner ℝ _ _ u w = 0) :
    @inner ℝ _ _ (piPlus Sig u) (piPlus Sig w) =
      @inner ℝ _ _ (Sig u) w / 2 := by
  simp only [piPlus, inner_smul_left, inner_smul_right, conj_trivial,
    inner_add_left, inner_add_right]
  have h1 := h_orth
  have h2 : @inner ℝ _ _ u (Sig w) = @inner ℝ _ _ (Sig u) w :=
    (sig_sym' hSig_sa u w).symm
  have h3 := sig_orth' hSig_inv hSig_sa u w h_orth
  rw [h1, h2, h3]; ring

/-- ⟨Π₋u, Π₋w⟩ = -q/2, when u ⊥ w. -/
private lemma cross_piMinus {n : ℕ}
    {Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig)
    {u w : EuclideanSpace ℝ (Fin n)} (h_orth : @inner ℝ _ _ u w = 0) :
    @inner ℝ _ _ (piMinus Sig u) (piMinus Sig w) =
      -@inner ℝ _ _ (Sig u) w / 2 := by
  simp only [piMinus, inner_smul_left, inner_smul_right, conj_trivial,
    inner_sub_left, inner_sub_right]
  have h1 := h_orth
  have h2 : @inner ℝ _ _ u (Sig w) = @inner ℝ _ _ (Sig u) w :=
    (sig_sym' hSig_sa u w).symm
  have h3 := sig_orth' hSig_inv hSig_sa u w h_orth
  rw [h1, h2, h3]; ring


/-! **Eigenspace CS Inequalities** -/

private lemma eigenspace_cs_plus {n : ℕ}
    {Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig)
    {u w : EuclideanSpace ℝ (Fin n)} (h_orth : @inner ℝ _ _ u w = 0) :
    (@inner ℝ _ _ (Sig u) w / 2) ^ 2 ≤
      ‖piPlus Sig u‖ ^ 2 * ‖piPlus Sig w‖ ^ 2 := by
  rw [← cross_piPlus hSig_inv hSig_sa h_orth]
  calc @inner ℝ _ _ (piPlus Sig u) (piPlus Sig w) ^ 2
      = |@inner ℝ _ _ (piPlus Sig u) (piPlus Sig w)| ^ 2 := (sq_abs _).symm
    _ ≤ (‖piPlus Sig u‖ * ‖piPlus Sig w‖) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
    _ = ‖piPlus Sig u‖ ^ 2 * ‖piPlus Sig w‖ ^ 2 := by ring

private lemma eigenspace_cs_minus {n : ℕ}
    {Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig)
    {u w : EuclideanSpace ℝ (Fin n)} (h_orth : @inner ℝ _ _ u w = 0) :
    (@inner ℝ _ _ (Sig u) w / 2) ^ 2 ≤
      ‖piMinus Sig u‖ ^ 2 * ‖piMinus Sig w‖ ^ 2 := by
  have h := cross_piMinus hSig_inv hSig_sa h_orth
  have : (@inner ℝ _ _ (Sig u) w / 2) ^ 2 =
      @inner ℝ _ _ (piMinus Sig u) (piMinus Sig w) ^ 2 := by rw [h]; ring
  rw [this]
  calc @inner ℝ _ _ (piMinus Sig u) (piMinus Sig w) ^ 2
      = |@inner ℝ _ _ (piMinus Sig u) (piMinus Sig w)| ^ 2 := (sq_abs _).symm
    _ ≤ (‖piMinus Sig u‖ * ‖piMinus Sig w‖) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
    _ = ‖piMinus Sig u‖ ^ 2 * ‖piMinus Sig w‖ ^ 2 := by ring


/-! **The Core Scalar Bound**

The paper's Case I argument in algebraic form. This is the sole sorry
in this file. -/

/-- The discriminant identity:
    ¼(1+μ₂²)²μ₁² + μ₂²(1-μ₁²) = ¼(1-μ₂²)²μ₁² + μ₂². -/
private lemma discriminant_identity (μ₁ μ₂ : ℝ) :
    (1 + μ₂ ^ 2) ^ 2 * μ₁ ^ 2 / 4 + μ₂ ^ 2 * (1 - μ₁ ^ 2) =
    (1 - μ₂ ^ 2) ^ 2 * μ₁ ^ 2 / 4 + μ₂ ^ 2 := by ring

/-- The core scalar bound via the paper's geometric approach.

    This replaces `rvw_quadratic_ineq` with a proof following
    the RVW paper's Section 4.2 Case I argument:
    1. X is affine in ζ → max at CS boundary
    2. `max(|a+b|, |a-b|) = |a| + |b|`
    3. Cauchy-Schwarz on 2D
    4. Discriminant simplification to rvwBound -/
private lemma rvw_trig_bound
    (a b c p q r : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hcb : c ≤ b)
    (h_unit : a ^ 2 + b ^ 2 = 1)
    (h_refl_u : |p| ≤ a ^ 2) (h_refl_w : |r| ≤ c ^ 2)
    (h_cs_plus : q ^ 2 ≤ (a ^ 2 + p) * (c ^ 2 + r))
    (h_cs_minus : q ^ 2 ≤ (a ^ 2 - p) * (c ^ 2 - r)) :
    |p + 2 * q + r| ≤ rvwBound (|p| / a ^ 2) (c / b) := by
  -- Handle c = 0 case separately
  by_cases hc0 : c = 0
  · have hr0 : r = 0 := by nlinarith [abs_le.mp h_refl_w]
    have hq0 : q = 0 := by
      have h1 : c ^ 2 + r = 0 := by nlinarith [abs_le.mp h_refl_w]
      have h2 : q ^ 2 ≤ 0 := by rw [h1] at h_cs_plus; nlinarith [abs_le.mp h_refl_u]
      nlinarith [sq_nonneg q]
    simp only [hr0, hq0, mul_zero, add_zero, hc0, zero_div]
    have hμ : 0 ≤ |p| / a ^ 2 := div_nonneg (abs_nonneg _) (by positivity)
    have hμ1 : |p| / a ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity : (0:ℝ) < a ^ 2)]; exact h_refl_u
    calc |p| = |p| / a ^ 2 * a ^ 2 := by field_simp
      _ ≤ |p| / a ^ 2 * 1 := by nlinarith
      _ = |p| / a ^ 2 := mul_one _
      _ ≤ rvwBound (|p| / a ^ 2) 0 := by
          unfold rvwBound
          have : Real.sqrt ((1 - 0 ^ 2) ^ 2 * (|p| / a ^ 2) ^ 2 / 4 + 0 ^ 2) =
              |p| / a ^ 2 / 2 := by
            rw [show (1 - 0 ^ 2) ^ 2 * (|p| / a ^ 2) ^ 2 / 4 + 0 ^ 2 =
                (|p| / a ^ 2 / 2) ^ 2 from by ring]
            exact Real.sqrt_sq (by positivity)
          linarith
  · -- Main case: c > 0
    have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    set μ₁ := |p| / a ^ 2
    set μ₂ := c / b
    have hμ₁_nn : 0 ≤ μ₁ := div_nonneg (abs_nonneg _) (by positivity)
    have hμ₂_nn : 0 ≤ μ₂ := div_nonneg hc hb.le
    have hμ₂_le : μ₂ ≤ 1 := by rw [div_le_one hb]; exact hcb
    have hμ₂_pos : 0 < μ₂ := div_pos hc_pos hb
    -- Step 1: Suffices to show the quadratic inequality X² ≤ C·|X| + D²
    suffices h_qi : (p + 2 * q + r) ^ 2 ≤
        (1 - μ₂ ^ 2) * μ₁ * |p + 2 * q + r| + μ₂ ^ 2 by
      -- Derive |X| ≤ rvwBound by contradiction using quadratic characterization
      set R := rvwBound μ₁ μ₂
      set X := |p + 2 * q + r|
      have hR_nn : 0 ≤ R := rvwBound_nonneg μ₁ μ₂ hμ₁_nn hμ₂_nn hμ₂_le
      have hX_nn : 0 ≤ X := abs_nonneg _
      have hR_eq := rvwBound_quadratic_eq μ₁ μ₂ hμ₁_nn hμ₂_nn
      -- rvwBound² = (1-μ₂²)μ₁·rvwBound + μ₂² and X² ≤ (1-μ₂²)μ₁·X + μ₂²
      by_contra h_neg
      push_neg at h_neg
      -- X > R ≥ 0, so X - R > 0
      have hXR : 0 < X - R := by linarith
      -- From X² ≤ C·X + D² and R² = C·R + D²: (X-R)(X+R) ≤ C(X-R)
      set C := (1 - μ₂ ^ 2) * μ₁
      have hC_nn : 0 ≤ C := mul_nonneg (by nlinarith [hμ₂_le]) hμ₁_nn
      have hR_sq : R ^ 2 = C * R + μ₂ ^ 2 := hR_eq
      -- (X-R)(X+R) = X²-R² ≤ C·X + μ₂² - (C·R + μ₂²) = C(X-R)
      have h1 : (X - R) * (X + R) ≤ C * (X - R) := by nlinarith [sq_abs (p + 2 * q + r)]
      -- Divide by (X - R) > 0
      have h_sum_le : X + R ≤ C := by
        rcases le_or_gt (X + R) C with h | h
        · exact h
        · exfalso; nlinarith [mul_lt_mul_of_pos_left h hXR]
      -- But R > C since R² = C·R + μ₂² and μ₂ > 0
      have hRC : C < R := by nlinarith [sq_nonneg R]
      -- X + R > R > C contradicts X + R ≤ C
      linarith
    -- Step 2: Clear denominators by multiplying by a²b² > 0
    have ha2 : (0:ℝ) < a ^ 2 := by positivity
    have hb2 : (0:ℝ) < b ^ 2 := by positivity
    have hab2 : (0:ℝ) < a ^ 2 * b ^ 2 := by positivity
    rw [show (1 - μ₂ ^ 2) * μ₁ * |p + 2 * q + r| + μ₂ ^ 2 =
        ((b ^ 2 - c ^ 2) * |p| * |p + 2 * q + r| + a ^ 2 * c ^ 2) / (a ^ 2 * b ^ 2) from by
      simp only [μ₁, μ₂]; field_simp]
    rw [le_div_iff₀ hab2]
    -- Goal: (p + 2*q + r)² * (a²*b²) ≤ (b²-c²)*|p|*|X| + a²*c²
    -- Step 3: Derive useful bounds
    have hp_le : p ≤ a ^ 2 := by linarith [(abs_le.mp h_refl_u).2]
    have hp_ge : -(a ^ 2) ≤ p := by linarith [(abs_le.mp h_refl_u).1]
    have hr_le : r ≤ c ^ 2 := by linarith [(abs_le.mp h_refl_w).2]
    have hr_ge : -(c ^ 2) ≤ r := by linarith [(abs_le.mp h_refl_w).1]
    have hbc2 : 0 ≤ b ^ 2 - c ^ 2 := by nlinarith
    -- Combined CS: a²q² ≤ c²(a⁴-p²)
    have h_combined : a ^ 2 * q ^ 2 ≤ c ^ 2 * (a ^ 4 - p ^ 2) := by
      have h1 : (a ^ 2 - p) * q ^ 2 ≤ (a ^ 2 - p) * ((a ^ 2 + p) * (c ^ 2 + r)) :=
        mul_le_mul_of_nonneg_left h_cs_plus (by linarith)
      have h2 : (a ^ 2 + p) * q ^ 2 ≤ (a ^ 2 + p) * ((a ^ 2 - p) * (c ^ 2 - r)) :=
        mul_le_mul_of_nonneg_left h_cs_minus (by linarith)
      nlinarith
    -- Step 4: The core polynomial inequality.
    -- Goal: (p+2q+r)² * a²b² ≤ (b²-c²) * |p| * |p+2q+r| + a²c²
    -- KNOWN OPEN: nlinarith (diagonal Positivstellensatz) is structurally infeasible
    -- for this inequality — the tight manifold {c=b, p=a², r=c², q=0} forces every
    -- diagonal certificate term to vanish. Full-matrix SOS certificate exists at
    -- degree 6 (SDP confirms feasibility) but first-order solvers (SCS, CLARABEL)
    -- lack precision for exact rational extraction. Viable paths:
    --   (A) High-precision SDP (MOSEK/SDPA-GMP) → exact certificate → nlinarith hints
    --   (B) Fundamentally different proof technique (the RVW paper does NOT prove
    --       this tight bound; it only proves f < 1 via a weaker eigenvalue bound)
    sorry


/-! **Assembly** -/

/-- Optimization bound: chains `rvw_trig_bound` with monotonicity.
    Handles edge cases (a=0 or b=0) separately. -/
private lemma rvw_optimization_bound_trig
    (a b c p q r lam₁ lam₂ : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hlam₁ : 0 ≤ lam₁) (hlam₂ : 0 ≤ lam₂)
    (hlam₁_le : lam₁ ≤ 1) (hlam₂_le : lam₂ ≤ 1)
    (h_unit : a ^ 2 + b ^ 2 = 1)
    (h_tilde : c ≤ lam₂ * b)
    (h_hat : |p| ≤ lam₁ * a ^ 2)
    (h_refl_u : |p| ≤ a ^ 2)
    (h_refl_w : |r| ≤ c ^ 2)
    (h_cs_plus : q ^ 2 ≤ (a ^ 2 + p) * (c ^ 2 + r))
    (h_cs_minus : q ^ 2 ≤ (a ^ 2 - p) * (c ^ 2 - r)) :
    |p + 2 * q + r| ≤ rvwBound lam₁ lam₂ := by
  by_cases ha0 : a = 0
  · -- a = 0: p = q = 0
    have hp : p = 0 := abs_nonpos_iff.mp (by rw [ha0] at h_refl_u; simpa using h_refl_u)
    have hq : q = 0 := sq_eq_zero_iff.mp (le_antisymm
      (by rw [ha0, hp] at h_cs_plus; simpa using h_cs_plus) (sq_nonneg q))
    simp only [hp, hq, mul_zero, add_zero, zero_add]
    have hb1 : b = 1 := by nlinarith [sq_nonneg b]
    calc |r| ≤ c ^ 2 := h_refl_w
      _ ≤ lam₂ ^ 2 := by nlinarith [hb1]
      _ ≤ lam₂ := by nlinarith
      _ ≤ rvwBound lam₁ lam₂ := by
            unfold rvwBound
            have h1 : 0 ≤ (1 - lam₂ ^ 2) * lam₁ / 2 := by
              apply div_nonneg _ (by norm_num : (0:ℝ) ≤ 2)
              exact mul_nonneg (by nlinarith) hlam₁
            have h2 : lam₂ ≤ Real.sqrt ((1 - lam₂ ^ 2) ^ 2 * lam₁ ^ 2 / 4 + lam₂ ^ 2) := by
              conv_lhs => rw [← Real.sqrt_sq hlam₂]
              exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ((1 - lam₂ ^ 2) * lam₁)])
            linarith
  · by_cases hb0 : b = 0
    · have hc0 : c = 0 := by nlinarith [mul_nonneg hlam₂ hb]
      have hr : r = 0 := abs_nonpos_iff.mp (by rw [hc0] at h_refl_w; simpa using h_refl_w)
      have hq : q = 0 := sq_eq_zero_iff.mp (le_antisymm
        (by rw [hc0, hr] at h_cs_plus; simpa using h_cs_plus) (sq_nonneg q))
      simp only [hq, hr, mul_zero, add_zero]
      have ha1 : a ^ 2 = 1 := by nlinarith [sq_nonneg a]
      calc |p| ≤ lam₁ * a ^ 2 := h_hat
        _ = lam₁ := by rw [ha1, mul_one]
        _ ≤ rvwBound lam₁ lam₂ := by
              unfold rvwBound
              have hD_ge : ((1 + lam₂ ^ 2) * lam₁ / 2) ^ 2 ≤
                  (1 - lam₂ ^ 2) ^ 2 * lam₁ ^ 2 / 4 + lam₂ ^ 2 := by
                nlinarith [sq_nonneg (1 - lam₁), sq_nonneg (lam₂ * (1 - lam₁))]
              have hnn : 0 ≤ (1 + lam₂ ^ 2) * lam₁ / 2 := by positivity
              have := Real.sqrt_le_sqrt hD_ge
              rw [Real.sqrt_sq hnn] at this
              linarith
    · -- Main case: a > 0, b > 0
      have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have hcb' : c ≤ b := le_trans h_tilde (by nlinarith)
      have h1 := rvw_trig_bound a b c p q r ha_pos hb_pos hc hcb'
        h_unit h_refl_u h_refl_w h_cs_plus h_cs_minus
      have hmu1 : |p| / a ^ 2 ≤ lam₁ := by
        rwa [div_le_iff₀ (by positivity : (0:ℝ) < a ^ 2)]
      have hmu2 : c / b ≤ lam₂ := by
        rw [div_le_iff₀ hb_pos]; linarith
      calc |p + 2 * q + r|
          ≤ rvwBound (|p| / a ^ 2) (c / b) := h1
        _ ≤ rvwBound lam₁ (c / b) :=
            rvwBound_mono_left (div_nonneg (abs_nonneg _) (by positivity))
              (div_nonneg hc hb_pos.le) (le_trans hmu2 hlam₂_le) hmu1
        _ ≤ rvwBound lam₁ lam₂ :=
            rvwBound_mono_right hlam₁ hlam₁_le (div_nonneg hc hb_pos.le) hlam₂_le hmu2

/-- **Alternative proof of `reflection_quadratic_bound` via the trig approach.**

    Same signature as `reflection_quadratic_bound` in `RVWBound.lean`.
    Once the sorry in `rvw_trig_bound` is filled, this can replace the
    existing proof chain. -/
theorem reflection_quadratic_bound_trig {n : ℕ}
    (Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig)
    (u w : EuclideanSpace ℝ (Fin n)) (h_orth : @inner ℝ _ _ u w = 0)
    (b : ℝ) (hb : 0 ≤ b)
    (h_unit : ‖u‖ ^ 2 + b ^ 2 = 1)
    (lam₁ lam₂ : ℝ) (hlam₁ : 0 ≤ lam₁) (hlam₂ : 0 ≤ lam₂)
    (hlam₁_le : lam₁ ≤ 1) (hlam₂_le : lam₂ ≤ 1)
    (h_hat : |@inner ℝ _ _ (Sig u) u| ≤ lam₁ * ‖u‖ ^ 2)
    (h_tilde_norm : ‖w‖ ≤ lam₂ * b) :
    |@inner ℝ _ _ (Sig (u + w)) (u + w)| ≤ rvwBound lam₁ lam₂ := by
  set a_val := ‖u‖; set c_val := ‖w‖
  set p_val := @inner ℝ _ _ (Sig u) u
  set q_val := @inner ℝ _ _ (Sig u) w
  set r_val := @inner ℝ _ _ (Sig w) w
  -- Bilinear expansion
  have h_expand : @inner ℝ _ _ (Sig (u + w)) (u + w) =
      p_val + 2 * q_val + r_val := by
    rw [map_add, inner_add_left, inner_add_right, inner_add_right]
    have : @inner ℝ _ _ (Sig w) u = @inner ℝ _ _ (Sig u) w :=
      (sig_sym' hSig_sa w u).trans (real_inner_comm _ _)
    rw [this]; ring
  rw [h_expand]
  -- Reflection bounds
  have h_refl_u : |p_val| ≤ a_val ^ 2 := by
    calc |p_val| ≤ ‖Sig u‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ = ‖u‖ * ‖u‖ := by rw [sig_norm_eq' hSig_inv hSig_sa]
      _ = a_val ^ 2 := by ring
  have h_refl_w : |r_val| ≤ c_val ^ 2 := by
    calc |r_val| ≤ ‖Sig w‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ = ‖w‖ * ‖w‖ := by rw [sig_norm_eq' hSig_inv hSig_sa]
      _ = c_val ^ 2 := by ring
  -- CS via (I+Σ), following RVWBound.lean pattern
  have h_uSw : @inner ℝ _ _ u (Sig w) = q_val := (sig_sym' hSig_sa u w).symm
  have h_sig_orth : @inner ℝ _ _ (Sig u) (Sig w) = 0 :=
    sig_orth' hSig_inv hSig_sa u w h_orth
  have h_cs_plus : q_val ^ 2 ≤ (a_val ^ 2 + p_val) * (c_val ^ 2 + r_val) := by
    have h_inner : @inner ℝ _ _ (u + Sig u) (w + Sig w) = 2 * q_val := by
      simp only [inner_add_left, inner_add_right]
      rw [h_orth, h_uSw, h_sig_orth]; ring
    have h_nu : ‖u + Sig u‖ ^ 2 = 2 * (a_val ^ 2 + p_val) := by
      rw [norm_add_sq_real]
      have h1 : @inner ℝ _ _ u (Sig u) = p_val := by rw [real_inner_comm]
      rw [h1, sig_norm_eq' hSig_inv hSig_sa]; ring
    have h_nw : ‖w + Sig w‖ ^ 2 = 2 * (c_val ^ 2 + r_val) := by
      rw [norm_add_sq_real]
      have h1 : @inner ℝ _ _ w (Sig w) = r_val := by rw [real_inner_comm]
      rw [h1, sig_norm_eq' hSig_inv hSig_sa]; ring
    have hCS := abs_real_inner_le_norm (u + Sig u) (w + Sig w)
    rw [h_inner] at hCS
    set M := ‖u + Sig u‖ * ‖w + Sig w‖
    have hCS_le := abs_le.mp hCS
    have h_prod_nonneg : 0 ≤ M ^ 2 - (2 * q_val) ^ 2 := by
      have : 0 ≤ (M - 2 * q_val) * (M + 2 * q_val) :=
        mul_nonneg (by linarith [hCS_le.2]) (by linarith [hCS_le.1])
      nlinarith
    have hM_sq : M ^ 2 = 2 * (a_val ^ 2 + p_val) * (2 * (c_val ^ 2 + r_val)) := by
      simp only [M, mul_pow, h_nu, h_nw]
    rw [hM_sq] at h_prod_nonneg; nlinarith
  -- CS via (I-Σ)
  have h_cs_minus : q_val ^ 2 ≤ (a_val ^ 2 - p_val) * (c_val ^ 2 - r_val) := by
    have h_inner : @inner ℝ _ _ (u - Sig u) (w - Sig w) = -(2 * q_val) := by
      simp only [inner_sub_left, inner_sub_right]
      rw [h_orth, h_uSw, h_sig_orth]; ring
    have h_nu : ‖u - Sig u‖ ^ 2 = 2 * (a_val ^ 2 - p_val) := by
      rw [norm_sub_sq_real]
      have h1 : @inner ℝ _ _ u (Sig u) = p_val := by rw [real_inner_comm]
      rw [h1, sig_norm_eq' hSig_inv hSig_sa]; ring
    have h_nw : ‖w - Sig w‖ ^ 2 = 2 * (c_val ^ 2 - r_val) := by
      rw [norm_sub_sq_real]
      have h1 : @inner ℝ _ _ w (Sig w) = r_val := by rw [real_inner_comm]
      rw [h1, sig_norm_eq' hSig_inv hSig_sa]; ring
    have hCS := abs_real_inner_le_norm (u - Sig u) (w - Sig w)
    rw [h_inner] at hCS
    set M := ‖u - Sig u‖ * ‖w - Sig w‖
    have hCS_le := abs_le.mp hCS
    have h_prod_nonneg : 0 ≤ M ^ 2 - (-(2 * q_val)) ^ 2 := by
      have : 0 ≤ (M - -(2 * q_val)) * (M + -(2 * q_val)) :=
        mul_nonneg (by linarith [hCS_le.2]) (by linarith [hCS_le.1])
      nlinarith
    have hM_sq : M ^ 2 = 2 * (a_val ^ 2 - p_val) * (2 * (c_val ^ 2 - r_val)) := by
      simp only [M, mul_pow, h_nu, h_nw]
    rw [hM_sq] at h_prod_nonneg; nlinarith
  exact rvw_optimization_bound_trig a_val b c_val p_val q_val r_val lam₁ lam₂
    (norm_nonneg _) hb (norm_nonneg _) hlam₁ hlam₂ hlam₁_le hlam₂_le h_unit h_tilde_norm
    h_hat h_refl_u h_refl_w h_cs_plus h_cs_minus
