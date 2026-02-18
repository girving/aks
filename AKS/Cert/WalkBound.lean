/-
  # Walk Bound → Spectral Gap

  Abstract operator theory connecting quadratic walk bounds on mean-zero
  vectors to spectral gap bounds. No mention of certificates, base-85
  encoding, or rotation maps — this is pure operator theory.

  Two results:
  1. `spectralGap_le_of_walk_bound`: walk bound on mean-zero vectors → spectral gap bound
  2. `sqrt_coeff_le_frac`: coefficient arithmetic converting √(c₁/(c₂·d²)) to βn/(βd·d)
-/

import AKS.Graph.Regular

open BigOperators Finset


/-! **Walk bound implies spectral gap bound** -/

/-- If `c₂ · d² · ‖Wf‖² ≤ c₁ · ‖f‖²` for all mean-zero `f`,
    then `spectralGap G ≤ √(c₁ / (c₂ · d²))`.

    This is the abstract version of the certificate bridge: any proof method
    that establishes a quadratic walk bound on mean-zero vectors gives a
    spectral gap bound. -/
theorem spectralGap_le_of_walk_bound
    {n d : ℕ} (hd : 0 < d) (G : RegularGraph n d)
    {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 < c₂)
    (hbound : ∀ f : EuclideanSpace ℝ (Fin n),
      meanCLM n f = 0 →
      c₂ * (d : ℝ) ^ 2 * ‖G.walkCLM f‖ ^ 2 ≤ c₁ * ‖f‖ ^ 2) :
    spectralGap G ≤ Real.sqrt (c₁ / (c₂ * (d : ℝ) ^ 2)) := by
  unfold spectralGap
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro f
  -- Set g := f - Pf (mean-zero part)
  set g := f - meanCLM n f with hg_def
  -- (W - P)f = Wg since WP = P
  have hWP := walkCLM_comp_meanCLM G hd f
  have hWPg : (G.walkCLM - meanCLM n) f = G.walkCLM g := by
    simp only [ContinuousLinearMap.sub_apply, hg_def, map_sub, hWP]
  rw [hWPg]
  -- g is mean-zero
  have hg_mean : meanCLM n g = 0 := by
    rw [hg_def, map_sub]
    change (meanCLM n) f - (meanCLM n * meanCLM n) f = 0
    rw [meanCLM_idempotent, sub_self]
  -- Apply the walk bound to g
  have hbg := hbound g hg_mean
  -- We need ‖Wg‖ ≤ √(c₁/(c₂d²)) · ‖g‖
  -- From hbg: c₂d² · ‖Wg‖² ≤ c₁ · ‖g‖²
  have hcd_pos : 0 < c₂ * (d : ℝ) ^ 2 := by positivity
  -- ‖Wg‖² ≤ (c₁/(c₂d²)) · ‖g‖²
  have hsq : ‖G.walkCLM g‖ ^ 2 ≤ c₁ / (c₂ * (d : ℝ) ^ 2) * ‖g‖ ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hcd_pos]
    linarith
  -- Take square roots
  have hsqrt : ‖G.walkCLM g‖ ≤ Real.sqrt (c₁ / (c₂ * (d : ℝ) ^ 2)) * ‖g‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (G.walkCLM g)),
        ← Real.sqrt_sq (norm_nonneg g), ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hsq
  -- Chain with ‖g‖ = ‖f - Pf‖ ≤ ‖f‖
  calc ‖G.walkCLM g‖
      ≤ Real.sqrt (c₁ / (c₂ * (d : ℝ) ^ 2)) * ‖g‖ := hsqrt
    _ ≤ Real.sqrt (c₁ / (c₂ * (d : ℝ) ^ 2)) * ‖f‖ := by
        apply mul_le_mul_of_nonneg_left (norm_sub_meanCLM_le n f) (Real.sqrt_nonneg _)


/-! **Coefficient arithmetic** -/

/-- If `c₁ · βd² ≤ c₂ · βn²` then `√(c₁/(c₂·d²)) ≤ βn/(βd·d)`.

    This converts a quadratic walk bound with integer coefficients to
    a clean rational spectral gap bound. -/
theorem sqrt_coeff_le_frac
    {c₁ c₂ : ℝ} {d βn βd : ℕ}
    (hc₂ : 0 < c₂) (hd : 0 < d) (hβd : 0 < βd)
    (hβ : c₁ * (βd : ℝ) ^ 2 ≤ c₂ * (βn : ℝ) ^ 2) :
    Real.sqrt (c₁ / (c₂ * (d : ℝ) ^ 2)) ≤ ↑βn / (↑βd * ↑d) := by
  have hβd_pos : (0 : ℝ) < βd := Nat.cast_pos.mpr hβd
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ ↑βn / (↑βd * ↑d))]
  apply Real.sqrt_le_sqrt
  -- Goal: c₁ / (c₂ · d²) ≤ (βn / (βd · d))²
  rw [div_pow, mul_pow]
  -- Goal: c₁ / (c₂ · d²) ≤ βn² / (βd² · d²)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hβ (sq_nonneg (d : ℝ))]
