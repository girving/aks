/-
  # Expander Mixing Lemma

  The spectral gap controls edge distribution in regular graphs.
  This is the link between spectral and combinatorial expansion.

  The proof decomposes into five sublemmas:
  1. Indicator vectors and their norms
  2. Walk operator on indicators = port counting
  3. Mean projection on indicators = expected count
  4. Abstract Cauchy-Schwarz + operator norm bound
  5. Final assembly
-/

import AKS.Graph.Regular

open Matrix BigOperators Finset


/-! **Indicator Vectors** -/

/-- Indicator vector of a vertex set in `EuclideanSpace`:
    `(indicatorVec S) v = if v ∈ S then 1 else 0`. -/
noncomputable def indicatorVec {n : ℕ} (S : Finset (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 _).symm (fun v ↦ if v ∈ S then (1 : ℝ) else 0)

@[simp]
theorem indicatorVec_apply {n : ℕ} (S : Finset (Fin n)) (v : Fin n) :
    indicatorVec S v = if v ∈ S then 1 else 0 := rfl

private theorem sum_indicatorVec {n : ℕ} (S : Finset (Fin n)) :
    (∑ v : Fin n, if v ∈ S then (1 : ℝ) else 0) = ↑S.card := by
  rw [Finset.sum_boole]
  congr 1; congr 1; ext; simp

theorem norm_sq_indicatorVec {n : ℕ} (S : Finset (Fin n)) :
    ‖indicatorVec S‖ ^ 2 = ↑S.card := by
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs, indicatorVec_apply]
  have h : ∀ v : Fin n, (if v ∈ S then (1 : ℝ) else 0) ^ 2 =
      if v ∈ S then 1 else 0 := by
    intro v; split_ifs <;> simp
  simp_rw [h]
  exact sum_indicatorVec S

theorem norm_indicatorVec {n : ℕ} (S : Finset (Fin n)) :
    ‖indicatorVec S‖ = Real.sqrt ↑S.card := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_indicatorVec]


/-! **Walk Operator on Indicators** -/

/-- The inner product of an indicator vector with the walk operator applied
    to another indicator equals the normalized port count from `S` to `T`. -/
theorem inner_indicatorVec_walkCLM {n d : ℕ} (G : RegularGraph n d)
    (S T : Finset (Fin n)) :
    @inner ℝ _ _ (indicatorVec S) (G.walkCLM (indicatorVec T)) =
    (↑(∑ v ∈ S, (Finset.univ.filter
        (fun i : Fin d ↦ G.neighbor v i ∈ T)).card) : ℝ) / ↑d := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    RegularGraph.walkCLM_apply, indicatorVec_apply]
  -- Factor out /d from each term: simp normalizes to (b/d)*a; rewrite to b*a/d then factor
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  -- Convert indicator multiplication: x * (if p then 1 else 0) = if p then x else 0
  simp_rw [mul_ite, mul_one, mul_zero]
  -- Restrict sum to S via sum_filter
  rw [← Finset.sum_filter]
  have huniv : Finset.univ.filter (· ∈ S) = S := by ext; simp
  rw [huniv]
  -- Convert inner sums to card via sum_boole, then push cast
  simp_rw [Finset.sum_boole]
  push_cast; rfl


/-! **Mean Projection on Indicators** -/

/-- The inner product of an indicator vector with the mean projection applied
    to another indicator equals the expected count `|S|·|T|/n`. -/
theorem inner_indicatorVec_meanCLM {n : ℕ}
    (S T : Finset (Fin n)) :
    @inner ℝ _ _ (indicatorVec S) (meanCLM n (indicatorVec T)) =
    ↑S.card * ↑T.card / ↑n := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    meanCLM_apply, indicatorVec_apply]
  -- The mean of indicatorVec T is T.card / n, constant in v
  simp_rw [sum_indicatorVec T]
  -- Factor constant out of sum: ∑ v, (T.card/n) * ind_S(v) = (T.card/n) * (∑ v, ind_S(v))
  rw [← Finset.mul_sum, sum_indicatorVec S]
  ring


/-! **Abstract Cauchy-Schwarz Bound** -/

/-- The inner product with `W - P` is bounded by the spectral gap
    times the norms of both vectors. -/
theorem abs_inner_sub_le_spectralGap {n d : ℕ} (G : RegularGraph n d)
    (f g : EuclideanSpace ℝ (Fin n)) :
    |@inner ℝ _ _ f ((G.walkCLM - meanCLM n) g)| ≤
    spectralGap G * ‖f‖ * ‖g‖ := by
  calc |@inner ℝ _ _ f ((G.walkCLM - meanCLM n) g)|
      ≤ ‖f‖ * ‖(G.walkCLM - meanCLM n) g‖ := abs_real_inner_le_norm f _
    _ ≤ ‖f‖ * (‖G.walkCLM - meanCLM n‖ * ‖g‖) := by
        apply mul_le_mul_of_nonneg_left
          ((G.walkCLM - meanCLM n).le_opNorm g) (norm_nonneg _)
    _ = spectralGap G * ‖f‖ * ‖g‖ := by unfold spectralGap; ring


/-! **Expander Mixing Lemma** -/

/-- The Expander Mixing Lemma: the spectral gap controls edge
    distribution. For any two vertex sets S, T ⊆ V:

      |e(S,T)/d - |S|·|T|/n| ≤ λ(G) · √(|S|·|T|)

    where `e(S,T)` counts edges (with port multiplicity) from `S` to `T`.
    This is the link between spectral and combinatorial expansion. -/
theorem expander_mixing_lemma {n d : ℕ} (G : RegularGraph n d)
    (S T : Finset (Fin n)) :
    |(↑(∑ v ∈ S, (Finset.univ.filter
        (fun i : Fin d ↦ G.neighbor v i ∈ T)).card) : ℝ) / ↑d
      - ↑S.card * ↑T.card / ↑n|
    ≤ spectralGap G * Real.sqrt (↑S.card * ↑T.card) := by
  -- Rewrite the difference as ⟨1_S, (W - P)(1_T)⟩
  have key : (↑(∑ v ∈ S, (Finset.univ.filter
        (fun i : Fin d ↦ G.neighbor v i ∈ T)).card) : ℝ) / ↑d
      - ↑S.card * ↑T.card / ↑n =
      @inner ℝ _ _ (indicatorVec S)
        ((G.walkCLM - meanCLM n) (indicatorVec T)) := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right,
      inner_indicatorVec_walkCLM, inner_indicatorVec_meanCLM]
  rw [key]
  -- Apply Cauchy-Schwarz + operator norm, then substitute indicator norms
  calc |@inner ℝ _ _ (indicatorVec S)
          ((G.walkCLM - meanCLM n) (indicatorVec T))|
      ≤ spectralGap G * ‖indicatorVec S‖ * ‖indicatorVec T‖ :=
        abs_inner_sub_le_spectralGap G _ _
    _ = spectralGap G * Real.sqrt (↑S.card * ↑T.card) := by
        rw [norm_indicatorVec, norm_indicatorVec, mul_assoc,
          ← Real.sqrt_mul (Nat.cast_nonneg _)]
