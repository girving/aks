/-
  # Tanner's Vertex Expansion Bound

  For a d-regular graph G with spectral gap ≤ β, Tanner's bound gives:
  |N(T)| ≥ |T|·n / (|T| + β²·(n - |T|))

  This is strictly stronger than the expander mixing lemma for small sets
  and is the key ingredient for the expander → halver bridge.

  The proof combines Cauchy-Schwarz on the codegree distribution with
  the spectral gap operator norm bound via orthogonal decomposition.
-/

import AKS.Mixing
import AKS.Square

open Finset BigOperators


/-! **Neighborhood and Codegree** -/

/-- The neighborhood of a vertex set T: all vertices with at least one
    neighbor in T. -/
def RegularGraph.neighborSet {n d : ℕ} (G : RegularGraph n d)
    (T : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ∃ p : Fin d, G.neighbor v p ∈ T)

/-- The codegree of a vertex v with respect to T: the number of ports
    leading to T. -/
def RegularGraph.codeg {n d : ℕ} (G : RegularGraph n d)
    (T : Finset (Fin n)) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun p : Fin d => G.neighbor v p ∈ T)).card

/-- Codegree is zero outside the neighborhood. -/
theorem RegularGraph.codeg_eq_zero_of_not_mem {n d : ℕ} (G : RegularGraph n d)
    (T : Finset (Fin n)) (v : Fin n) (hv : v ∉ G.neighborSet T) :
    G.codeg T v = 0 := by
  simp only [neighborSet, Finset.mem_filter, Finset.mem_univ, true_and,
    not_exists] at hv
  simp only [codeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _; exact hv p


/-! **Codegree Sum** -/

/-- The sum of codegrees equals d·|T|. -/
theorem RegularGraph.codeg_sum {n d : ℕ} (G : RegularGraph n d)
    (T : Finset (Fin n)) :
    ∑ v, G.codeg T v = d * T.card := by
  -- Lift to ℝ where sum_neighbor_eq is available
  suffices h : (∑ v, (G.codeg T v : ℝ)) = (d : ℝ) * ↑T.card by exact_mod_cast h
  -- Express each codeg as a sum of indicators
  have hc : ∀ v : Fin n, (G.codeg T v : ℝ) =
      ∑ i : Fin d, if G.neighbor v i ∈ T then (1 : ℝ) else 0 := by
    intro v; simp only [codeg, Finset.sum_boole]
  simp_rw [hc]
  -- Apply rotation bijection: ∑ v ∑ i, f(nbr(v,i)) = ∑ v ∑ i, f(v)
  rw [G.sum_neighbor_eq (fun v ↦ if v ∈ T then (1 : ℝ) else 0)]
  -- Simplify: ∑ v, d * [v ∈ T] = d * |T|
  simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]


/-! **Walk Operator and Codegree** -/

/-- The walk operator applied to an indicator vector gives codeg/d at each vertex. -/
theorem RegularGraph.walkCLM_indicatorVec {n d : ℕ} (G : RegularGraph n d)
    (T : Finset (Fin n)) (v : Fin n) :
    G.walkCLM (indicatorVec T) v = (G.codeg T v : ℝ) / d := by
  simp only [RegularGraph.walkCLM_apply, indicatorVec_apply, codeg]
  congr 1
  simp only [Finset.sum_boole]

/-- ‖W·1_T‖² = (∑ codeg(v)²) / d². -/
theorem RegularGraph.norm_sq_walkCLM_indicatorVec {n d : ℕ} (G : RegularGraph n d)
    (T : Finset (Fin n)) :
    ‖G.walkCLM (indicatorVec T)‖ ^ 2 =
    (∑ v, (G.codeg T v : ℝ) ^ 2) / (d : ℝ) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs, G.walkCLM_indicatorVec T]
  simp_rw [div_pow]
  rw [← Finset.sum_div]


/-! **Orthogonal Decomposition for ‖W·1_T‖²** -/

/-- The mean projection applied to an indicator gives constant |T|/n. -/
private theorem meanCLM_indicatorVec_eq {n : ℕ} (T : Finset (Fin n)) (v : Fin n) :
    meanCLM n (indicatorVec T) v = (↑T.card : ℝ) / ↑n := by
  simp only [meanCLM_apply]
  congr 1
  simp_rw [indicatorVec_apply]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- ‖P(1_T)‖² = |T|²/n. -/
private theorem norm_sq_meanCLM_indicatorVec {n : ℕ} (hn : 0 < n) (T : Finset (Fin n)) :
    ‖meanCLM n (indicatorVec T)‖ ^ 2 = (↑T.card) ^ 2 / ↑n := by
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs, meanCLM_indicatorVec_eq T, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow]
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  field_simp

/-- The sum ∑ v, indicatorVec T v = ↑T.card (as ℝ). -/
private theorem sum_indicatorVec_eq {n : ℕ} (T : Finset (Fin n)) :
    ∑ v : Fin n, indicatorVec T v = (↑T.card : ℝ) := by
  simp_rw [indicatorVec_apply, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Finset.univ_inter]

/-- Key bound: ‖W·1_T‖² ≤ |T|·(|T| + β²·(n - |T|)) / n.
    Uses orthogonal decomposition W(1_T) = P(1_T) + (W-P)(1_T),
    Pythagorean theorem (since P*(W-P) = 0), and operator norm bound. -/
theorem norm_sq_walk_indicatorVec_le {n d : ℕ} (G : RegularGraph n d)
    (hd : 0 < d) (hn : 0 < n)
    (T : Finset (Fin n)) (β : ℝ) (hβ : spectralGap G ≤ β) :
    ‖G.walkCLM (indicatorVec T)‖ ^ 2 ≤
    ↑T.card * (↑T.card + β ^ 2 * (↑n - ↑T.card)) / ↑n := by
  set f := indicatorVec T
  have hn_r : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_r
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hd)
  -- Abbreviations for proved helper results
  have hPf_sq := norm_sq_meanCLM_indicatorVec hn T
  -- Sum of W(f) over all vertices = |T|
  have hsum_Wf : ∑ v, G.walkCLM f v = (↑T.card : ℝ) := by
    simp only [RegularGraph.walkCLM_apply]
    rw [← Finset.sum_div, G.sum_neighbor_eq (fun v ↦ f v)]
    simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, mul_div_cancel_left₀ _ hd_ne]
    exact sum_indicatorVec_eq T
  -- Sum of P(f) over all vertices = |T|
  have hsum_Pf : ∑ v, meanCLM n f v = (↑T.card : ℝ) := by
    simp only [meanCLM_apply]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    exact sum_indicatorVec_eq T
  -- P(W-P) = 0 (from PW=P and P²=P)
  have hPA : meanCLM n * (G.walkCLM - meanCLM n) = (0 : _ →L[ℝ] _) := by
    rw [mul_sub, meanCLM_comp_walkCLM G hd, meanCLM_idempotent, sub_self]
  -- Orthogonality helper: P applied to (W-P)f is zero
  have hPA_f : meanCLM n ((G.walkCLM - meanCLM n) f) = 0 := by
    show (meanCLM n * (G.walkCLM - meanCLM n)) f = 0
    rw [hPA, ContinuousLinearMap.zero_apply]
  -- Orthogonality: ⟨Pf, (W-P)f⟩ = 0 (via P self-adjoint + P(W-P) = 0)
  have hortho : @inner ℝ _ _ (meanCLM n f) ((G.walkCLM - meanCLM n) f) = 0 := by
    have h1 := ContinuousLinearMap.adjoint_inner_left
      (meanCLM n : EuclideanSpace ℝ (Fin n) →L[ℝ] _) f ((G.walkCLM - meanCLM n) f)
    rw [(meanCLM_isSelfAdjoint n).adjoint_eq] at h1
    rw [real_inner_comm, ← h1, hPA_f, inner_zero_left]
  -- Decompose: Wf = Pf + (W-P)f
  have hdecomp : G.walkCLM f = meanCLM n f + (G.walkCLM - meanCLM n) f := by
    simp only [ContinuousLinearMap.sub_apply]; abel
  -- Pythagorean: ‖Wf‖² = ‖Pf‖² + ‖(W-P)f‖²
  have hpyth : ‖G.walkCLM f‖ ^ 2 =
      ‖meanCLM n f‖ ^ 2 + ‖(G.walkCLM - meanCLM n) f‖ ^ 2 := by
    rw [hdecomp, norm_add_sq_real, hortho, mul_zero, add_zero]
  -- (W-P)(Pf) = 0 (from WP=P and P²=P)
  have hAPf : (G.walkCLM - meanCLM n) (meanCLM n f) = 0 := by
    simp only [ContinuousLinearMap.sub_apply]
    rw [walkCLM_comp_meanCLM G hd f]
    have : meanCLM n (meanCLM n f) = meanCLM n f := by
      show (meanCLM n * meanCLM n) f = meanCLM n f; rw [meanCLM_idempotent]
    rw [this, sub_self]
  -- (W-P)(f) = (W-P)(f - Pf) since (W-P)(Pf) = 0
  have hAfact : (G.walkCLM - meanCLM n) f =
      (G.walkCLM - meanCLM n) (f - meanCLM n f) := by
    rw [map_sub, hAPf, sub_zero]
  -- ‖(W-P)f‖ ≤ β · ‖f - Pf‖ (operator norm bound)
  have hAnorm : ‖(G.walkCLM - meanCLM n) f‖ ≤ β * ‖f - meanCLM n f‖ := by
    calc ‖(G.walkCLM - meanCLM n) f‖
        = ‖(G.walkCLM - meanCLM n) (f - meanCLM n f)‖ := by rw [hAfact]
      _ ≤ ‖(G.walkCLM - meanCLM n : _ →L[ℝ] _)‖ * ‖f - meanCLM n f‖ :=
          (G.walkCLM - meanCLM n).le_opNorm (f - meanCLM n f)
      _ ≤ β * ‖f - meanCLM n f‖ := mul_le_mul_of_nonneg_right hβ (norm_nonneg _)
  -- ‖f - Pf‖² = |T| - |T|²/n (Pythagorean decomposition of f)
  have hfPf_sq : ‖f - meanCLM n f‖ ^ 2 = ↑T.card - (↑T.card) ^ 2 / ↑n := by
    -- ⟨Pf, f-Pf⟩ = 0 via P self-adjoint + P(f-Pf) = 0
    have hP_proj : meanCLM n (f - meanCLM n f) = 0 := by
      rw [map_sub]; show meanCLM n f - (meanCLM n * meanCLM n) f = 0
      rw [meanCLM_idempotent, sub_self]
    have hortho2 : @inner ℝ _ _ (meanCLM n f) (f - meanCLM n f) = 0 := by
      have h1 := ContinuousLinearMap.adjoint_inner_left
        (meanCLM n : EuclideanSpace ℝ (Fin n) →L[ℝ] _) f (f - meanCLM n f)
      rw [(meanCLM_isSelfAdjoint n).adjoint_eq] at h1
      rw [real_inner_comm, ← h1, hP_proj, inner_zero_left]
    have hf_decomp : f = meanCLM n f + (f - meanCLM n f) := by abel
    have : ‖f‖ ^ 2 = ‖meanCLM n f‖ ^ 2 + ‖f - meanCLM n f‖ ^ 2 := by
      conv_lhs => rw [hf_decomp]
      rw [norm_add_sq_real, hortho2, mul_zero, add_zero]
    rw [norm_sq_indicatorVec] at this; linarith
  -- ‖(W-P)f‖² ≤ β²·(|T| - |T|²/n)
  have hAf_sq : ‖(G.walkCLM - meanCLM n) f‖ ^ 2 ≤
      β ^ 2 * (↑T.card - (↑T.card) ^ 2 / ↑n) := by
    calc ‖(G.walkCLM - meanCLM n) f‖ ^ 2
        ≤ (β * ‖f - meanCLM n f‖) ^ 2 := by
          apply sq_le_sq'
          · linarith [norm_nonneg ((G.walkCLM - meanCLM n) f),
              mul_nonneg (le_trans (spectralGap_nonneg G) hβ) (norm_nonneg (f - meanCLM n f))]
          · exact hAnorm
      _ = β ^ 2 * ‖f - meanCLM n f‖ ^ 2 := by ring
      _ = β ^ 2 * (↑T.card - (↑T.card) ^ 2 / ↑n) := by rw [hfPf_sq]
  -- Final combination
  calc ‖G.walkCLM f‖ ^ 2
      = ‖meanCLM n f‖ ^ 2 + ‖(G.walkCLM - meanCLM n) f‖ ^ 2 := hpyth
    _ ≤ (↑T.card) ^ 2 / ↑n + β ^ 2 * (↑T.card - (↑T.card) ^ 2 / ↑n) := by
        linarith [hPf_sq, hAf_sq]
    _ = ↑T.card * (↑T.card + β ^ 2 * (↑n - ↑T.card)) / ↑n := by
        field_simp


/-! **Tanner's Bound** -/

/-- Tanner's vertex expansion bound: for any T ⊆ V in a d-regular graph
    with spectral gap ≤ β,
    |N(T)| · (|T| + β²·(n - |T|)) ≥ |T| · n. -/
theorem tanner_bound {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d) (hn : 0 < n)
    (β : ℝ) (hβ : spectralGap G ≤ β) (_hβ_nn : 0 ≤ β)
    (T : Finset (Fin n)) (hT : 0 < T.card) :
    (T.card : ℝ) * ↑n ≤ ↑(G.neighborSet T).card * (↑T.card + β ^ 2 * (↑n - ↑T.card)) := by
  set N := G.neighborSet T
  have hd_r : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hn_r : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hT_r : (0 : ℝ) < ↑T.card := Nat.cast_pos.mpr hT
  -- Step 1: ∑_{v ∈ N(T)} codeg(v) = d * |T| (codeg=0 outside N(T))
  have hsum : ∑ v ∈ N, (G.codeg T v : ℝ) = (d : ℝ) * ↑T.card := by
    rw [Finset.sum_subset (Finset.subset_univ N) (fun v _ hv ↦ by
      simp only [Nat.cast_eq_zero]; exact G.codeg_eq_zero_of_not_mem T v hv)]
    exact_mod_cast G.codeg_sum T
  -- Step 2: Cauchy-Schwarz: (∑_{N} codeg)² ≤ |N| * ∑_{N} codeg²
  have cs := sq_sum_le_card_mul_sum_sq (s := N) (f := fun v ↦ (G.codeg T v : ℝ))
  rw [hsum] at cs
  -- Step 3: ∑_{N} codeg² ≤ ∑_V codeg²
  have hsumsq : ∑ v ∈ N, (G.codeg T v : ℝ) ^ 2 ≤
      ∑ v, (G.codeg T v : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ N)
      (fun _ _ _ ↦ sq_nonneg _)
  -- Step 4: ∑_V codeg² = d² * ‖W·1_T‖²
  have hcodeg_sq : ∑ v, (G.codeg T v : ℝ) ^ 2 =
      (d : ℝ) ^ 2 * ‖G.walkCLM (indicatorVec T)‖ ^ 2 := by
    rw [G.norm_sq_walkCLM_indicatorVec T, mul_div_cancel₀]
    exact pow_ne_zero 2 (ne_of_gt hd_r)
  -- Step 5: n * ‖W·1_T‖² ≤ |T|·(|T| + β²(n-|T|)) (norm bound, multiplied by n)
  have hnorm_nd : ↑n * ‖G.walkCLM (indicatorVec T)‖ ^ 2 ≤
      ↑T.card * (↑T.card + β ^ 2 * (↑n - ↑T.card)) := by
    have h := norm_sq_walk_indicatorVec_le G hd hn T β hβ
    have h' := (le_div_iff₀ hn_r).mp h
    linarith
  -- Chain: d²·|T|² ≤ |N|·d²·‖W 1_T‖² (from CS + subset + codeg identity)
  have hchain : (d : ℝ) ^ 2 * (↑T.card) ^ 2 ≤
      ↑N.card * ((d : ℝ) ^ 2 * ‖G.walkCLM (indicatorVec T)‖ ^ 2) := by
    calc (d : ℝ) ^ 2 * (↑T.card) ^ 2
        = ((d : ℝ) * ↑T.card) ^ 2 := by ring
      _ ≤ ↑N.card * ∑ v ∈ N, (G.codeg T v : ℝ) ^ 2 := cs
      _ ≤ ↑N.card * ∑ v, (G.codeg T v : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hsumsq (Nat.cast_nonneg _)
      _ = ↑N.card * ((d : ℝ) ^ 2 * ‖G.walkCLM (indicatorVec T)‖ ^ 2) := by
          rw [hcodeg_sq]
  -- Combined bound: d²·|T|²·n ≤ |N|·d²·|T|·(|T| + β²(n-|T|))
  have h_combined : (d : ℝ) ^ 2 * (↑T.card) ^ 2 * ↑n ≤
      ↑N.card * (d : ℝ) ^ 2 * ↑T.card * (↑T.card + β ^ 2 * (↑n - ↑T.card)) := by
    nlinarith [mul_le_mul_of_nonneg_right hchain (le_of_lt hn_r),
      mul_le_mul_of_nonneg_left hnorm_nd
        (mul_nonneg (Nat.cast_nonneg N.card) (le_of_lt (sq_pos_of_pos hd_r))),
      sq_nonneg ‖G.walkCLM (indicatorVec T)‖]
  -- Cancel d²·|T| (both positive): |T|·n ≤ |N|·(...)
  by_contra h; push_neg at h
  linarith [mul_lt_mul_of_pos_left h (mul_pos (sq_pos_of_pos hd_r) hT_r)]
