/-
  # Complete Graph and Its Spectral Gap

  The complete graph K_{n+1} as an n-regular graph via `Fin.succAbove`,
  and the proof that λ(K_{n+1}) = 1/n.
-/

import AKS.Graph.Regular

open Matrix BigOperators Finset


/-! **Complete Graph** -/

/-- Rotation map for the complete graph K_{n+1}: the i-th neighbor of v is
    obtained by skipping v in the enumeration, using `Fin.succAbove`.
    The reverse port is `Fin.predAbove`. -/
private def complete_rot {n : ℕ}
    (p : Fin (n + 1) × Fin n) : Fin (n + 1) × Fin n :=
  (p.1.succAbove p.2, p.2.predAbove p.1)

private theorem complete_rot_involution {n : ℕ}
    (p : Fin (n + 1) × Fin n) :
    complete_rot (complete_rot p) = p := by
  simp only [complete_rot, Fin.succAbove_succAbove_predAbove,
    Fin.predAbove_predAbove_succAbove, Prod.mk.eta]

/-- The complete graph on `n + 1` vertices as a regular graph.
    K_{n+1} is n-regular. λ(K_{n+1}) = 1/n. -/
def completeGraph (n : ℕ) : RegularGraph (n + 1) n where
  rot := complete_rot
  rot_involution := complete_rot_involution

/-- The neighbor function of the complete graph is `succAbove`. -/
private theorem completeGraph_neighbor {n : ℕ} (v : Fin (n + 1)) (i : Fin n) :
    (completeGraph n).neighbor v i = v.succAbove i := rfl

/-- For the complete graph, the walk operator gives the average over all
    *other* vertices: `(Wf)(v) = ((∑ f) - f v) / n`. -/
private theorem walkCLM_completeGraph_apply {n : ℕ}
    (f : EuclideanSpace ℝ (Fin (n + 1))) (v : Fin (n + 1)) :
    (completeGraph n).walkCLM f v = ((∑ j, f j) - f v) / ↑n := by
  simp only [RegularGraph.walkCLM_apply, completeGraph_neighbor]
  congr 1
  have := Fin.sum_univ_succAbove (fun j ↦ f j) v
  linarith

/-- The CLM operator identity for the complete graph:
    `W - P = -(1/n) • (1 - P)` where W = walkCLM, P = meanCLM. -/
private theorem walkCLM_sub_meanCLM_completeGraph {n : ℕ} (hn : n ≥ 1) :
    (completeGraph n).walkCLM - meanCLM (n + 1) =
    (-(1 / (n : ℝ))) • (1 - meanCLM (n + 1)) := by
  refine ContinuousLinearMap.ext (fun f ↦ ?_)
  apply PiLp.ext; intro v
  show (completeGraph n).walkCLM f v - meanCLM (n + 1) f v =
    -(1 / (↑n : ℝ)) * (f v - meanCLM (n + 1) f v)
  rw [walkCLM_completeGraph_apply, meanCLM_apply]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : (↑n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- The norm of the orthogonal complement projection `1 - meanCLM` is 1
    (for n ≥ 2 vertices, i.e., non-constant functions exist). -/
private theorem norm_one_sub_meanCLM {n : ℕ} (hn : n ≥ 2) :
    ‖1 - meanCLM n‖ = 1 := by
  set T := 1 - meanCLM n
  apply le_antisymm
  · -- Upper bound: ‖Tf‖ ≤ ‖f‖ (1 - P is a contraction)
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f; rw [one_mul]
    show ‖f - meanCLM n f‖ ≤ ‖f‖
    exact norm_sub_meanCLM_le n f
  · -- Lower bound: exhibit f with Pf = 0, f ≠ 0, so ‖Tf‖ = ‖f‖
    -- Build test vector: 1 at index 0, -1 at index 1, 0 elsewhere
    set v0 : Fin n := ⟨0, by omega⟩
    set v1 : Fin n := ⟨1, by omega⟩
    let g : Fin n → ℝ := fun i ↦ if i = v0 then 1 else if i = v1 then -1 else 0
    let f : EuclideanSpace ℝ (Fin n) := (WithLp.equiv 2 _).symm g
    have hfv : ∀ i, f i = g i := fun _ ↦ rfl
    have hgsum : ∑ i, g i = 0 := by
      have hne : v0 ≠ v1 := by simp [Fin.ext_iff, v0, v1]
      have hsplit : ∀ i : Fin n, g i = (if i = v0 then (1:ℝ) else 0) +
                                        (if i = v1 then (-1:ℝ) else 0) := by
        intro i; simp only [g]; split_ifs with h1 h2
        · exact absurd (h1.symm.trans h2) hne
        · ring
        · ring
        · ring
      simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true, add_neg_cancel]
    have hfsum : ∑ i, f i = 0 := by simp_rw [hfv]; exact hgsum
    have hf_ne : f ≠ 0 := by
      intro h
      have : g v0 = 0 := by
        calc g v0 = f v0 := (hfv v0).symm
          _ = (0 : EuclideanSpace ℝ (Fin n)) v0 := by rw [h]
          _ = 0 := rfl
      simp [g] at this
    -- T f = f since Pf = 0
    have hTf : T f = f := by
      apply PiLp.ext; intro v
      show f v - meanCLM n f v = f v
      rw [meanCLM_apply, hfsum, zero_div, sub_zero]
    -- From ‖Tf‖ = ‖f‖ and T.le_opNorm: ‖f‖ ≤ ‖T‖ * ‖f‖
    have h_le := T.le_opNorm f
    rw [hTf] at h_le
    exact le_of_mul_le_mul_right (by rw [one_mul]; exact h_le) (norm_pos_iff.mpr hf_ne)

/-- The spectral gap of the complete graph: λ(K_{n+1}) = 1/n. -/
theorem spectralGap_complete (n : ℕ) (hn : n ≥ 1) :
    spectralGap (completeGraph n) = 1 / (n : ℝ) := by
  unfold spectralGap
  rw [walkCLM_sub_meanCLM_completeGraph hn, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_div, abs_one, Nat.abs_cast,
    norm_one_sub_meanCLM (show n + 1 ≥ 2 by omega), mul_one]
