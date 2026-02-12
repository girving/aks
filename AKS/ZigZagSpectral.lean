/-
  # Zig-Zag Operator Properties

  Algebraic identities and spectral bounds for the zig-zag product
  operators defined in `ZigZagOperators.lean`:
  - `Q` = cluster mean projection
  - `B` = within-cluster walk
  - `Σ` = step permutation

  These properties feed into the abstract RVW bound in `RVWBound.lean`
  to prove `zigzag_spectral_bound` in `ZigZag.lean`.
-/

import AKS.ZigZagOperators

open Matrix BigOperators Finset


/-! **Cluster Mean Properties** -/

/-- The cluster mean projection is idempotent: `Q * Q = Q`. -/
theorem clusterMeanCLM_idempotent {n₁ d₁ : ℕ} (hd₁ : 0 < d₁) :
    (clusterMeanCLM hd₁ : EuclideanSpace ℝ (Fin (n₁ * d₁)) →L[ℝ] _) *
    clusterMeanCLM hd₁ = clusterMeanCLM hd₁ := by
  ext f vk
  simp only [ContinuousLinearMap.mul_apply, clusterMeanCLM_apply]
  simp
  field_simp

/-- The cluster mean projection is self-adjoint: `Q* = Q`. -/
theorem clusterMeanCLM_isSelfAdjoint {n₁ d₁ : ℕ} (hd₁ : 0 < d₁) :
    IsSelfAdjoint (clusterMeanCLM hd₁ : EuclideanSpace ℝ (Fin (n₁ * d₁)) →L[ℝ] _) := by
  sorry


/-! **Within-Cluster Walk Properties** -/

/-- The within-cluster walk operator is self-adjoint: `B* = B`. -/
theorem withinClusterCLM_isSelfAdjoint {n₁ d₁ d₂ : ℕ}
    (G₂ : RegularGraph d₁ d₂) (hd₁ : 0 < d₁) :
    IsSelfAdjoint (withinClusterCLM (n₁ := n₁) G₂ hd₁) := by
  sorry

/-- The within-cluster walk preserves the cluster mean: `B * Q = Q`.
    Walking within a cluster preserves the cluster average because
    the walk operator of a regular graph preserves constants. -/
theorem withinCluster_comp_clusterMean {n₁ d₁ d₂ : ℕ}
    (G₂ : RegularGraph d₁ d₂) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    withinClusterCLM (n₁ := n₁) G₂ hd₁ * clusterMeanCLM hd₁ =
    clusterMeanCLM hd₁ := by
  sorry

/-- The cluster mean absorbs the within-cluster walk: `Q * B = Q`.
    The cluster mean of the walked function equals the cluster mean
    of the original (double-counting via G₂'s rotation bijection). -/
theorem clusterMean_comp_withinCluster {n₁ d₁ d₂ : ℕ}
    (G₂ : RegularGraph d₁ d₂) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    clusterMeanCLM hd₁ * withinClusterCLM (n₁ := n₁) G₂ hd₁ =
    clusterMeanCLM hd₁ := by
  sorry

/-- The within-cluster walk is a contraction: `‖B‖ ≤ 1`. -/
theorem withinClusterCLM_norm_le_one {n₁ d₁ d₂ : ℕ}
    (G₂ : RegularGraph d₁ d₂) (hd₁ : 0 < d₁) :
    ‖withinClusterCLM (n₁ := n₁) G₂ hd₁‖ ≤ 1 := by
  sorry


/-! **Step Permutation Properties** -/

/-- The step permutation is an involution: `Σ * Σ = 1`. -/
theorem stepPermCLM_sq_eq_one {n₁ d₁ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (hd₁ : 0 < d₁) :
    stepPermCLM G₁ hd₁ * stepPermCLM G₁ hd₁ =
    (1 : EuclideanSpace ℝ (Fin (n₁ * d₁)) →L[ℝ] _) := by
  sorry

/-- The step permutation is self-adjoint: `Σ* = Σ`.
    This follows from `Σ` being a permutation operator (hence isometry)
    combined with `Σ² = 1` (so `Σ* = Σ⁻¹ = Σ`). -/
theorem stepPermCLM_isSelfAdjoint {n₁ d₁ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (hd₁ : 0 < d₁) :
    IsSelfAdjoint (stepPermCLM G₁ hd₁) := by
  sorry


/-! **Spectral Bounds** -/

/-- **Tilde contraction:** The within-cluster walk contracts by `spectralGap G₂`
    on the orthogonal complement of cluster means.

    `B(I - Q)` acts block-diagonally: within each cluster `v`, it equals
    `W_{G₂} - P_{d₁}` (the walk minus the cluster mean), which has norm
    `spectralGap G₂`. -/
theorem withinCluster_tilde_contraction {n₁ d₁ d₂ : ℕ}
    (G₂ : RegularGraph d₁ d₂) (hd₁ : 0 < d₁) :
    ‖withinClusterCLM (n₁ := n₁) G₂ hd₁ *
     (1 - clusterMeanCLM hd₁)‖ ≤ spectralGap G₂ := by
  sorry

/-- **Hat block spectral gap:** `Q · Σ · Q` restricted to the hat subspace
    acts like `W_{G₁}` lifted to the product space, so its distance from
    the global mean projection is bounded by `spectralGap G₁`.

    More precisely: `‖QΣQ - P‖ ≤ spectralGap G₁` where `P = meanCLM (n₁ * d₁)`. -/
theorem hat_block_norm {n₁ d₁ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (hd₁ : 0 < d₁) :
    ‖clusterMeanCLM (n₁ := n₁) hd₁ * stepPermCLM G₁ hd₁ * clusterMeanCLM hd₁ -
     (meanCLM (n₁ * d₁) : EuclideanSpace ℝ (Fin (n₁ * d₁)) →L[ℝ] _)‖ ≤
    spectralGap G₁ := by
  sorry


/-! **Global Mean Decomposition** -/

/-- The global mean on `ℝ^{n₁·d₁}` factors through the cluster mean.
    Averaging globally = taking cluster means, then averaging those.

    This establishes the relationship `P ≤ Q` (as projections) needed
    for the abstract RVW bound. -/
theorem meanCLM_eq_clusterMean_comp {n₁ d₁ : ℕ} (hd₁ : 0 < d₁) :
    (meanCLM (n₁ * d₁) : EuclideanSpace ℝ (Fin (n₁ * d₁)) →L[ℝ] _) *
    clusterMeanCLM hd₁ =
    meanCLM (n₁ * d₁) := by
  sorry

theorem clusterMean_comp_meanCLM {n₁ d₁ : ℕ} (hd₁ : 0 < d₁) :
    clusterMeanCLM (n₁ := n₁) hd₁ *
    (meanCLM (n₁ * d₁) : EuclideanSpace ℝ (Fin (n₁ * d₁)) →L[ℝ] _) =
    meanCLM (n₁ * d₁) := by
  sorry
