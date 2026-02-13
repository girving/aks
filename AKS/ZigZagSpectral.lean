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
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, clusterMeanCLM_apply]
  -- LHS: ∑ vk, g(vk) * ((∑ i, f(encode (cluster vk) i)) / d₁)
  -- RHS: ∑ vk, ((∑ i, g(encode (cluster vk) i)) / d₁) * f(vk)
  -- Both equal (1/d₁²) · ∑ vk, ∑ i, g(vk) * f(encode (cluster vk) i)
  --                    = (1/d₁²) · ∑ vk, ∑ i, f(vk) * g(encode (cluster vk) i)
  -- after reorganizing by cluster structure
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
  ext f vk
  simp only [ContinuousLinearMap.mul_apply, withinClusterCLM_apply,
             clusterMeanCLM_apply]
  -- LHS: (∑ j, (∑ i, f (encode (cluster (encode (cluster vk) (G₂.neighbor ...))) i)) / d₁) / d₂
  -- cluster (encode v k) = v, so all inner sums equal (∑ i, f (encode (cluster vk) i)) / d₁
  simp only [cluster_encode]
  -- Now: (∑ j, (∑ i, f (encode (cluster vk) i)) / d₁) / d₂
  rw [Finset.sum_const, Finset.card_fin]
  -- d₂ • x / d₂ = x, which converts to d₂ * x / d₂ = x
  simp
  field_simp

/-- The cluster mean absorbs the within-cluster walk: `Q * B = Q`.
    The cluster mean of the walked function equals the cluster mean
    of the original (double-counting via G₂'s rotation bijection). -/
theorem clusterMean_comp_withinCluster {n₁ d₁ d₂ : ℕ}
    (G₂ : RegularGraph d₁ d₂) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    clusterMeanCLM hd₁ * withinClusterCLM (n₁ := n₁) G₂ hd₁ =
    clusterMeanCLM hd₁ := by
  ext f vk
  simp only [ContinuousLinearMap.mul_apply, clusterMeanCLM_apply,
             withinClusterCLM_apply, cluster_encode, port_encode]
  -- LHS: (∑ i, (∑ j, f (encode (cluster vk) (G₂.neighbor i j))) / d₂) / d₁
  -- RHS: (∑ i, f (encode (cluster vk) i)) / d₁
  -- Use rotation bijection to show inner sums equal full sum
  have h := RegularGraph.sum_neighbor_eq G₂ (fun k => f.ofLp (encode (cluster hd₁ vk) k))
  calc (∑ i, (∑ j, f.ofLp (encode (cluster hd₁ vk) (G₂.neighbor i j))) / ↑d₂) / ↑d₁
      = (∑ i, (∑ j, f.ofLp (encode (cluster hd₁ vk) (G₂.neighbor i j)))) / ↑d₂ / ↑d₁ := by rw [← Finset.sum_div]
    _ = (∑ i, ∑ _j, f.ofLp (encode (cluster hd₁ vk) i)) / ↑d₂ / ↑d₁ := by rw [h]
    _ = (∑ i, d₂ • f.ofLp (encode (cluster hd₁ vk) i)) / ↑d₂ / ↑d₁ := by simp [Finset.sum_const]
    _ = (d₂ • ∑ i, f.ofLp (encode (cluster hd₁ vk) i)) / ↑d₂ / ↑d₁ := by rw [Finset.smul_sum]
    _ = (∑ i, f.ofLp (encode (cluster hd₁ vk) i)) / ↑d₁ := by simp; field_simp

/-- The within-cluster walk is a contraction: `‖B‖ ≤ 1`.
    Since B applies G₂'s walk operator independently within each cluster,
    and ‖G₂.walkCLM‖ ≤ 1, we have ‖B‖ ≤ 1. -/
theorem withinClusterCLM_norm_le_one {n₁ d₁ d₂ : ℕ}
    (G₂ : RegularGraph d₁ d₂) (hd₁ : 0 < d₁) :
    ‖withinClusterCLM (n₁ := n₁) G₂ hd₁‖ ≤ 1 := by
  -- Use opNorm_le_bound: show ‖Bf‖ ≤ ‖f‖ for all f
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun f => ?_)
  simp only [one_mul]
  -- Expand norms as sums of squares
  simp only [EuclideanSpace.norm_eq]
  rw [Real.sqrt_le_sqrt_iff (by positivity)]
  -- ‖Bf‖² = ∑ vk, (Bf)(vk)²
  -- Group by cluster and use that each cluster is a walk operator
  calc ∑ vk, ‖(withinClusterCLM G₂ hd₁ f).ofLp vk‖ ^ 2
      = ∑ v, ∑ k, ‖(withinClusterCLM G₂ hd₁ f).ofLp (encode v k)‖ ^ 2 := by
          conv_lhs => rw [← sum_encode_eq_sum hd₁ (fun vk => ‖(withinClusterCLM G₂ hd₁ f).ofLp vk‖ ^ 2)]
    _ ≤ ∑ v, ∑ k, ‖f.ofLp (encode v k)‖ ^ 2 := by
          -- Within each cluster v, the walk operator is a contraction
          refine Finset.sum_le_sum (fun v _ => ?_)
          -- For each cluster v, show: ∑ k, ‖(Bf)(v,k)‖² ≤ ∑ k, ‖f(v,k)‖²
          -- Unfold the within-cluster walk definition
          simp only [withinClusterCLM_apply, cluster_encode, port_encode]
          -- Now: ∑ k, ‖(∑ j, f(v, G₂.neighbor k j)) / d₂‖² ≤ ∑ k, ‖f(v, k)‖²
          -- This is exactly saying G₂'s walk operator has norm ≤ 1 on this cluster
          -- Define g : Fin d₁ → ℝ by g(k) = f(v, k)
          -- Then LHS = ‖G₂.walkFun g‖² and RHS = ‖g‖²
          sorry
    _ = ∑ vk, ‖f.ofLp vk‖ ^ 2 := by
          conv_rhs => rw [← sum_encode_eq_sum hd₁ (fun vk => ‖f.ofLp vk‖ ^ 2)]


/-! **Step Permutation Properties** -/

/-- The step permutation is an involution: `Σ * Σ = 1`. -/
theorem stepPermCLM_sq_eq_one {n₁ d₁ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (hd₁ : 0 < d₁) :
    stepPermCLM G₁ hd₁ * stepPermCLM G₁ hd₁ =
    (1 : EuclideanSpace ℝ (Fin (n₁ * d₁)) →L[ℝ] _) := by
  ext f vk
  simp only [ContinuousLinearMap.mul_apply, stepPermCLM_apply,
             ContinuousLinearMap.one_apply, cluster_encode, port_encode]
  -- After simplification: f (encode (rot (rot (cluster vk, port vk))).1 ...)
  rw [RegularGraph.rot_involution, encode_cluster_port]

/-- The step permutation is self-adjoint: `Σ* = Σ`.
    This follows from `Σ` being a permutation operator (hence isometry)
    combined with `Σ² = 1` (so `Σ* = Σ⁻¹ = Σ`). -/
theorem stepPermCLM_isSelfAdjoint {n₁ d₁ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (hd₁ : 0 < d₁) :
    IsSelfAdjoint (stepPermCLM G₁ hd₁) := by
  -- Use the fact that Σ² = 1 and Σ is a permutation
  -- For permutations: if Σ² = 1, then Σ* = Σ⁻¹ = Σ
  have h_sq := stepPermCLM_sq_eq_one G₁ hd₁
  -- From Σ² = 1, we get Σ* = Σ⁻¹ = Σ
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
  ext f vk
  simp only [ContinuousLinearMap.mul_apply, meanCLM_apply, clusterMeanCLM_apply]
  -- LHS: (∑ j, ((∑ i, f (encode (cluster j) i)) / d₁)) / (n₁ * d₁)
  -- RHS: (∑ k, f k) / (n₁ * d₁)
  -- Key: as j ranges over Fin (n₁ * d₁), cluster j takes each value in Fin n₁ exactly d₁ times
  congr 1
  calc ∑ j, (∑ i, f.ofLp (encode (cluster hd₁ j) i)) / ↑d₁
      = (∑ j, ∑ i, f.ofLp (encode (cluster hd₁ j) i)) / ↑d₁ := by rw [← Finset.sum_div]
    _ = (d₁ • ∑ v, ∑ i, f.ofLp (encode v i)) / ↑d₁ := by
        congr 1
        -- Group by cluster: ∑ j ... = d₁ · ∑ v ...
        exact sum_over_cluster hd₁ (fun v => ∑ i, f.ofLp (encode v i))
    _ = ∑ v, ∑ i, f.ofLp (encode v i) := by simp; field_simp
    _ = ∑ k, f.ofLp k := sum_encode_eq_sum hd₁ _

theorem clusterMean_comp_meanCLM {n₁ d₁ : ℕ} (hd₁ : 0 < d₁) :
    clusterMeanCLM (n₁ := n₁) hd₁ *
    (meanCLM (n₁ * d₁) : EuclideanSpace ℝ (Fin (n₁ * d₁)) →L[ℝ] _) =
    meanCLM (n₁ * d₁) := by
  ext f vk
  simp only [ContinuousLinearMap.mul_apply, clusterMeanCLM_apply, meanCLM_apply]
  -- LHS: (∑ i, (meanCLM f) (encode (cluster vk) i)) / d₁
  -- Since meanCLM f is constant (= (∑ k, f k) / (n₁ * d₁)), this simplifies
  -- to (d₁ · ((∑ k, f k) / (n₁ * d₁))) / d₁ = (∑ k, f k) / (n₁ * d₁) = RHS
  rw [Finset.sum_const, Finset.card_fin]
  simp
  field_simp
