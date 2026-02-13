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
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  -- Unfold clusterMeanCLM on both sides
  show ∑ vk, g.ofLp vk * (clusterMeanCLM hd₁ f).ofLp vk =
       ∑ vk, (clusterMeanCLM hd₁ g).ofLp vk * f.ofLp vk
  simp only [clusterMeanCLM_apply]
  -- Both sides equal (1/d₁) * (sum of products over cluster structure)
  -- Transform and reorganize
  suffices h : ∑ vk, ∑ i, g.ofLp vk * f.ofLp (encode (cluster hd₁ vk) i) =
               ∑ vk, ∑ i, g.ofLp (encode (cluster hd₁ vk) i) * f.ofLp vk by
    have lhs : ∑ vk, g.ofLp vk * ((∑ i, f.ofLp (encode (cluster hd₁ vk) i)) / ↑d₁) =
               (∑ vk, ∑ i, g.ofLp vk * f.ofLp (encode (cluster hd₁ vk) i)) / ↑d₁ := by
      trans (∑ vk, (g.ofLp vk * ∑ i, f.ofLp (encode (cluster hd₁ vk) i)) / ↑d₁)
      · congr; funext vk; rw [mul_div_assoc]
      · rw [← Finset.sum_div]; congr; funext vk; rw [Finset.mul_sum]
    have rhs : ∑ vk, ((∑ i, g.ofLp (encode (cluster hd₁ vk) i)) / ↑d₁) * f.ofLp vk =
               (∑ vk, ∑ i, g.ofLp (encode (cluster hd₁ vk) i) * f.ofLp vk) / ↑d₁ := by
      trans (∑ vk, ((∑ i, g.ofLp (encode (cluster hd₁ vk) i)) * f.ofLp vk) / ↑d₁)
      · congr; funext vk; rw [div_mul_eq_mul_div]
      · rw [← Finset.sum_div]; congr; funext vk; rw [Finset.sum_mul]
    rw [lhs, rhs, h]

  -- Show the double sums are equal by cluster reorganization
  calc ∑ vk, ∑ i, g.ofLp vk * f.ofLp (encode (cluster hd₁ vk) i)
      = ∑ vk, ∑ i, g.ofLp (encode (cluster hd₁ vk) (port hd₁ vk)) *
                   f.ofLp (encode (cluster hd₁ vk) i) := by
        congr 1; ext vk; congr 1; ext i
        rw [encode_cluster_port hd₁]
    _ = ∑ v, ∑ j, ∑ i, g.ofLp (encode v j) * f.ofLp (encode v i) := by
        conv_lhs => rw [← sum_encode_eq_sum hd₁]
        congr 1; ext v; congr 1; ext j
        simp only [cluster_encode, port_encode]
    _ = ∑ v, ∑ i, ∑ j, g.ofLp (encode v j) * f.ofLp (encode v i) := by
        congr 1; ext v; rw [Finset.sum_comm]
    _ = ∑ v, ∑ i, ∑ j, g.ofLp (encode v i) * f.ofLp (encode v j) := by
        -- Relabel: swap dummy variables i ↔ j
        congr 1; funext v
        trans (∑ j, ∑ i, g.ofLp (encode v j) * f.ofLp (encode v i))
        · rw [Finset.sum_comm]
        · -- Now relabel j→i and i→j (just renaming dummies)
          show ∑ j, ∑ i, g.ofLp (encode v j) * f.ofLp (encode v i) =
               ∑ i, ∑ j, g.ofLp (encode v i) * f.ofLp (encode v j)
          -- These are literally the same (j and i are just dummy variable names)
          rfl
    _ = ∑ v, ∑ j, ∑ i, g.ofLp (encode v i) * f.ofLp (encode v j) := by
        congr 1; ext v; rw [Finset.sum_comm]
    _ = ∑ vk, ∑ i, g.ofLp (encode (cluster hd₁ vk) i) *
                   f.ofLp (encode (cluster hd₁ vk) (port hd₁ vk)) := by
        conv_rhs => rw [← sum_encode_eq_sum hd₁]
        congr 1; ext v; congr 1; ext j
        simp only [cluster_encode, port_encode]
    _ = ∑ vk, ∑ i, g.ofLp (encode (cluster hd₁ vk) i) * f.ofLp vk := by
        congr 1; ext vk; congr 1; ext i
        rw [encode_cluster_port hd₁]


/-! **Within-Cluster Walk Properties** -/

/-- The within-cluster walk operator is self-adjoint: `B* = B`.
    This follows from G₂'s rotation map being an involution, which makes
    the neighbor sum symmetric. -/
theorem withinClusterCLM_isSelfAdjoint {n₁ d₁ d₂ : ℕ}
    (G₂ : RegularGraph d₁ d₂) (hd₁ : 0 < d₁) :
    IsSelfAdjoint (withinClusterCLM (n₁ := n₁) G₂ hd₁) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  -- Unfold withinClusterCLM on both sides
  show ∑ vk, g.ofLp vk * (withinClusterCLM G₂ hd₁ f).ofLp vk =
       ∑ vk, (withinClusterCLM G₂ hd₁ g).ofLp vk * f.ofLp vk
  simp only [withinClusterCLM_apply]
  -- Both sides equal (1/d₂) * ∑ v, ∑ k, ∑ j, ... after pulling out divisions
  -- The inner double sum is symmetric by rotation bijection

  suffices h : ∑ vk, ∑ j, g.ofLp vk * f.ofLp (encode (cluster hd₁ vk) (G₂.neighbor (port hd₁ vk) j)) =
               ∑ vk, ∑ j, g.ofLp (encode (cluster hd₁ vk) (G₂.neighbor (port hd₁ vk) j)) * f.ofLp vk by
    have lhs : ∑ vk, g.ofLp vk * ((∑ j, f.ofLp (encode (cluster hd₁ vk) (G₂.neighbor (port hd₁ vk) j))) / ↑d₂) =
               (∑ vk, ∑ j, g.ofLp vk * f.ofLp (encode (cluster hd₁ vk) (G₂.neighbor (port hd₁ vk) j))) / ↑d₂ := by
      trans (∑ vk, (g.ofLp vk * ∑ j, f.ofLp (encode (cluster hd₁ vk) (G₂.neighbor (port hd₁ vk) j))) / ↑d₂)
      · congr; funext vk; rw [mul_div_assoc]
      · rw [← Finset.sum_div]; congr; funext vk; rw [Finset.mul_sum]
    have rhs : ∑ vk, ((∑ j, g.ofLp (encode (cluster hd₁ vk) (G₂.neighbor (port hd₁ vk) j))) / ↑d₂) * f.ofLp vk =
               (∑ vk, ∑ j, g.ofLp (encode (cluster hd₁ vk) (G₂.neighbor (port hd₁ vk) j)) * f.ofLp vk) / ↑d₂ := by
      trans (∑ vk, ((∑ j, g.ofLp (encode (cluster hd₁ vk) (G₂.neighbor (port hd₁ vk) j))) * f.ofLp vk) / ↑d₂)
      · congr; funext vk; rw [div_mul_eq_mul_div]
      · rw [← Finset.sum_div]; congr; funext vk; rw [Finset.sum_mul]
    rw [lhs, rhs, h]

  -- Show double sums are equal by converting to cluster structure and using rotation bijection
  conv_lhs => rw [← sum_encode_eq_sum hd₁]
  conv_rhs => rw [← sum_encode_eq_sum hd₁]
  simp only [cluster_encode, port_encode]

  congr 1; ext v
  -- For each cluster v, apply rotation bijection to swap neighbors
  simp_rw [RegularGraph.neighbor]
  simp_rw [← Fintype.sum_prod_type']
  -- Now both sides are ∑_{k,j} ... where the product is over Fin d₁ × Fin d₂
  -- Simplify (x.1, x.2) to x
  simp only [Prod.mk.eta]
  -- Apply rotation bijection to reindex
  have h := G₂.rotEquiv.sum_comp (fun p ↦ g.ofLp (encode v (G₂.rot p).1) * f.ofLp (encode v p.1))
  simp only [show ∀ p, (G₂.rotEquiv p : Fin d₁ × Fin d₂) = G₂.rot p from fun _ ↦ rfl,
    G₂.rot_involution] at h
  exact h

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
  apply Real.sqrt_le_sqrt
  -- ‖Bf‖² = ∑ vk, (Bf)(vk)²
  -- Group by cluster and use that each cluster is a walk operator
  calc ∑ vk, ‖(withinClusterCLM G₂ hd₁ f).ofLp vk‖ ^ 2
      = ∑ v, ∑ k, ‖(withinClusterCLM G₂ hd₁ f).ofLp (encode v k)‖ ^ 2 := by
          conv_lhs => rw [← sum_encode_eq_sum hd₁ (fun vk => ‖(withinClusterCLM G₂ hd₁ f).ofLp vk‖ ^ 2)]
    _ ≤ ∑ v, ∑ k, ‖f.ofLp (encode v k)‖ ^ 2 := by
          -- Within each cluster v, the walk operator is a contraction
          refine Finset.sum_le_sum (fun v _ => ?_)
          -- For each cluster v, show: ∑ k, ‖(Bf)(v,k)‖² ≤ ∑ k, ‖f(v,k)‖²
          simp only [withinClusterCLM_apply, cluster_encode, port_encode]
          -- Define the cluster-restricted function
          let g : EuclideanSpace ℝ (Fin d₁) := (WithLp.equiv 2 _).symm (fun k => f.ofLp (encode v k))
          -- Connect to G₂.walkCLM and use its contraction property
          have sum_eq : ∑ k, ‖(∑ j, f.ofLp (encode v (G₂.neighbor k j))) / ↑d₂‖ ^ 2
                      = ∑ k, ‖(G₂.walkCLM g).ofLp k‖ ^ 2 := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            show ‖(∑ j, f.ofLp (encode v (G₂.neighbor k j))) / ↑d₂‖ ^ 2
               = ‖(∑ j, g.ofLp (G₂.neighbor k j)) / ↑d₂‖ ^ 2
            rfl
          rw [sum_eq]
          -- Use ‖G₂.walkCLM g‖² ≤ ‖g‖² from walkCLM_norm_le_one
          have h_norm : ‖G₂.walkCLM g‖ ≤ ‖g‖ := by
            calc ‖G₂.walkCLM g‖ ≤ ‖G₂.walkCLM‖ * ‖g‖ := ContinuousLinearMap.le_opNorm _ _
              _ ≤ 1 * ‖g‖ := by gcongr; exact RegularGraph.walkCLM_norm_le_one G₂
              _ = ‖g‖ := one_mul _
          calc ∑ k, ‖(G₂.walkCLM g).ofLp k‖ ^ 2
              = ‖G₂.walkCLM g‖ ^ 2 := by rw [← EuclideanSpace.norm_sq_eq]
            _ ≤ ‖g‖ ^ 2 := by gcongr
            _ = ∑ k, ‖g.ofLp k‖ ^ 2 := by rw [EuclideanSpace.norm_sq_eq]
            _ = ∑ k, ‖f.ofLp (encode v k)‖ ^ 2 := by
                  refine Finset.sum_congr rfl (fun k _ => ?_)
                  show ‖g.ofLp k‖ ^ 2 = ‖f.ofLp (encode v k)‖ ^ 2
                  rfl
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
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  -- Unfold stepPermCLM
  show ∑ vk, g.ofLp vk * (stepPermCLM G₁ hd₁ f).ofLp vk =
       ∑ vk, (stepPermCLM G₁ hd₁ g).ofLp vk * f.ofLp vk
  simp only [stepPermCLM_apply]
  -- LHS: ∑ vk, g(vk) * f(σ(vk)) where σ = encode ∘ G₁.rot ∘ (cluster, port)
  -- RHS: ∑ vk, g(σ(vk)) * f(vk)
  -- These are equal by reindexing LHS via the bijection σ

  -- Define the permutation σ
  let σ := fun vk => encode (G₁.rot (cluster hd₁ vk, port hd₁ vk)).1
                            (G₁.rot (cluster hd₁ vk, port hd₁ vk)).2

  -- Convert to product space and use rotation bijection
  conv_lhs => rw [← sum_encode_eq_sum hd₁]
  conv_rhs => rw [← sum_encode_eq_sum hd₁]
  simp only [cluster_encode, port_encode]

  -- Now both are ∑ over Fin n₁ × Fin d₁
  simp_rw [← Fintype.sum_prod_type']

  -- Simplify (x.1, x.2) to x using Prod.mk.eta
  simp only [Prod.mk.eta]

  -- Apply rotation bijection
  have h := G₁.rotEquiv.sum_comp (fun p : Fin n₁ × Fin d₁ ↦
    g.ofLp (encode p.1 p.2) * f.ofLp (encode (G₁.rot p).1 (G₁.rot p).2))
  simp only [show ∀ p, (G₁.rotEquiv p : Fin n₁ × Fin d₁) = G₁.rot p from fun _ ↦ rfl,
    G₁.rot_involution] at h
  exact h.symm


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
