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


/-- The cluster mean projection has operator norm ≤ 1. -/
theorem clusterMeanCLM_norm_le_one {n₁ d₁ : ℕ} (hd₁ : 0 < d₁) :
    ‖clusterMeanCLM (n₁ := n₁) hd₁‖ ≤ 1 := by
  sorry  -- TODO: Prove that averaging operator has norm ≤ 1

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


/-! **Block-Diagonal Structure Helpers** -/

/-- The norm squared of a function decomposes as the sum of norms squared
    over each cluster. This is just Pythagoras for orthogonal decomposition. -/
theorem norm_sq_cluster_decomposition {n₁ d₁ : ℕ} (hd₁ : 0 < d₁)
    (f : EuclideanSpace ℝ (Fin (n₁ * d₁))) :
    ‖f‖ ^ 2 = ∑ v : Fin n₁, ∑ k : Fin d₁, f.ofLp (encode v k) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  conv_lhs => rw [← sum_encode_eq_sum hd₁]
  simp

/-- B(I-Q) simplifies to B-Q since BQ = Q. -/
theorem withinCluster_mul_complement_clusterMean {n₁ d₁ d₂ : ℕ}
    (G₂ : RegularGraph d₁ d₂) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    withinClusterCLM (n₁ := n₁) G₂ hd₁ * (1 - clusterMeanCLM hd₁) =
    withinClusterCLM G₂ hd₁ - clusterMeanCLM hd₁ := by
  rw [mul_sub, mul_one, withinCluster_comp_clusterMean G₂ hd₁ hd₂]

/-- Within each cluster v, (B-Q) acts like (G₂.walkCLM - meanCLM d₁).
    This is the key to showing the block-diagonal structure. -/
theorem withinCluster_minus_clusterMean_cluster_action {n₁ d₁ d₂ : ℕ}
    (G₂ : RegularGraph d₁ d₂) (hd₁ : 0 < d₁)
    (f : EuclideanSpace ℝ (Fin (n₁ * d₁))) (v : Fin n₁) (k : Fin d₁) :
    ((withinClusterCLM G₂ hd₁ - clusterMeanCLM hd₁) f).ofLp (encode v k) =
    ((∑ j : Fin d₂, f.ofLp (encode v (G₂.neighbor k j))) / d₂) -
    ((∑ i : Fin d₁, f.ofLp (encode v i)) / d₁) := by
  simp only [ContinuousLinearMap.sub_apply, withinClusterCLM_apply,
             clusterMeanCLM_apply, cluster_encode, port_encode]
  rfl


/-! **Cluster Quotient Helpers** -/

/-- Extract the cluster-constant part of a function as a function on Fin n₁.
    This is the "quotient map" that sends f ↦ (v ↦ mean of f on cluster v). -/
noncomputable def clusterQuotient {n₁ d₁ : ℕ} (hd₁ : 0 < d₁)
    (f : EuclideanSpace ℝ (Fin (n₁ * d₁))) : EuclideanSpace ℝ (Fin n₁) :=
  (WithLp.equiv 2 _).symm (fun v ↦ (∑ k : Fin d₁, f.ofLp (encode v k)) / d₁)

@[simp] lemma clusterQuotient_apply {n₁ d₁ : ℕ} (hd₁ : 0 < d₁)
    (f : EuclideanSpace ℝ (Fin (n₁ * d₁))) (v : Fin n₁) :
    (clusterQuotient hd₁ f).ofLp v = (∑ k : Fin d₁, f.ofLp (encode v k)) / d₁ := by
  simp [clusterQuotient]

/-- Lift a function on Fin n₁ to a cluster-constant function on Fin (n₁ * d₁). -/
noncomputable def clusterLift {n₁ d₁ : ℕ} (hd₁ : 0 < d₁)
    (g : EuclideanSpace ℝ (Fin n₁)) : EuclideanSpace ℝ (Fin (n₁ * d₁)) :=
  (WithLp.equiv 2 _).symm (fun vk ↦ g.ofLp (cluster hd₁ vk))

@[simp] lemma clusterLift_apply {n₁ d₁ : ℕ} (hd₁ : 0 < d₁)
    (g : EuclideanSpace ℝ (Fin n₁)) (vk : Fin (n₁ * d₁)) :
    (clusterLift hd₁ g).ofLp vk = g.ofLp (cluster hd₁ vk) := by
  simp [clusterLift]

/-- The cluster mean projection factors as lift ∘ quotient. -/
theorem clusterMeanCLM_eq_lift_quotient {n₁ d₁ : ℕ} (hd₁ : 0 < d₁)
    (f : EuclideanSpace ℝ (Fin (n₁ * d₁))) :
    clusterMeanCLM hd₁ f = clusterLift hd₁ (clusterQuotient hd₁ f) := by
  apply PiLp.ext; intro vk
  simp only [clusterMeanCLM_apply, clusterLift_apply, clusterQuotient_apply]

/-- **Key identity:** On cluster-constant functions (via lift/quotient),
    the step permutation Σ acts like the walk operator W_{G₁}.

    This shows: quotient ∘ Σ ∘ lift = W_{G₁}. -/
theorem stepPerm_quotient_lift {n₁ d₁ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (hd₁ : 0 < d₁)
    (g : EuclideanSpace ℝ (Fin n₁)) :
    clusterQuotient hd₁ (stepPermCLM G₁ hd₁ (clusterLift hd₁ g)) =
    G₁.walkCLM g := by
  apply PiLp.ext; intro v
  simp only [clusterQuotient_apply, stepPermCLM_apply, clusterLift_apply,
             RegularGraph.walkCLM_apply, RegularGraph.neighbor]
  -- LHS: (∑ k, g((G₁.rot(cluster(encode v k), port(encode v k))).1)) / d₁
  -- RHS: (∑ k, g((G₁.rot(v, k)).1)) / d₁
  congr 1; refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp [cluster_encode, port_encode]

/-- Norm scaling: ‖lift(g)‖ = √d₁ * ‖g‖. -/
theorem norm_clusterLift {n₁ d₁ : ℕ} (hd₁ : 0 < d₁)
    (g : EuclideanSpace ℝ (Fin n₁)) :
    ‖clusterLift hd₁ g‖ = Real.sqrt d₁ * ‖g‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [clusterLift_apply]
  rw [← sum_encode_eq_sum hd₁]
  simp only [Finset.sum_comm (t := univ)]
  rw [show ∑ v, ∑ k, ‖g.ofLp v‖ ^ 2 = ∑ v, d₁ • ‖g.ofLp v‖ ^ 2 by
      simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]]
  rw [← Finset.sum_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
  congr 1
  rw [Real.sqrt_sq (Nat.cast_nonneg _)]

/-- The global mean annihilates functions with zero cluster means. -/
theorem meanCLM_of_zero_clusterQuotient {n₁ d₁ : ℕ} (hd₁ : 0 < d₁)
    (f : EuclideanSpace ℝ (Fin (n₁ * d₁)))
    (h : clusterQuotient hd₁ f = 0) :
    meanCLM (n₁ * d₁) f = 0 := by
  apply PiLp.ext; intro vk
  simp only [meanCLM_apply]
  have : ∑ j, f.ofLp j = 0 := by
    rw [← sum_encode_eq_sum hd₁]
    simp only [Finset.sum_comm (t := univ)]
    have : ∀ v, ∑ k, f.ofLp (encode v k) = 0 := by
      intro v
      have := congr_arg (·.ofLp v) h
      simp only [clusterQuotient_apply, PiLp.zero_apply] at this
      field_simp at this
      exact this
    simp [this]
  rw [this]
  simp

/-- QΣQ - P vanishes on the orthogonal complement of Q. -/
theorem hat_block_vanishes_on_complement {n₁ d₁ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (hd₁ : 0 < d₁)
    (f : EuclideanSpace ℝ (Fin (n₁ * d₁)))
    (h : clusterMeanCLM hd₁ f = 0) :
    (clusterMeanCLM (n₁ := n₁) hd₁ * stepPermCLM G₁ hd₁ * clusterMeanCLM hd₁ -
     meanCLM (n₁ * d₁)) f = 0 := by
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, h]
  simp only [map_zero, sub_self]

/-- On cluster-constant functions (lifted), QΣQ acts like lift(W_{G₁}). -/
theorem hat_block_on_lift {n₁ d₁ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (hd₁ : 0 < d₁)
    (g : EuclideanSpace ℝ (Fin n₁)) :
    clusterMeanCLM (n₁ := n₁) hd₁ (stepPermCLM G₁ hd₁ (clusterMeanCLM hd₁ (clusterLift hd₁ g))) =
    clusterLift hd₁ (G₁.walkCLM g) := by
  -- Q(Σ(Q(lift(g)))) = Q(Σ(lift(g))) since Q(lift(g)) = lift(g)
  have : clusterMeanCLM hd₁ (clusterLift hd₁ g) = clusterLift hd₁ g := by
    rw [clusterMeanCLM_eq_lift_quotient]
    simp only [clusterQuotient_apply, clusterLift_apply]
    apply PiLp.ext; intro vk
    simp only [clusterLift_apply]
    congr 1
    rw [← sum_encode_eq_sum hd₁]
    simp only [Finset.sum_comm (t := univ)]
    have : ∀ v, ∑ k, g.ofLp (cluster hd₁ (encode v k)) = d₁ • g.ofLp v := by
      intro v; simp [Finset.sum_const, Fintype.card_fin, cluster_encode]
    simp [this, nsmul_eq_mul]
    field_simp
  rw [this]
  -- Q(Σ(lift(g))) = lift(quotient(Σ(lift(g))))
  rw [clusterMeanCLM_eq_lift_quotient]
  -- quotient(Σ(lift(g))) = W_{G₁}(g) by stepPerm_quotient_lift
  rw [stepPerm_quotient_lift]

/-- On lifted functions, the global mean P acts like lift(meanCLM n₁). -/
theorem meanCLM_on_lift {n₁ d₁ : ℕ} (hd₁ : 0 < d₁)
    (g : EuclideanSpace ℝ (Fin n₁)) :
    meanCLM (n₁ * d₁) (clusterLift hd₁ g) = clusterLift hd₁ (meanCLM n₁ g) := by
  apply PiLp.ext; intro vk
  simp only [meanCLM_apply, clusterLift_apply]
  -- LHS: (∑ j, g(cluster j)) / (n₁ * d₁)
  -- RHS: ((∑ v, g(v)) / n₁)
  congr 1
  rw [← sum_encode_eq_sum hd₁]
  simp only [Finset.sum_comm (t := univ), clusterLift_apply]
  have : ∀ v, ∑ k, g.ofLp (cluster hd₁ (encode v k)) = d₁ • g.ofLp v := by
    intro v; simp [Finset.sum_const, Fintype.card_fin, cluster_encode]
  simp [this, nsmul_eq_mul]
  ring

/-! **Cluster Restriction Helpers** -/

/-- Extract cluster v from a function on the product space. -/
def clusterRestrict {n₁ d₁ : ℕ} (f : EuclideanSpace ℝ (Fin (n₁ * d₁)))
    (v : Fin n₁) : EuclideanSpace ℝ (Fin d₁) :=
  (WithLp.equiv 2 _).symm (fun k ↦ f.ofLp (encode v k))

@[simp] lemma clusterRestrict_apply {n₁ d₁ : ℕ}
    (f : EuclideanSpace ℝ (Fin (n₁ * d₁))) (v : Fin n₁) (k : Fin d₁) :
    (clusterRestrict f v).ofLp k = f.ofLp (encode v k) := by
  simp [clusterRestrict]

/-- Within cluster v, (B-Q) acts like (W_{G₂} - meanCLM d₁). -/
theorem clusterRestrict_action {n₁ d₁ d₂ : ℕ}
    (G₂ : RegularGraph d₁ d₂) (hd₁ : 0 < d₁)
    (f : EuclideanSpace ℝ (Fin (n₁ * d₁))) (v : Fin n₁) :
    clusterRestrict ((withinClusterCLM G₂ hd₁ - clusterMeanCLM hd₁) f) v =
    (G₂.walkCLM - meanCLM d₁) (clusterRestrict f v) := by
  apply PiLp.ext; intro k
  simp only [clusterRestrict_apply, ContinuousLinearMap.sub_apply,
             RegularGraph.walkCLM_apply, meanCLM_apply]
  exact withinCluster_minus_clusterMean_cluster_action G₂ hd₁ f v k

/-- Norm squared decomposes over cluster restrictions. -/
theorem norm_sq_clusterRestrict {n₁ d₁ : ℕ} (hd₁ : 0 < d₁)
    (f : EuclideanSpace ℝ (Fin (n₁ * d₁))) :
    ‖f‖ ^ 2 = ∑ v : Fin n₁, ‖clusterRestrict f v‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, clusterRestrict_apply]
  rw [← sum_encode_eq_sum hd₁]

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
  -- Need hd₂ for the simplification lemma
  rcases Nat.eq_zero_or_pos d₂ with rfl | hd₂
  · -- d₂ = 0 case: both operators are zero
    simp [withinClusterCLM, clusterMeanCLM, Finset.sum_empty]
    exact spectralGap_nonneg G₂

  -- Simplify B(I-Q) = B - Q
  rw [withinCluster_mul_complement_clusterMean G₂ hd₁ hd₂]

  -- Use opNorm_le_bound
  apply ContinuousLinearMap.opNorm_le_bound
  · exact spectralGap_nonneg G₂
  · intro f
    -- Bound using cluster decomposition
    have h_sq : ‖(withinClusterCLM G₂ hd₁ - clusterMeanCLM hd₁) f‖ ^ 2 ≤
                (spectralGap G₂) ^ 2 * ‖f‖ ^ 2 := by
      calc ‖(withinClusterCLM G₂ hd₁ - clusterMeanCLM hd₁) f‖ ^ 2
          = ∑ v : Fin n₁, ‖clusterRestrict ((withinClusterCLM G₂ hd₁ - clusterMeanCLM hd₁) f) v‖ ^ 2 := by
            exact norm_sq_clusterRestrict hd₁ _
        _ = ∑ v : Fin n₁, ‖(G₂.walkCLM - meanCLM d₁) (clusterRestrict f v)‖ ^ 2 := by
            refine Finset.sum_congr rfl fun v _ ↦ ?_
            rw [clusterRestrict_action G₂ hd₁]
        _ ≤ ∑ v : Fin n₁, (spectralGap G₂ * ‖clusterRestrict f v‖) ^ 2 := by
            apply Finset.sum_le_sum; intro v _
            unfold spectralGap
            exact sq_le_sq' (by linarith [norm_nonneg _, spectralGap_nonneg G₂])
                            (ContinuousLinearMap.le_opNorm _ _)
        _ = (spectralGap G₂) ^ 2 * ∑ v : Fin n₁, ‖clusterRestrict f v‖ ^ 2 := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun v _ ↦ ?_; ring
        _ = (spectralGap G₂) ^ 2 * ‖f‖ ^ 2 := by
            rw [← norm_sq_clusterRestrict hd₁]
    -- Take square root
    calc ‖(withinClusterCLM G₂ hd₁ - clusterMeanCLM hd₁) f‖
        = √(‖(withinClusterCLM G₂ hd₁ - clusterMeanCLM hd₁) f‖ ^ 2) := by
          rw [Real.sqrt_sq (norm_nonneg _)]
      _ ≤ √((spectralGap G₂) ^ 2 * ‖f‖ ^ 2) := by
          apply Real.sqrt_le_sqrt; exact h_sq
      _ = spectralGap G₂ * ‖f‖ := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (spectralGap_nonneg G₂),
              Real.sqrt_sq (norm_nonneg _)]

/-- **Hat block spectral gap:** `Q · Σ · Q` restricted to the hat subspace
    acts like `W_{G₁}` lifted to the product space, so its distance from
    the global mean projection is bounded by `spectralGap G₁`.

    More precisely: `‖QΣQ - P‖ ≤ spectralGap G₁` where `P = meanCLM (n₁ * d₁)`. -/
theorem hat_block_norm {n₁ d₁ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (hd₁ : 0 < d₁) :
    ‖clusterMeanCLM (n₁ := n₁) hd₁ * stepPermCLM G₁ hd₁ * clusterMeanCLM hd₁ -
     (meanCLM (n₁ * d₁) : EuclideanSpace ℝ (Fin (n₁ * d₁)) →L[ℝ] _)‖ ≤
    spectralGap G₁ := by
  -- Abbreviations
  set Q := clusterMeanCLM (n₁ := n₁) hd₁
  set S := stepPermCLM G₁ hd₁
  set P := (meanCLM (n₁ * d₁) : EuclideanSpace ℝ (Fin (n₁ * d₁)) →L[ℝ] _)

  -- Use opNorm_le_bound
  apply ContinuousLinearMap.opNorm_le_bound
  · exact spectralGap_nonneg G₁
  · intro f
    -- Key: (QSQ - P) acts only on the image of Q
    -- Write Qf = clusterLift(g) where g = clusterQuotient(f)
    set g := clusterQuotient hd₁ f

    -- Since Q is idempotent, Qf = clusterLift(g)
    have hQf : Q f = clusterLift hd₁ g := clusterMeanCLM_eq_lift_quotient hd₁ f

    -- (QSQ - P)f = (QSQ - P)(Qf) using Q² = Q and PQ = P
    have vanish_key : (Q * S * Q - P) f = (Q * S * Q - P) (Q f) := by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply]
      congr 1
      · -- QS(Qf) = QS(Q(Qf))
        rw [clusterMeanCLM_idempotent hd₁]
      · -- Pf = P(Qf) using PQ = P
        have hPQ : P * Q = P := meanCLM_eq_clusterMean_comp hd₁
        calc P f = (P * Q) f + P ((1 - Q) f) := by
              rw [← add_sub_cancel_left (Q f) f]
              simp only [map_add, ContinuousLinearMap.sub_apply,
                         ContinuousLinearMap.one_apply, map_sub]
          _ = P (Q f) + P ((1 - Q) f) := by rw [hPQ]; rfl
          _ = P (Q f) := by
              -- P((I-Q)f) = 0 since (I-Q)f has zero cluster means, so zero global mean
              have : (1 - Q) f = (1 - Q) f := rfl
              simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at this
              have hzero : Q ((1 - Q) f) = 0 := by
                simp only [map_sub, ContinuousLinearMap.one_apply]
                rw [clusterMeanCLM_idempotent hd₁]
                simp
              have : clusterQuotient hd₁ ((1 - Q) f) = 0 := by
                rw [← clusterMeanCLM_eq_lift_quotient] at hzero
                have : clusterLift hd₁ (clusterQuotient hd₁ ((1 - Q) f)) = 0 := hzero
                -- If lift(g) = 0, then g = 0
                have : ∀ v, (clusterQuotient hd₁ ((1 - Q) f)).ofLp v = 0 := by
                  intro v
                  have := congr_arg (·.ofLp (encode v ⟨0, hd₁⟩)) this
                  simp only [clusterLift_apply, cluster_encode, PiLp.zero_apply] at this
                  exact this
                ext v; exact this v
              exact meanCLM_of_zero_clusterQuotient hd₁ _ this

    rw [vanish_key, hQf]

    -- On clusterLift(g): (QSQ - P)(clusterLift(g)) = clusterLift((W_{G₁} - meanCLM n₁)(g))
    have action_on_lift : (Q * S * Q - P) (clusterLift hd₁ g) =
        clusterLift hd₁ ((G₁.walkCLM - meanCLM n₁) g) := by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply]
      have : Q * S * Q = Q * (S * Q) := by rw [mul_assoc]
      rw [this]
      rw [hat_block_on_lift, meanCLM_on_lift]
      simp [ContinuousLinearMap.sub_apply]

    rw [action_on_lift]

    -- Bound using norm scaling and spectral gap
    calc ‖clusterLift hd₁ ((G₁.walkCLM - meanCLM n₁) g)‖
        = Real.sqrt d₁ * ‖(G₁.walkCLM - meanCLM n₁) g‖ := by
          exact norm_clusterLift hd₁ _
      _ ≤ Real.sqrt d₁ * (spectralGap G₁ * ‖g‖) := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          unfold spectralGap
          exact ContinuousLinearMap.le_opNorm _ _
      _ = spectralGap G₁ * (Real.sqrt d₁ * ‖g‖) := by ring
      _ = spectralGap G₁ * ‖clusterLift hd₁ g‖ := by
          rw [norm_clusterLift hd₁]
      _ = spectralGap G₁ * ‖Q f‖ := by rw [← hQf]
      _ ≤ spectralGap G₁ * ‖f‖ := by
          apply mul_le_mul_of_nonneg_left _ (spectralGap_nonneg G₁)
          -- Q is a projection with norm ≤ 1
          calc ‖Q f‖ ≤ ‖Q‖ * ‖f‖ := Q.le_opNorm f
            _ ≤ 1 * ‖f‖ := by
                apply mul_le_mul_of_nonneg_right (clusterMeanCLM_norm_le_one hd₁) (norm_nonneg _)
            _ = ‖f‖ := one_mul _


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
