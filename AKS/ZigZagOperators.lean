/-
  # Zig-Zag Product Operators

  Defines the three CLM operators used in the spectral analysis of the
  zig-zag product: the within-cluster walk `B`, the step permutation `Σ`,
  and the cluster mean projection `Q`.

  These act on `EuclideanSpace ℝ (Fin (n₁ * d₁))`, where vertices are
  encoded as `v * d₁ + k` for cluster `v : Fin n₁` and port `k : Fin d₁`.

  Algebraic properties and spectral bounds are in `ZigZagSpectral.lean`.
-/

import AKS.RegularGraph

open Matrix BigOperators Finset


/-! **Cluster Encoding Helpers** -/

/-- Decode the cluster index from a product vertex. -/
def cluster {n₁ d₁ : ℕ} (hd₁ : 0 < d₁) (vk : Fin (n₁ * d₁)) : Fin n₁ :=
  ⟨vk.val / d₁, (Nat.div_lt_iff_lt_mul hd₁).mpr vk.isLt⟩

/-- Decode the port index from a product vertex. -/
def port {n₁ d₁ : ℕ} (hd₁ : 0 < d₁) (vk : Fin (n₁ * d₁)) : Fin d₁ :=
  ⟨vk.val % d₁, Nat.mod_lt _ hd₁⟩

/-- Encode a (cluster, port) pair as a product vertex. -/
def encode {n₁ d₁ : ℕ} (v : Fin n₁) (k : Fin d₁) : Fin (n₁ * d₁) :=
  ⟨v.val * d₁ + k.val, Fin.pair_lt v k⟩

@[simp]
theorem cluster_encode {n₁ d₁ : ℕ} (hd₁ : 0 < d₁) (v : Fin n₁) (k : Fin d₁) :
    cluster hd₁ (encode v k) = v :=
  fin_encode_fst v k _

@[simp]
theorem port_encode {n₁ d₁ : ℕ} (hd₁ : 0 < d₁) (v : Fin n₁) (k : Fin d₁) :
    port hd₁ (encode v k) = k :=
  fin_encode_snd v k _

@[simp]
theorem encode_cluster_port {n₁ d₁ : ℕ} (hd₁ : 0 < d₁) (vk : Fin (n₁ * d₁)) :
    encode (cluster hd₁ vk) (port hd₁ vk) = vk :=
  fin_div_add_mod vk _

/-- Summing over the product space via encode equals summing over all indices.
    This is the bijection between Fin n₁ × Fin d₁ and Fin (n₁ * d₁). -/
theorem sum_encode_eq_sum {n₁ d₁ : ℕ} (hd₁ : 0 < d₁) (f : Fin (n₁ * d₁) → ℝ) :
    ∑ v : Fin n₁, ∑ i : Fin d₁, f (encode v i) = ∑ k : Fin (n₁ * d₁), f k := by
  simp_rw [← Fintype.sum_prod_type']
  -- Use Finset.sum_bij' to show bijection
  refine Finset.sum_bij' (fun (p : Fin n₁ × Fin d₁) _ => encode p.1 p.2)
    (fun k _ => (cluster hd₁ k, port hd₁ k))
    (fun _ _ => Finset.mem_univ _)
    (fun _ _ => Finset.mem_univ _)
    (fun p _ => ?_)
    (fun k _ => encode_cluster_port hd₁ k)
    (fun p _ => ?_)
  · simp [cluster_encode, port_encode]
  · rfl

/-- Summing a function of cluster over all product indices counts each cluster d₁ times. -/
theorem sum_over_cluster {n₁ d₁ : ℕ} (hd₁ : 0 < d₁) (g : Fin n₁ → ℝ) :
    ∑ j : Fin (n₁ * d₁), g (cluster hd₁ j) = d₁ • ∑ v : Fin n₁, g v := by
  -- Rewrite using encode/cluster/port bijection
  conv_lhs => rw [← sum_encode_eq_sum hd₁ (fun j => g (cluster hd₁ j))]
  simp only [cluster_encode]
  -- Now LHS = ∑ v, ∑ i, g v
  rw [show ∑ v, ∑ _i : Fin d₁, g v = ∑ v, d₁ • g v by
    congr 1; ext v; rw [Finset.sum_const, Finset.card_fin]]
  rw [Finset.smul_sum]


/-! **Within-Cluster Walk Operator (B = I ⊗ W_{G₂})** -/

/-- The within-cluster walk function: applies G₂'s walk independently
    within each d₁-cluster. `(Bf)(v,k) = (1/d₂) ∑ⱼ f(v, G₂.neighbor k j)`. -/
noncomputable def withinClusterFun {n₁ d₁ d₂ : ℕ}
    (G₂ : RegularGraph d₁ d₂) (hd₁ : 0 < d₁)
    (f : Fin (n₁ * d₁) → ℝ) : Fin (n₁ * d₁) → ℝ :=
  fun vk ↦
    (∑ j : Fin d₂, f (encode (cluster hd₁ vk) (G₂.neighbor (port hd₁ vk) j))) / d₂

/-- The within-cluster walk as a linear map on `EuclideanSpace`. -/
noncomputable def withinClusterLM {n₁ d₁ d₂ : ℕ}
    (G₂ : RegularGraph d₁ d₂) (hd₁ : 0 < d₁) :
    EuclideanSpace ℝ (Fin (n₁ * d₁)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n₁ * d₁)) where
  toFun f := WithLp.toLp 2 (withinClusterFun G₂ hd₁ (WithLp.ofLp f))
  map_add' f g := by
    apply PiLp.ext; intro vk
    simp [withinClusterFun, Finset.sum_add_distrib, add_div]
  map_smul' r f := by
    apply PiLp.ext; intro vk
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, withinClusterFun, ← Finset.mul_sum, mul_div_assoc]

/-- The within-cluster walk operator as a CLM. Applies G₂'s walk independently
    within each d₁-cluster: `(Bf)(v,k) = (1/d₂) ∑ⱼ f(v, G₂.neighbor k j)`. -/
noncomputable def withinClusterCLM {n₁ d₁ d₂ : ℕ}
    (G₂ : RegularGraph d₁ d₂) (hd₁ : 0 < d₁) :
    EuclideanSpace ℝ (Fin (n₁ * d₁)) →L[ℝ] EuclideanSpace ℝ (Fin (n₁ * d₁)) :=
  (withinClusterLM G₂ hd₁).toContinuousLinearMap

@[simp]
theorem withinClusterCLM_apply {n₁ d₁ d₂ : ℕ}
    (G₂ : RegularGraph d₁ d₂) (hd₁ : 0 < d₁)
    (f : EuclideanSpace ℝ (Fin (n₁ * d₁))) (vk : Fin (n₁ * d₁)) :
    withinClusterCLM G₂ hd₁ f vk =
    (∑ j : Fin d₂, f (encode (cluster hd₁ vk) (G₂.neighbor (port hd₁ vk) j))) / d₂ :=
  rfl


/-! **Step Permutation Operator (Σ)** -/

/-- The step permutation function: permutes `(v,k) ↦ G₁.rot(v,k)`.
    `(Σf)(v,k) = f(G₁.rot(v,k))`. -/
def stepPermFun {n₁ d₁ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (hd₁ : 0 < d₁)
    (f : Fin (n₁ * d₁) → ℝ) : Fin (n₁ * d₁) → ℝ :=
  fun vk ↦
    let step := G₁.rot (cluster hd₁ vk, port hd₁ vk)
    f (encode step.1 step.2)

/-- The step permutation as a linear map on `EuclideanSpace`. -/
def stepPermLM {n₁ d₁ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (hd₁ : 0 < d₁) :
    EuclideanSpace ℝ (Fin (n₁ * d₁)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n₁ * d₁)) where
  toFun f := WithLp.toLp 2 (stepPermFun G₁ hd₁ (WithLp.ofLp f))
  map_add' f g := by
    apply PiLp.ext; intro vk; simp [stepPermFun]
  map_smul' r f := by
    apply PiLp.ext; intro vk
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, stepPermFun]

/-- The step permutation as a CLM. Permutes according to G₁'s rotation map:
    `(Σf)(v,k) = f(G₁.rot(v,k))`. -/
noncomputable def stepPermCLM {n₁ d₁ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (hd₁ : 0 < d₁) :
    EuclideanSpace ℝ (Fin (n₁ * d₁)) →L[ℝ] EuclideanSpace ℝ (Fin (n₁ * d₁)) :=
  (stepPermLM G₁ hd₁).toContinuousLinearMap

@[simp]
theorem stepPermCLM_apply {n₁ d₁ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (hd₁ : 0 < d₁)
    (f : EuclideanSpace ℝ (Fin (n₁ * d₁))) (vk : Fin (n₁ * d₁)) :
    stepPermCLM G₁ hd₁ f vk =
    f (encode (G₁.rot (cluster hd₁ vk, port hd₁ vk)).1
             (G₁.rot (cluster hd₁ vk, port hd₁ vk)).2) :=
  rfl


/-! **Cluster Mean Projection (Q)** -/

/-- The cluster mean function: averages f within each d₁-cluster.
    `(Qf)(v,k) = (1/d₁) ∑ⱼ f(v,j)`. -/
noncomputable def clusterMeanFun {n₁ d₁ : ℕ} (hd₁ : 0 < d₁)
    (f : Fin (n₁ * d₁) → ℝ) : Fin (n₁ * d₁) → ℝ :=
  fun vk ↦ (∑ j : Fin d₁, f (encode (cluster hd₁ vk) j)) / d₁

/-- The cluster mean as a linear map on `EuclideanSpace`. -/
noncomputable def clusterMeanLM {n₁ d₁ : ℕ} (hd₁ : 0 < d₁) :
    EuclideanSpace ℝ (Fin (n₁ * d₁)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n₁ * d₁)) where
  toFun f := WithLp.toLp 2 (clusterMeanFun hd₁ (WithLp.ofLp f))
  map_add' f g := by
    apply PiLp.ext; intro vk
    simp [clusterMeanFun, Finset.sum_add_distrib, add_div]
  map_smul' r f := by
    apply PiLp.ext; intro vk
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, clusterMeanFun, ← Finset.mul_sum, mul_div_assoc]

/-- The cluster mean projection as a CLM. Averages f within each d₁-cluster:
    `(Qf)(v,k) = (1/d₁) ∑ⱼ f(v,j)`. -/
noncomputable def clusterMeanCLM {n₁ d₁ : ℕ} (hd₁ : 0 < d₁) :
    EuclideanSpace ℝ (Fin (n₁ * d₁)) →L[ℝ] EuclideanSpace ℝ (Fin (n₁ * d₁)) :=
  (clusterMeanLM hd₁).toContinuousLinearMap

@[simp]
theorem clusterMeanCLM_apply {n₁ d₁ : ℕ} (hd₁ : 0 < d₁)
    (f : EuclideanSpace ℝ (Fin (n₁ * d₁))) (vk : Fin (n₁ * d₁)) :
    clusterMeanCLM hd₁ f vk =
    (∑ j : Fin d₁, f (encode (cluster hd₁ vk) j)) / d₁ :=
  rfl


/-! **The Zig-Zag Product** -/

/-- **The zig-zag product** G₁ ⓩ G₂.

    Given:  G₁ = (n₁, d₁)-regular graph
            G₂ = (d₁, d₂)-regular graph  (G₂ has d₁ vertices!)
    Result: (n₁ · d₁, d₂²)-regular graph

    Vertices of G₁ ⓩ G₂ are pairs (v, k) where v ∈ V(G₁), k ∈ V(G₂) = [d₁].

    The rotation map performs three steps:
    1. **Zig**: Walk along G₂ from port k using port a (first half of d₂²).
       Arrive at port k'.
    2. **Step**: Cross the big graph G₁ along port k'.
       Arrive at (v', k'') on the other side.
    3. **Zag**: Walk along G₂ again from port k'' using port b.
       Arrive at final port k'''.

    The pair (a, b) ∈ [d₂] × [d₂] encodes the d₂²-valued port. -/
private def zigzag_rot {n₁ d₁ d₂ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (G₂ : RegularGraph d₁ d₂)
    (p : Fin (n₁ * d₁) × Fin (d₂ * d₂)) : Fin (n₁ * d₁) × Fin (d₂ * d₂) :=
  have hd₁ : 0 < d₁ :=
    Nat.pos_of_ne_zero (by rintro rfl; exact absurd p.1.isLt (by simp))
  have hd₂ : 0 < d₂ :=
    Nat.pos_of_ne_zero (by rintro rfl; exact absurd p.2.isLt (by simp))
  -- Decode vertex (v, k) from Fin (n₁ * d₁)
  let v : Fin n₁ := ⟨p.1.val / d₁, (Nat.div_lt_iff_lt_mul hd₁).mpr p.1.isLt⟩
  let k : Fin d₁ := ⟨p.1.val % d₁, Nat.mod_lt _ hd₁⟩
  -- Decode port (a, b) from Fin (d₂ * d₂)
  let a : Fin d₂ := ⟨p.2.val / d₂, (Nat.div_lt_iff_lt_mul hd₂).mpr p.2.isLt⟩
  let b : Fin d₂ := ⟨p.2.val % d₂, Nat.mod_lt _ hd₂⟩
  -- Zig: walk in G₂ from k along port a
  let zig := G₂.rot (k, a)
  -- Step: walk in G₁ from v along port zig.1
  let step := G₁.rot (v, zig.1)
  -- Zag: walk in G₂ from step.2 along port b
  let zag := G₂.rot (step.2, b)
  -- Encode: vertex = (step.1, zag.1), port = (zag.2, zig.2)
  (⟨step.1.val * d₁ + zag.1.val, Fin.pair_lt step.1 zag.1⟩,
   ⟨zag.2.val * d₂ + zig.2.val, Fin.pair_lt zag.2 zig.2⟩)

private theorem zigzag_rot_involution {n₁ d₁ d₂ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (G₂ : RegularGraph d₁ d₂)
    (p : Fin (n₁ * d₁) × Fin (d₂ * d₂)) :
    zigzag_rot G₁ G₂ (zigzag_rot G₁ G₂ p) = p := by
  obtain ⟨vk, ab⟩ := p
  simp only [zigzag_rot, fin_encode_fst, fin_encode_snd, Prod.mk.eta,
    G₁.rot_involution, G₂.rot_involution, fin_div_add_mod]

def RegularGraph.zigzag {n₁ d₁ d₂ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (G₂ : RegularGraph d₁ d₂) :
    RegularGraph (n₁ * d₁) (d₂ * d₂) where
  rot := zigzag_rot G₁ G₂
  rot_involution := zigzag_rot_involution G₁ G₂


/-! **Walk Factorization: W_Z = B · Σ · B** -/

/-- The zig-zag walk operator factors as the composition of within-cluster
    walk, step permutation, and within-cluster walk: `W_Z = B · Σ · B`.

    This is the fundamental factorization underlying the RVW spectral bound. -/
theorem zigzag_walkCLM_eq {n₁ d₁ d₂ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (G₂ : RegularGraph d₁ d₂)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    (G₁.zigzag G₂).walkCLM =
    withinClusterCLM G₂ hd₁ * stepPermCLM G₁ hd₁ * withinClusterCLM G₂ hd₁ := by
  sorry
