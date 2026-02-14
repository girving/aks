/-
  # Explicit Expanders via the Zig-Zag Product

  Lean formalization of the Reingold–Vadhan–Wigderson (2002) zig-zag
  product and its application to constructing explicit expander families.

  General regular graph theory (`RegularGraph`, spectral gap, squaring,
  complete graph) lives in `RegularGraph.lean`. This file builds on it
  with the zig-zag product, spectral composition theorem, and the
  iterated construction that yields expanders at every size.
-/

import AKS.ZigZagSpectral
import AKS.RVWBound
import AKS.Square

open Matrix BigOperators Finset


/-! **The Spectral Composition Theorem** -/

/-- **The Main Theorem (Reingold–Vadhan–Wigderson 2002):**

    λ(G₁ ⓩ G₂) ≤ f(λ₁, λ₂)

    where f is the precise RVW bound `rvwBound`.

    At the fixed point c = f(c², β), this simplifies to β² = c²/(1+c+c²),
    which converges for β² < 1/3 (i.e., D ≥ 12 with Alon–Boppana). -/
theorem zigzag_spectral_bound {n₁ d₁ d₂ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (G₂ : RegularGraph d₁ d₂)
    (lam₁ lam₂ : ℝ)
    (hG₁ : spectralGap G₁ ≤ lam₁) (hlam₁_le : lam₁ ≤ 1)
    (hG₂ : spectralGap G₂ ≤ lam₂) (hlam₂_le : lam₂ ≤ 1)
    (hd₂ : 0 < d₂) :
    spectralGap (G₁.zigzag G₂) ≤ rvwBound lam₁ lam₂ := by
  -- Derive non-negativity of bounds
  have hlam₁ : 0 ≤ lam₁ := le_trans (spectralGap_nonneg G₁) hG₁
  have hlam₂ : 0 ≤ lam₂ := le_trans (spectralGap_nonneg G₂) hG₂
  -- Degenerate case: n₁ * d₁ = 0 (trivial space, all norms are 0)
  rcases Nat.eq_zero_or_pos (n₁ * d₁) with h0 | hpos
  · haveI : IsEmpty (Fin (n₁ * d₁)) := by rw [h0]; exact Fin.isEmpty
    have hsg : spectralGap (G₁.zigzag G₂) = 0 := by
      apply le_antisymm _ (spectralGap_nonneg _)
      unfold spectralGap
      apply ContinuousLinearMap.opNorm_le_bound _ le_rfl
      intro x; simp [Subsingleton.elim x 0]
    rw [hsg]
    -- rvwBound ≥ 0: a + √(a² + b²) ≥ 0 since √(a² + b²) ≥ √(a²) = |a| ≥ -a
    unfold rvwBound
    have hsq : ((1 - lam₂ ^ 2) * lam₁ / 2) ^ 2 ≤
        (1 - lam₂ ^ 2) ^ 2 * lam₁ ^ 2 / 4 + lam₂ ^ 2 := by nlinarith [sq_nonneg lam₂]
    have h1 : |(1 - lam₂ ^ 2) * lam₁ / 2| ≤
        √((1 - lam₂ ^ 2) ^ 2 * lam₁ ^ 2 / 4 + lam₂ ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hsq
    linarith [neg_abs_le ((1 - lam₂ ^ 2) * lam₁ / 2)]
  -- Main case: n₁ * d₁ > 0, so d₁ > 0
  have hd₁ : 0 < d₁ := pos_of_mul_pos_right hpos (Nat.zero_le n₁)
  -- Abbreviate operators
  set B := withinClusterCLM (n₁ := n₁) G₂ hd₁
  set Sig := stepPermCLM G₁ hd₁
  set Q := clusterMeanCLM (n₁ := n₁) hd₁
  set P := (meanCLM (n₁ * d₁) : EuclideanSpace ℝ (Fin (n₁ * d₁)) →L[ℝ] _)
  -- Derive h_tilde from withinCluster_tilde_contraction
  have h_tilde : ∀ x, Q x = 0 → ‖B x‖ ≤ lam₂ * ‖x‖ := by
    intro x hQx
    have h1 : (1 - Q) x = x := by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hQx, sub_zero]
    calc ‖B x‖
        = ‖(B * (1 - Q)) x‖ := by rw [ContinuousLinearMap.mul_apply, h1]
      _ ≤ ‖B * (1 - Q)‖ * ‖x‖ := (B * (1 - Q)).le_opNorm x
      _ ≤ spectralGap G₂ * ‖x‖ := by
          exact mul_le_mul_of_nonneg_right
            (withinCluster_tilde_contraction G₂ hd₁) (norm_nonneg x)
      _ ≤ lam₂ * ‖x‖ := mul_le_mul_of_nonneg_right hG₂ (norm_nonneg x)
  -- Apply the abstract RVW operator norm bound
  show ‖(G₁.zigzag G₂).walkCLM - meanCLM (n₁ * d₁)‖ ≤ rvwBound lam₁ lam₂
  exact rvw_operator_norm_bound hpos
    ((G₁.zigzag G₂).walkCLM) B Sig Q P
    (zigzag_walkCLM_eq G₁ G₂ hd₁ hd₂)
    (clusterMeanCLM_idempotent hd₁)
    (clusterMeanCLM_isSelfAdjoint hd₁)
    (withinCluster_comp_clusterMean G₂ hd₁ hd₂)
    (clusterMean_comp_withinCluster G₂ hd₁ hd₂)
    (withinClusterCLM_isSelfAdjoint G₂ hd₁)
    (withinClusterCLM_norm_le_one G₂ hd₁)
    (stepPermCLM_sq_eq_one G₁ hd₁)
    (stepPermCLM_isSelfAdjoint G₁ hd₁)
    (stepPermCLM_comp_meanCLM G₁ hd₁)
    (meanCLM_idempotent (n₁ * d₁))
    (meanCLM_isSelfAdjoint (n₁ * d₁))
    (meanCLM_eq_clusterMean_comp hd₁)
    (clusterMean_comp_meanCLM hd₁)
    lam₁ lam₂ hlam₁ hlam₂
    hlam₁_le hlam₂_le
    h_tilde
    ((hat_block_norm G₁ hd₁).trans hG₁)


/-! **The Iterated Construction** -/

/- The RVW expander family, built by iterating:

      G_{k+1} := (G_k)² ⓩ H₀

    where H₀ is a D-regular base expander on D⁴ vertices.

    Properties at each step:
    • G_k is D²-regular (constant degree!)
    • G_k² is D⁴-regular
    • Zig-zag with H₀ (D⁴ vertices, D-regular) restores D²-regularity
    • n_k = D^(4(k+1)) vertices (exponential growth)
    • λ(G_k) ≤ c < 1 (constant spectral gap, from `zigzagFamily_gap`)

    For the concrete instantiation with `baseExpander` (D = 12):
    D² = 144, D⁴ = 20736, `baseExpander_gap ≤ 5/9`, family spectral gap ≤ 93/100.

    The key point: the degree D² is a CONSTANT independent of n,
    which is what we need for the AKS sorting network. -/

/-- Build the k-th graph in the zig-zag iteration.
    Given a D-regular base expander `H₀` on D⁴ vertices,
    returns D²-regular graphs with exponentially growing vertex count. -/
noncomputable def zigzagFamily {D : ℕ} (H₀ : RegularGraph ((D * D) * (D * D)) D) :
    ℕ → Σ (n : ℕ), RegularGraph n (D * D)
  | 0 => ⟨(D * D) * (D * D), H₀.square⟩
  | k + 1 =>
    let ⟨nₖ, Gₖ⟩ := zigzagFamily H₀ k
    -- Gₖ.square : RegularGraph nₖ ((D*D)*(D*D)), matching H₀'s vertex count
    -- Gₖ.square.zigzag H₀ : RegularGraph (nₖ * ((D*D)*(D*D))) (D*D)
    ⟨nₖ * ((D * D) * (D * D)), Gₖ.square.zigzag H₀⟩

/-- The spectral gap stays bounded at every level of the iteration.
    The hypotheses encode the fixed-point condition for the precise RVW
    recurrence: we need the base case `β² ≤ c` and the inductive step
    `rvwBound (c²) β ≤ c` (i.e., c is a fixed point of x ↦ rvwBound(x², β)).
    The fixed point exists when β² < 1/3, which holds for D ≥ 12. -/
theorem zigzagFamily_gap {D : ℕ} {H₀ : RegularGraph ((D * D) * (D * D)) D}
    {β c : ℝ} (hD : 0 < D) (hβ : spectralGap H₀ ≤ β) (hβ_le : β ≤ 1)
    (hbase : β ^ 2 ≤ c) (hc_le : c ≤ 1)
    (hiter : rvwBound (c ^ 2) β ≤ c) (k : ℕ) :
    spectralGap (zigzagFamily H₀ k).2 ≤ c := by
  induction k with
  | zero =>
    show spectralGap H₀.square ≤ c
    rw [spectralGap_square]
    exact (pow_le_pow_left₀ (spectralGap_nonneg _) hβ 2).trans hbase
  | succ k ih =>
    show spectralGap ((zigzagFamily H₀ k).2.square.zigzag H₀) ≤ c
    have h₁ : spectralGap (zigzagFamily H₀ k).2.square ≤ c ^ 2 := by
      rw [spectralGap_square]
      exact pow_le_pow_left₀ (spectralGap_nonneg _) ih 2
    have hc2_le : c ^ 2 ≤ 1 := by nlinarith [sq_nonneg c]
    exact (zigzag_spectral_bound _ _ _ _ h₁ hc2_le hβ hβ_le hD).trans hiter


/-! **The Main Result** -/

/-- **Explicit expander families exist** (via zig-zag).

    Given a D-regular base expander `H₀` on D⁴ vertices with spectral gap ≤ β,
    and constants satisfying the iteration fixed-point conditions, there is a
    D²-regular expander family with spectral gap ≤ c at every size.

    To get expanders at EVERY size n (not just n = D^(4(k+1))):
    pick k such that `zigzagFamily H₀ k` has ≥ n vertices, then take
    an induced subgraph (Cauchy interlacing preserves spectral gap). -/
theorem explicit_expanders_exist_zigzag {D : ℕ}
    {H₀ : RegularGraph ((D * D) * (D * D)) D}
    {β c : ℝ} (hβ : spectralGap H₀ ≤ β) (hβ_le : β ≤ 1)
    (hbase : β ^ 2 ≤ c) (hc_le : c ≤ 1)
    (hiter : rvwBound (c ^ 2) β ≤ c) :
    ∀ (n : ℕ), n > 0 →
    ∃ (G : RegularGraph n (D * D)), spectralGap G ≤ c := by
  -- For each n, find k such that zigzagFamily H₀ k has ≥ n vertices,
  -- then take an induced subgraph on n vertices.
  -- (Subgraph spectral gap can only improve: fewer paths = less mixing,
  --  but formally this needs the Cauchy interlacing theorem.)
  --
  -- The family `zigzagFamily H₀ k` satisfies `zigzagFamily_gap hD hβ hbase hiter k`.
  sorry

-- The `zigzag_implies_aks_network` theorem connecting this to the AKS
-- sorting network construction is in the root AKS.lean module, since it
-- references types from both `AKS.Basic` and `AKS.ZigZag`.
