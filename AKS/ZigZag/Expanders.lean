module
/-
  # Explicit Expanders via the Zig-Zag Product

  Lean formalization of the Reingold–Vadhan–Wigderson (2002) zig-zag
  product and its application to constructing explicit expander families.

  General regular graph theory (`RegularGraph`, spectral gap, squaring,
  complete graph) lives in `Graph/Regular.lean`. This file builds on it
  with the zig-zag product, spectral composition theorem, and the
  iterated construction that yields expanders at every size.
-/

public import AKS.ZigZag.Spectral
public import AKS.ZigZag.RVWBound
public import AKS.Graph.Square
public import AKS.Graph.Walk

@[expose] public section


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
  exact rvw_operator_norm_bound
    ((G₁.zigzag G₂).walkCLM) B Sig Q P
    (zigzag_walkCLM_eq G₁ G₂ hd₁ hd₂)
    (clusterMeanCLM_idempotent hd₁)
    (clusterMeanCLM_isSelfAdjoint hd₁)
    (withinCluster_comp_clusterMean G₂ hd₁ hd₂)
    (clusterMean_comp_withinCluster G₂ hd₁ hd₂)
    (withinClusterCLM_isSelfAdjoint G₂ hd₁)
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

    For the concrete instantiation with `Random20736.graph` (D = 12):
    D² = 144, D⁴ = 20736, spectral gap ≤ 10/12, family spectral gap ≤ 93/100.

    The key point: the degree D² is a CONSTANT independent of n,
    which is what we need for the AKS sorting network. -/

/-- Build the k-th graph in the zig-zag iteration.
    Given a D-regular base expander `H₀` on D⁴ vertices,
    returns D²-regular graphs with exponentially growing vertex count. -/
def zigzagFamily {D : ℕ} (H₀ : RegularGraph ((D * D) * (D * D)) D) :
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


/-! **Family Size** -/

/-- The vertex count at level `k` is `B^(k+1)` where `B = (D*D)*(D*D)`. -/
theorem zigzagFamily_size {D : ℕ} (H₀ : RegularGraph ((D * D) * (D * D)) D) (k : ℕ) :
    (zigzagFamily H₀ k).1 = ((D * D) * (D * D)) ^ (k + 1) := by
  induction k with
  | zero => simp [zigzagFamily, pow_one]
  | succ k ih => simp only [zigzagFamily, ih]; ring

/-- For any `n`, there exists a level `k` such that the family has ≥ `n` vertices.
    Since `B = (D*D)*(D*D) ≥ 16` when `D ≥ 2`, we have `B^(n+1) ≥ 2^n > n`. -/
theorem exists_zigzagFamily_ge {D : ℕ} (hD : 2 ≤ D)
    (H₀ : RegularGraph ((D * D) * (D * D)) D) (n : ℕ) :
    ∃ k, n ≤ (zigzagFamily H₀ k).1 := by
  use n
  rw [zigzagFamily_size]
  have hB : 2 ≤ (D * D) * (D * D) := by
    have : 4 ≤ D * D := by nlinarith
    nlinarith
  exact le_of_lt (calc
    n < 2 ^ n := Nat.lt_two_pow_self
    _ ≤ ((D * D) * (D * D)) ^ n := Nat.pow_le_pow_left hB n
    _ ≤ ((D * D) * (D * D)) ^ (n + 1) :=
        Nat.pow_le_pow_right (by omega : 0 < (D * D) * (D * D)) (Nat.le_succ n))


/-! **Contracted Expanders at Arbitrary Sizes** -/

/- Note: `contractedExpander` and `explicit_expanders_graph` are NOT used by the
   sorting network pipeline. The actual path is `seiferasNetworkPow2` in
   `Seiferas.lean`, which uses equal-fiber contraction at power-of-2 sizes,
   giving regular graphs directly. These contracted-expander defs
   are kept as a weaker alternative that works at every size (producing irregular
   `Graph n` instead of `RegularGraph n d`). -/

/-- Smallest `k` such that `zigzagFamily H₀ k` has ≥ `n` vertices.
    Uses fuel-bounded search; `k = O(log n / log D⁴)`. -/
def zigzagLevel {D : ℕ} (H₀ : RegularGraph ((D * D) * (D * D)) D)
    (n : ℕ) : ℕ :=
  go H₀ n 0 (n + 1)
where
  go {D : ℕ} (H₀ : RegularGraph ((D * D) * (D * D)) D)
      (n k fuel : ℕ) : ℕ :=
    if n ≤ (zigzagFamily H₀ k).1 then k
    else match fuel with
    | 0 => k
    | fuel' + 1 => go H₀ n (k + 1) fuel'

private theorem zigzagLevel_go_ge {D : ℕ}
    (H₀ : RegularGraph ((D * D) * (D * D)) D)
    (n : ℕ) (k fuel : ℕ) (h : n ≤ (zigzagFamily H₀ (k + fuel)).1) :
    n ≤ (zigzagFamily H₀ (zigzagLevel.go H₀ n k fuel)).1 := by
  induction fuel generalizing k with
  | zero => simp only [zigzagLevel.go]; split <;> assumption
  | succ fuel' ih =>
    simp only [zigzagLevel.go]
    split
    · assumption
    · exact ih (k + 1) (by
        have : k + 1 + fuel' = k + (fuel' + 1) := by omega
        rwa [this])

theorem zigzagLevel_ge {D : ℕ} (hD : 2 ≤ D)
    (H₀ : RegularGraph ((D * D) * (D * D)) D) (n : ℕ) :
    n ≤ (zigzagFamily H₀ (zigzagLevel H₀ n)).1 := by
  have hB : 2 ≤ (D * D) * (D * D) := by
    have : 2 ≤ D * D := by nlinarith
    nlinarith
  exact zigzagLevel_go_ge H₀ n 0 (n + 1) (by
    rw [Nat.zero_add, zigzagFamily_size]
    exact le_of_lt (calc
      n < 2 ^ n := Nat.lt_two_pow_self
      _ ≤ ((D * D) * (D * D)) ^ n := Nat.pow_le_pow_left hB n
      _ ≤ ((D * D) * (D * D)) ^ (n + 1 + 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)))

private theorem zigzagLevel_go_min {D : ℕ}
    (H₀ : RegularGraph ((D * D) * (D * D)) D)
    (n k fuel : ℕ) (j : ℕ) (hjk : k ≤ j)
    (hj : j < zigzagLevel.go H₀ n k fuel) :
    ¬(n ≤ (zigzagFamily H₀ j).1) := by
  induction fuel generalizing k with
  | zero => simp only [zigzagLevel.go] at hj; split at hj <;> omega
  | succ fuel' ih =>
    simp only [zigzagLevel.go] at hj
    split at hj
    · omega
    · next h =>
      rcases eq_or_lt_of_le hjk with rfl | hjk'
      · exact h
      · exact ih (k + 1) (by omega) hj

/-- `zigzagLevel` returns the smallest `k` such that
    `n ≤ (zigzagFamily H₀ k).1`. -/
theorem zigzagLevel_min {D : ℕ} (_hD : 2 ≤ D)
    (H₀ : RegularGraph ((D * D) * (D * D)) D) (n : ℕ)
    (j : ℕ) (hj : j < zigzagLevel H₀ n) :
    ¬(n ≤ (zigzagFamily H₀ j).1) :=
  zigzagLevel_go_min H₀ n 0 (n + 1) j (Nat.zero_le j) hj

/-- An expander at any target size `n`, built by contracting an oversized
    zig-zag family member. The result is a `Graph n` (possibly irregular)
    with spectral gap ≤ `c`.

    Uses `zigzagLevel` to pick the smallest sufficient family member,
    so the contracted graph has degree `O(D⁶)` (constant in `n`). -/
def contractedExpander {D : ℕ}
    (H₀ : RegularGraph ((D * D) * (D * D)) D)
    (n : ℕ) (hn : 0 < n) : Graph n :=
  let k := zigzagLevel H₀ n
  (zigzagFamily H₀ k).2.toGraph.contract (fun v => ⟨v.val % n, Nat.mod_lt _ hn⟩)

/-- The spectral gap of the contracted expander is bounded by the family's
    fixed-point constant `c`. Chains three proved results:
    1. `Graph.spectralGap_contract`: contraction can only decrease spectral gap
    2. `spectralGap_toGraph`: `Graph.spectralGap` agrees with `spectralGap` for regular graphs
    3. `zigzagFamily_gap`: the family's spectral gap is bounded by `c` -/
theorem contractedExpander_spectralGap {D : ℕ} (hD : 2 ≤ D)
    {H₀ : RegularGraph ((D * D) * (D * D)) D}
    {β c : ℝ} (hβ : spectralGap H₀ ≤ β) (hβ_le : β ≤ 1)
    (hbase : β ^ 2 ≤ c) (hc_le : c ≤ 1)
    (hiter : rvwBound (c ^ 2) β ≤ c) (n : ℕ) (hn : 0 < n) :
    (contractedExpander H₀ n hn).spectralGap ≤ c := by
  set k := zigzagLevel H₀ n
  set Gk := (zigzagFamily H₀ k).2
  show (Gk.toGraph.contract _).spectralGap ≤ c
  calc (Gk.toGraph.contract _).spectralGap
      ≤ Gk.toGraph.spectralGap := Graph.spectralGap_contract _ _
    _ = spectralGap Gk := spectralGap_toGraph Gk (show 0 < D * D by nlinarith)
    _ ≤ c := zigzagFamily_gap (show 0 < D by omega) hβ hβ_le hbase hc_le hiter k

/-- **Explicit expanders at every positive size** (via contraction).

    Given a D-regular base expander `H₀` on D⁴ vertices with spectral gap ≤ β,
    and constants satisfying the iteration fixed-point conditions, there is
    an expander graph with spectral gap ≤ c at every positive size `n`.

    The result is a `Graph n` which may be irregular. -/
theorem explicit_expanders_graph {D : ℕ} (hD : 2 ≤ D)
    {H₀ : RegularGraph ((D * D) * (D * D)) D}
    {β c : ℝ} (hβ : spectralGap H₀ ≤ β) (hβ_le : β ≤ 1)
    (hbase : β ^ 2 ≤ c) (hc_le : c ≤ 1)
    (hiter : rvwBound (c ^ 2) β ≤ c) :
    ∀ n, n > 0 → ∃ G : Graph n, G.spectralGap ≤ c :=
  fun n hn => ⟨contractedExpander H₀ n hn,
    contractedExpander_spectralGap hD hβ hβ_le hbase hc_le hiter n hn⟩


/-! **Power-of-2 Helpers** -/

/-- For the smallest zigzag family level `k` with `B^(k+1) ≥ m`,
    the quotient `B^(k+1) / m` is at most `B`, giving `⌊N/m⌋ + 1 ≤ B + 1`.
    This provides a uniform upper bound on `d_max` across all target sizes `m`. -/
theorem zigzagFamily_min_div_bound {D : ℕ} (hD : 2 ≤ D)
    (H₀ : RegularGraph ((D * D) * (D * D)) D)
    {m : ℕ} (hm : 0 < m)
    (k : ℕ) (hk_min : ∀ j, j < k → ¬ (m ≤ (zigzagFamily H₀ j).1))
    (hge : m ≤ (zigzagFamily H₀ k).1) :
    (zigzagFamily H₀ k).1 / m + 1 ≤ (D * D) * (D * D) + 1 := by
  suffices h : (zigzagFamily H₀ k).1 / m ≤ (D * D) * (D * D) by omega
  have hBpos : 0 < (D * D) * (D * D) := by positivity
  rw [zigzagFamily_size]
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · -- k = 0: B^1 / m ≤ B
    simp only [Nat.zero_add, pow_one]
    exact Nat.div_le_self _ m
  · -- k ≥ 1: by minimality, previous level has < m vertices
    have hmin : ¬ (m ≤ (zigzagFamily H₀ (k - 1)).1) :=
      hk_min (k - 1) (Nat.sub_lt hk_pos Nat.one_pos)
    push_neg at hmin
    rw [zigzagFamily_size] at hmin
    have hk_eq : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk_pos
    rw [hk_eq] at hmin
    -- B^(k+1) = B^k * B ≤ m * B, so B^(k+1)/m ≤ m*B/m = B
    have hle : ((D*D)*(D*D)) ^ (k + 1) ≤ m * ((D*D)*(D*D)) := by
      rw [pow_succ]
      exact Nat.mul_le_mul_right _ (le_of_lt hmin)
    calc ((D*D)*(D*D)) ^ (k + 1) / m
        ≤ (m * ((D*D)*(D*D))) / m := Nat.div_le_div_right hle
      _ = (D*D)*(D*D) := Nat.mul_div_cancel_left _ hm

/-- For D a power of 2, zigzag family sizes are powers of 2.
    If `2^s ≤ B^(k+1) = 2^(4a(k+1))`, then `2^s ∣ B^(k+1)`. -/
theorem pow2_dvd_zigzagFamily {a : ℕ}
    (H₀ : RegularGraph ((2^a * 2^a) * (2^a * 2^a)) (2^a))
    (s k : ℕ) (hle : 2^s ≤ (zigzagFamily H₀ k).1) :
    2^s ∣ (zigzagFamily H₀ k).1 := by
  rw [zigzagFamily_size]
  have hB : (2^a * 2^a) * (2^a * 2^a) = 2^(4*a) := by ring
  rw [hB, ← pow_mul]
  apply Nat.pow_dvd_pow 2
  -- Need: s ≤ 4 * a * (k + 1)
  -- From hle: 2^s ≤ 2^(4*a*(k+1))
  by_contra h
  push_neg at h
  rw [zigzagFamily_size, hB, ← pow_mul] at hle
  exact absurd hle (not_le.mpr (Nat.pow_lt_pow_right (by omega) h))

end
