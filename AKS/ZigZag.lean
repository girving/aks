/-
  # Explicit Expanders via the Zig-Zag Product

  Lean 4 formalization of the Reingold–Vadhan–Wigderson (2002) zig-zag
  product and its application to constructing explicit expander families.

  General regular graph theory (`RegularGraph`, spectral gap, squaring,
  complete graph) lives in `RegularGraph.lean`. This file builds on it
  with the zig-zag product, spectral composition theorem, and the
  iterated construction that yields expanders at every size.
-/

import AKS.ZigZagSpectral
import AKS.RVWBound
import AKS.Square
import AKS.Random

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
    (hG₁ : spectralGap G₁ ≤ lam₁)
    (hG₂ : spectralGap G₂ ≤ lam₂) :
    spectralGap (G₁.zigzag G₂) ≤ rvwBound lam₁ lam₂ := by
  -- Assembly proof: plugs the sublemmas from ZigZagOperators, ZigZagSpectral,
  -- and RVWBound together.
  --
  -- Step 1: Handle degenerate cases (d₁ = 0 or d₂ = 0).
  -- Step 2: Rewrite walkCLM using zigzag_walkCLM_eq: W_Z = B · Σ · B.
  -- Step 3: Apply rvw_operator_norm_bound with:
  --   B = withinClusterCLM G₂, Σ = stepPermCLM G₁, Q = clusterMeanCLM, P = meanCLM
  --   feeding in all the algebraic properties from ZigZagSpectral.lean.
  -- Step 4: Chain with rvwBound_mono_left/right to pass from spectralGap to lam₁/lam₂.
  sorry


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
    {β c : ℝ} (hβ : spectralGap H₀ ≤ β) (hbase : β ^ 2 ≤ c)
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
    exact (zigzag_spectral_bound _ _ _ _ h₁ hβ).trans hiter


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
    {β c : ℝ} (hβ : spectralGap H₀ ≤ β) (hbase : β ^ 2 ≤ c)
    (hiter : rvwBound (c ^ 2) β ≤ c) :
    ∀ (n : ℕ), n > 0 →
    ∃ (G : RegularGraph n (D * D)), spectralGap G ≤ c := by
  -- For each n, find k such that zigzagFamily H₀ k has ≥ n vertices,
  -- then take an induced subgraph on n vertices.
  -- (Subgraph spectral gap can only improve: fewer paths = less mixing,
  --  but formally this needs the Cauchy interlacing theorem.)
  --
  -- The family `zigzagFamily H₀ k` satisfies `zigzagFamily_gap hβ hbase hiter k`.
  sorry

-- The `zigzag_implies_aks_network` theorem connecting this to the AKS
-- sorting network construction is in the root AKS.lean module, since it
-- references types from both `AKS.Basic` and `AKS.ZigZag`.
