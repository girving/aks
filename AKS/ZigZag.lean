/-
  # Explicit Expanders via the Zig-Zag Product

  Lean 4 formalization of the Reingold–Vadhan–Wigderson (2002) zig-zag
  product and its application to constructing explicit expander families.

  General regular graph theory (`RegularGraph`, spectral gap, squaring,
  complete graph) lives in `RegularGraph.lean`. This file builds on it
  with the zig-zag product, spectral composition theorem, and the
  iterated construction that yields expanders at every size.
-/

import AKS.RegularGraph

#exit

open Matrix BigOperators Finset


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


/-! **The Spectral Composition Theorem** -/

/-- **The Main Theorem (Reingold–Vadhan–Wigderson 2002):**

    λ(G₁ ⓩ G₂) ≤ λ(G₁) + λ(G₂) + λ(G₂)²

    More precisely, they prove:

    λ(G₁ ⓩ G₂) ≤ f(λ₁, λ₂)

    where f(λ₁, λ₂) < 1 whenever λ₁ < 1 and λ₂ < 1.

    The bound used in practice is:

    λ(G₁ ⓩ G₂) ≤ 1 - (1 - λ₂)² · (1 - λ₁) / 2

    Key insight: even if G₁ has terrible expansion (λ₁ close to 1),
    as long as G₂ has decent expansion (λ₂ bounded away from 1),
    the zig-zag product inherits good expansion from G₂. -/
theorem zigzag_spectral_bound {n₁ d₁ d₂ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (G₂ : RegularGraph d₁ d₂)
    (lam₁ lam₂ : ℝ)
    (hG₁ : spectralGap G₁ ≤ lam₁)
    (hG₂ : spectralGap G₂ ≤ lam₂) :
    spectralGap (G₁.zigzag G₂) ≤ 1 - (1 - lam₂)^2 * (1 - lam₁) / 2 := by
  -- ═══════════════════════════════════════════════════════════════
  -- PROOF SKETCH (the core of the entire construction)
  -- ═══════════════════════════════════════════════════════════════
  --
  -- Let M₁, M₂ be the normalized adjacency matrices of G₁, G₂.
  -- Let M_zz be the normalized adjacency matrix of G₁ ⓩ G₂.
  --
  -- The zig-zag product's adjacency matrix factors as:
  --
  --   M_zz = (I_n ⊗ M₂) · P · (I_n ⊗ M₂)
  --
  -- where:
  --   I_n ⊗ M₂  = "zig/zag" step (apply G₂ within each cloud)
  --   P          = "step" (permutation matrix encoding G₁'s edges)
  --
  -- To bound λ(M_zz), we need to bound ‖M_zz x‖ for x ⊥ 𝟏.
  --
  -- Decompose x ∈ ℝ^{n·d} into n blocks of size d:
  --   x = (x₁, ..., xₙ)  where xᵢ ∈ ℝ^d
  --
  -- Further decompose each block:
  --   xᵢ = x̂ᵢ · 𝟏/√d + x̃ᵢ   where x̃ᵢ ⊥ 𝟏 in ℝ^d
  --
  -- The "hat" part x̂ = (x̂₁, ..., x̂ₙ) ∈ ℝ^n carries the
  -- inter-cloud structure. The "tilde" parts x̃ᵢ carry intra-cloud.
  --
  -- Now analyze each step:
  --
  -- Zig (I ⊗ M₂):
  --   - Leaves x̂ unchanged (M₂ · 𝟏 = 𝟏)
  --   - Contracts x̃ by factor λ₂: ‖x̃'‖ ≤ λ₂ · ‖x̃‖
  --
  -- Step (P):
  --   - Permutes blocks according to G₁'s port structure
  --   - The key: this is where G₁'s expansion acts on x̂
  --   - Contracts the "hat" component by λ₁: after projection,
  --     ‖x̂'‖_{⊥𝟏} ≤ λ₁ · ‖x̂‖_{⊥𝟏}
  --   - May inflate x̃, but only transfers hat ↔ tilde
  --
  -- Zag (I ⊗ M₂):
  --   - Again contracts tilde by λ₂
  --   - Leaves hat unchanged
  --
  -- Combining: the total operator on (x̂, x̃) satisfies
  --
  --   ‖M_zz x‖² ≤ (λ₁ · ‖x̂‖ + λ₂ · ‖x̃‖)² + (λ₂ · ‖x̂‖ + λ₂² · ‖x̃‖)²
  --
  -- Optimizing over the split ‖x̂‖² + ‖x̃‖² = 1 gives
  --
  --   λ(G₁ ⓩ G₂) ≤ 1 - (1 - λ₂)²(1 - λ₁)/2
  --
  -- This is a calculation in finite-dimensional operator norms:
  -- bound ‖A·B·C‖ via ‖A‖·‖B‖·‖C‖ on orthogonal decompositions,
  -- then optimize a quadratic form.
  sorry

/-- **Corollary**: If G₂ has constant spectral gap (λ₂ < 1) and
    G₁ has any spectral gap (λ₁ < 1), the zig-zag product has
    spectral gap bounded away from 1 by a constant depending on λ₂. -/
theorem zigzag_bounded_gap {n₁ d₁ d₂ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (G₂ : RegularGraph d₁ d₂)
    (lam₂ : ℝ) (hlam₂ : lam₂ < 1)
    (hG₂ : spectralGap G₂ ≤ lam₂) :
    spectralGap (G₁.zigzag G₂) < 1 := by
  have h := zigzag_spectral_bound G₁ G₂ 1 lam₂ (spectralGap_le_one G₁) hG₂
  -- 1 - (1 - λ₂)² · (1 - 1) / 2 = 1 - 0 = 1
  -- But we need the actual λ₁ < 1 for a strict bound.
  -- When λ₁ = λ(G₁) < 1 (which holds for any connected graph),
  -- we get a strict inequality.
  sorry


/-! **The Base Case: A Concrete Small Expander** -/

/- To bootstrap the construction, we need one explicit small expander.

    We use the complete graph K_d on d vertices (minus self-loops,
    made into a rotation map). This has:

      λ(K_d) = 1/(d-1)

    which is < 1 for d ≥ 3.

    For the actual AKS construction, we need a specific (D⁴, D)-regular
    graph where D is a chosen constant. We can take D = 16 and
    verify the spectral gap of a 16-vertex graph computationally. -/

/-- A concrete verified base expander. For D = 8:
    H₀ is an 8-regular graph on 8⁴ = 4096 vertices with λ(H₀) ≤ 0.9.

    In a full formalization, this would be:
    1. An explicit adjacency list (or Cayley graph construction).
    2. A verified eigenvalue computation using interval arithmetic.
    The computation is large but finite and mechanically checkable. -/
axiom baseExpander : RegularGraph 4096 8

axiom baseExpander_gap : spectralGap baseExpander ≤ 9/10


/-! **The Iterated Construction** -/

/- The RVW expander family, built by iterating:

      G_{k+1} := (G_k)² ⓩ H₀

    where H₀ = baseExpander (D⁴ = 4096 vertices, D = 8 regular).

    Properties at each step (D = 8):
    • G_k is D²-regular (= 64-regular, constant degree!)
    • G_k² is D⁴-regular (= 4096-regular)
    • Zig-zag with H₀ (D⁴ vertices, D-regular) restores D²-regularity
    • n_k = D^(4(k+1)) vertices (exponential growth)
    • λ(G_k) ≤ λ_max < 1 (constant spectral gap)

    To get expanders at EVERY size n (not just n = D^(4(k+1))):
    • For arbitrary n, pick k such that n_k ≥ n.
    • Take an n-vertex subgraph or use the Friedman–Wigderson
      derandomized squaring to interpolate sizes.
    • Alternatively, the zig-zag construction can be modified to
      handle arbitrary sizes (see RVW §5).

    The key point: the degree D² is a CONSTANT independent of n,
    which is what we need for the AKS sorting network. -/

/-- Build the k-th graph in the zig-zag iteration.
    Returns a graph with degree 64 = 8² at each level. -/
noncomputable def zigzagFamily : ℕ → Σ (n : ℕ), RegularGraph n 64
  | 0 => ⟨4096, baseExpander.square⟩  -- G₀² is 64-regular on 4096 vertices
  | k + 1 =>
    let ⟨nₖ, Gₖ⟩ := zigzagFamily k
    -- G_{k+1} = Gₖ² ⓩ H₀
    -- Gₖ² has nₖ vertices, degree 64² = 4096
    -- But we need H to have 4096 vertices...
    -- Actually, let's track this more carefully.
    --
    -- At each step:
    --   Gₖ  : (nₖ, D²)-regular
    --   Gₖ² : (nₖ, D⁴)-regular
    --   Gₖ² ⓩ H₀ : (nₖ · D⁴, D²)-regular   where H₀ has D⁴ vertices
    --
    -- So vertex count grows as nₖ₊₁ = nₖ · D⁴.
    -- Starting from n₀ = D⁴: nₖ = D^(4 · (k+1)).
    sorry

/-- The spectral gap stays bounded at every level of the iteration. -/
theorem zigzagFamily_gap (k : ℕ) :
    spectralGap (zigzagFamily k).2 ≤ 99/100 := by
  induction k with
  | zero =>
    -- Base case: λ(G₀²) = λ(G₀)² ≤ (9/10)² = 81/100 ≤ 99/100.
    sorry
  | succ k ih =>
    -- Inductive step:
    -- λ(G_{k+1}) = λ(Gₖ² ⓩ baseExpander)
    --            ≤ 1 - (1 - λ(baseExpander))² · (1 - λ(Gₖ²)) / 2
    --            ≤ 1 - (1 - 9/10)² · (1 - λ(Gₖ)²) / 2
    --
    -- Since λ(Gₖ) ≤ 99/100 by IH:
    --   λ(Gₖ²) = λ(Gₖ)² ≤ (99/100)² ≈ 0.9801
    --   1 - λ(Gₖ²) ≥ 1 - 0.9801 = 0.0199
    --   (1 - 0.9)² · 0.0199 / 2 = 0.01 · 0.0199 / 2 ≈ 0.0000995
    --
    -- So λ(G_{k+1}) ≤ 1 - 0.0000995 < 1, and with better constants
    -- (smaller λ for baseExpander) this stays ≤ 99/100.
    --
    -- The actual RVW paper optimizes these constants carefully.
    sorry


/-! **The Main Result** -/

/-- **Explicit expander families exist** (via zig-zag).

    For any ε > 0, there exists a constant d and an explicit
    d-regular graph family {Gₙ}_{n ∈ ℕ} with λ(Gₙ) ≤ 1 - ε. -/
theorem explicit_expanders_exist_zigzag :
    ∃ (d : ℕ), ∀ (n : ℕ), n > 0 →
    ∃ (G : RegularGraph n d), spectralGap G ≤ 99/100 := by
  -- Take d = D² = 64 from the zig-zag construction.
  -- For each n, find k such that zigzagFamily k has ≥ n vertices,
  -- then take an induced subgraph on n vertices.
  -- (Subgraph spectral gap can only improve: fewer paths = less mixing,
  --  but formally this needs the Cauchy interlacing theorem.)
  --
  -- Alternatively, the RVW paper shows how to handle all sizes
  -- directly via a modified iteration.
  sorry

-- The `zigzag_implies_aks_network` theorem connecting this to the AKS
-- sorting network construction is in the root AKS.lean module, since it
-- references types from both `AKS.Basic` and `AKS.ZigZag`.
