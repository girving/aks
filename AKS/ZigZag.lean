/-
  # Explicit Expanders via the Zig-Zag Product

  Lean 4 formalization of the Reingold–Vadhan–Wigderson (2002) zig-zag
  product and its application to constructing explicit expander families.

  General regular graph theory (`RegularGraph`, spectral gap, squaring,
  complete graph) lives in `RegularGraph.lean`. This file builds on it
  with the zig-zag product, spectral composition theorem, and the
  iterated construction that yields expanders at every size.
-/

import AKS.Square

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

    λ(G₁ ⓩ G₂) ≤ λ₁ + λ₂ + λ₂²

    This is the additive form of the RVW spectral composition theorem.
    It follows from the precise bound f(λ₁, λ₂) = (1−λ₂²)λ₁/2 + √((1−λ₂²)²λ₁²/4 + λ₂²)
    via √(a² + b²) ≤ a + b, giving f ≤ λ₁ + λ₂.

    The additive bound is most useful when both spectral gaps are small
    (e.g., after squaring), which is exactly the regime of the iterated
    construction. -/
theorem zigzag_spectral_bound {n₁ d₁ d₂ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (G₂ : RegularGraph d₁ d₂)
    (lam₁ lam₂ : ℝ)
    (hG₁ : spectralGap G₁ ≤ lam₁)
    (hG₂ : spectralGap G₂ ≤ lam₂) :
    spectralGap (G₁.zigzag G₂) ≤ lam₁ + lam₂ + lam₂ ^ 2 := by
  -- Proof strategy:
  -- 1. The precise RVW bound gives f(λ₁, λ₂) = (1−λ₂²)λ₁/2 + √((1−λ₂²)²λ₁²/4 + λ₂²)
  -- 2. Show f is monotone in both arguments (to pass from spectralGap to lam₁/lam₂)
  -- 3. Simplify: √(a² + b²) ≤ a + b gives f ≤ (1−λ₂²)λ₁ + λ₂ ≤ λ₁ + λ₂ ≤ λ₁ + λ₂ + λ₂²
  --
  -- The hard part is step 1: decompose ℝ^{n·d} into n blocks of size d,
  -- project each block onto constants (hat) and orthogonal (tilde),
  -- then analyze the zig-zag walk's effect on each component.
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
    H₀ is an 8-regular graph on 8⁴ = 4096 vertices with λ(H₀) ≤ 1/5.

    In a full formalization, this would be:
    1. An explicit adjacency list (or Cayley graph construction).
    2. A verified eigenvalue computation using interval arithmetic.
    The computation is large but finite and mechanically checkable. -/
axiom baseExpander : RegularGraph 4096 8

axiom baseExpander_gap : spectralGap baseExpander ≤ 1/5


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
    -- Gₖ² : RegularGraph nₖ (64 * 64), i.e. 4096-regular
    -- baseExpander : RegularGraph 4096 8
    -- Gₖ².zigzag baseExpander : RegularGraph (nₖ * 4096) (8 * 8), i.e. 64-regular
    -- Lean reduces 64 * 64 = 4096 and 8 * 8 = 64 by native_decide/norm_num
    ⟨nₖ * 4096, Gₖ.square.zigzag baseExpander⟩

/-- The spectral gap stays bounded at every level of the iteration.
    With `baseExpander_gap ≤ 1/5`, the iteration converges to a fixed point ≈ 0.28.
    The bound 1/2 holds at every step: squaring gives ≤ 1/4, then zigzag adds
    at most 1/5 + 1/25 = 6/25, totaling 1/4 + 6/25 = 49/100 < 1/2. -/
theorem zigzagFamily_gap (k : ℕ) :
    spectralGap (zigzagFamily k).2 ≤ 1/2 := by
  induction k with
  | zero =>
    -- Base case: λ(G₀²) = λ(G₀)² ≤ (1/5)² = 1/25 ≤ 1/2.
    show spectralGap baseExpander.square ≤ 1 / 2
    rw [spectralGap_square]
    calc (spectralGap baseExpander) ^ 2
        ≤ (1 / 5 : ℝ) ^ 2 :=
          pow_le_pow_left₀ (spectralGap_nonneg _) baseExpander_gap 2
      _ ≤ 1 / 2 := by norm_num
  | succ k ih =>
    -- Inductive step: λ(Gₖ² ⓩ H₀) ≤ λ(Gₖ)² + λ(H₀) + λ(H₀)²
    --   ≤ (1/2)² + 1/5 + (1/5)² = 1/4 + 1/5 + 1/25 = 49/100 ≤ 1/2
    show spectralGap ((zigzagFamily k).2.square.zigzag baseExpander) ≤ 1 / 2
    have h₁ : spectralGap (zigzagFamily k).2.square ≤ 1 / 4 := by
      rw [spectralGap_square]
      calc (spectralGap (zigzagFamily k).2) ^ 2
          ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ (spectralGap_nonneg _) ih 2
        _ = 1 / 4 := by norm_num
    calc spectralGap ((zigzagFamily k).2.square.zigzag baseExpander)
        ≤ 1 / 4 + 1 / 5 + (1 / 5) ^ 2 :=
          zigzag_spectral_bound _ _ _ _ h₁ baseExpander_gap
      _ ≤ 1 / 2 := by norm_num


/-! **The Main Result** -/

/-- **Explicit expander families exist** (via zig-zag).

    For any ε > 0, there exists a constant d and an explicit
    d-regular graph family {Gₙ}_{n ∈ ℕ} with λ(Gₙ) ≤ 1 - ε. -/
theorem explicit_expanders_exist_zigzag :
    ∃ (d : ℕ), ∀ (n : ℕ), n > 0 →
    ∃ (G : RegularGraph n d), spectralGap G ≤ 1/2 := by
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
