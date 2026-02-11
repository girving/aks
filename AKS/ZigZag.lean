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
import AKS.Random

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

    For the concrete instantiation with `baseExpander` (D = 8):
    D² = 64, D⁴ = 4096, `baseExpander_gap ≤ 1/5`, spectral gap ≤ 1/2.

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
    The hypotheses encode the fixed-point condition for the recurrence
    λ_{k+1} ≤ λ_k² + β + β²: we need the base case `β² ≤ c` and the
    inductive step `c² + β + β² ≤ c`. -/
theorem zigzagFamily_gap {D : ℕ} {H₀ : RegularGraph ((D * D) * (D * D)) D}
    {β c : ℝ} (hβ : spectralGap H₀ ≤ β) (hbase : β ^ 2 ≤ c)
    (hiter : c ^ 2 + β + β ^ 2 ≤ c) (k : ℕ) :
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
    (hiter : c ^ 2 + β + β ^ 2 ≤ c) :
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
