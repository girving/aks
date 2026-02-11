/-
  # Base Expander for the Zig-Zag Construction

  The iterated zig-zag construction (`zigzagFamily` in `ZigZag.lean`) requires
  a concrete "seed" expander: a D-regular graph on D⁴ vertices with spectral
  gap bounded by some constant β < 1.

  This file provides the base expander as axioms. Replacing these axioms with
  a concrete verified graph is an engineering task (see roadmap below).

  ## Roadmap for Replacing the Axioms

  1. **Generate a candidate graph.** Use a random D-regular graph on D⁴
     vertices (e.g., via the configuration model or random permutations).
     By Friedman's theorem, a random D-regular graph is nearly Ramanujan
     with high probability: spectral gap ≈ 2√(D-1)/D.

  2. **Numerically verify the spectral gap.** Compute eigenvalues of the
     adjacency matrix and check that all non-trivial eigenvalues satisfy
     |λᵢ|/D ≤ β.

  3. **Create a Lean certificate.** Encode the graph as an explicit rotation
     map `Fin n × Fin D → Fin n × Fin D` and verify:
     (a) The rotation map is an involution (decidable, `native_decide`).
     (b) The spectral gap bound, via either:
         - Interval arithmetic on the characteristic polynomial, or
         - A sum-of-squares certificate for the matrix inequality
           `(β²D² · I - A²) ≥ 0` on the orthogonal complement of constants.

  The choice of D depends on which spectral composition bound we use:
  - **Additive bound** (`λ₁ + λ₂ + λ₂²`): needs β ≤ (√2-1)/2 ≈ 0.207,
    which by Alon–Boppana requires D ≥ 99. The graph has ~10⁸ vertices.
  - **Precise RVW bound**: works for any D ≥ 2 and any β < 1. A Ramanujan
    graph with D = 16 (β ≈ 0.48, D⁴ = 65536 vertices) suffices.
-/

import AKS.RegularGraph


/-! **Base Expander Axioms** -/

/-- A concrete base expander. Currently axiomatized; see roadmap above.

    For D = 8: H₀ is an 8-regular graph on 8⁴ = 4096 vertices.
    The spectral gap bound `≤ 1/5` assumes either a Ramanujan-like
    construction or a verified random graph. -/
axiom baseExpander : RegularGraph 4096 8

/-- The spectral gap of the base expander is at most 1/5.

    Note: By Alon–Boppana, any 8-regular graph family has spectral gap
    ≥ 2√7/8 ≈ 0.661 asymptotically. So this bound (0.2) is only achievable
    for a SINGLE graph of moderate size (not a family), or requires
    increasing D. This axiom will be replaced when we settle on concrete
    parameters; see the roadmap above. -/
axiom baseExpander_gap : spectralGap baseExpander ≤ 1/5
