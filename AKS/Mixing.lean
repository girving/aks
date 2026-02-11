/-
  # Expander Mixing Lemma

  The spectral gap controls edge distribution in regular graphs.
  This is the link between spectral and combinatorial expansion.
-/

import AKS.RegularGraph

open Matrix BigOperators Finset

/-- The Expander Mixing Lemma: the spectral gap controls edge
    distribution. For any two vertex sets S, T ⊆ V:

      |e(S,T)/d - |S|·|T|/n| ≤ λ(G) · √(|S|·|T|)

    This is the link between spectral and combinatorial expansion. -/
theorem expander_mixing_lemma {n d : ℕ} (G : RegularGraph n d)
    (S T : Finset (Fin n)) :
    |((Finset.sum S fun v ↦ (T.filter (fun u ↦
        ∃ i : Fin d, G.neighbor v i = u)).card) : ℝ) / d
      - S.card * T.card / n|
    ≤ spectralGap G * Real.sqrt (S.card * T.card) := by
  sorry
