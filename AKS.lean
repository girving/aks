import AKS.Basic
import AKS.ZigZag

/-- **Connection to AKS:** This result plugs directly into the
    AKS sorting network construction.

    With an explicit (n, d, lam)-expander family where d and lam are
    constants, we get:
    - eps-halvers of depth 1 and size O(n)
    - AKS sorting network of depth O(log n) and size O(n log n) -/
theorem zigzag_implies_aks_network :
    (∃ (d : ℕ), ∀ n, n > 0 → ∃ (G : RegularGraph n d), spectralGap G ≤ 99/100) →
    ∃ (c : ℝ), c > 0 ∧ ∀ (n : ℕ), n ≥ 2 →
    ∃ (net : ComparatorNetwork n),
      IsSortingNetwork net ∧
      (net.depth : ℝ) ≤ c * Real.log n ∧
      (net.size : ℝ) ≤ c * n * Real.log n := by
  sorry
