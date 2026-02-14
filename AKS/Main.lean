/-
  # AKS Main Assembly

  Assembles the concrete zig-zag expander family with the parameterized
  AKS construction to produce the final unparameterized results.

  The key chain:
  1. `explicit_expanders_exist_zigzag` (ZigZag.lean): zig-zag expander family, gap ≤ c < 1
  2. Iterated squaring (`squareIter`): reduces spectral gap from c to c^(2^k) < 1/2
  3. `zigzag_implies_aks_network` (AKSNetwork.lean): expander family with gap < 1/2 → O(n log n) sorting networks
  4. This file: plug them together in `aks_sorting_networks_exist`
-/

import AKS.AKSNetwork
import AKS.ZigZag
import AKS.Square

open Real


/-! **Iterated Graph Squaring** -/

/-- Helper: cast a `RegularGraph` when the degree is propositionally equal. -/
private def RegularGraph.castDeg {n d₁ d₂ : ℕ} (h : d₁ = d₂) (G : RegularGraph n d₁) :
    RegularGraph n d₂ :=
  h ▸ G

private theorem spectralGap_castDeg {n d₁ d₂ : ℕ} (h : d₁ = d₂) (G : RegularGraph n d₁) :
    spectralGap (G.castDeg h) = spectralGap G := by
  subst h; rfl

/-- Iterated squaring of a regular graph.
    `G.squareIter k` squares the graph `k` times, yielding a
    `d^(2^k)`-regular graph on the same `n` vertices. -/
noncomputable def RegularGraph.squareIter {n d : ℕ} (G : RegularGraph n d) :
    (k : ℕ) → RegularGraph n (d ^ (2 ^ k))
  | 0 => G.castDeg (by ring)
  | k + 1 => (G.squareIter k).square.castDeg (by rw [pow_succ 2, pow_mul, sq])

/-- The spectral gap of the k-th iterated square is the 2^k-th power of the original gap. -/
theorem spectralGap_squareIter {n d : ℕ} (G : RegularGraph n d) (k : ℕ) :
    spectralGap (G.squareIter k) = (spectralGap G) ^ (2 ^ k) := by
  induction k with
  | zero =>
    simp only [RegularGraph.squareIter, spectralGap_castDeg, pow_zero, pow_one]
  | succ k ih =>
    simp only [RegularGraph.squareIter, spectralGap_castDeg, spectralGap_square,
      ih, pow_succ 2, pow_mul, sq]


/-! **Spectral Gap Reduction** -/

/-- For `0 ≤ c < 1` and `0 < t`, there exists `k` such that `c ^ (2^k) < t`. -/
theorem exists_pow_two_pow_lt {c t : ℝ} (hc_nn : 0 ≤ c) (hc_lt : c < 1)
    (ht : 0 < t) : ∃ k : ℕ, c ^ (2 ^ k) < t := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one ht hc_lt
  exact ⟨m, lt_of_le_of_lt (pow_le_pow_of_le_one hc_nn hc_lt.le
    (Nat.lt_two_pow_self (n := m)).le) hm⟩


/-! **Expander Family with Small Gap** -/

/-- Given a zig-zag expander family with gap ≤ c < 1, iterated squaring
    produces an expander family with arbitrarily small spectral gap.
    The degree increases (from `D²` to `(D²)^(2^k)`) but remains constant. -/
theorem expander_family_small_gap {D : ℕ}
    {H₀ : RegularGraph ((D * D) * (D * D)) D}
    {β_base c : ℝ}
    (hβ : spectralGap H₀ ≤ β_base) (hβ_le : β_base ≤ 1)
    (hbase : β_base ^ 2 ≤ c) (hc_le : c ≤ 1)
    (hiter : rvwBound (c ^ 2) β_base ≤ c)
    (hc_pos : 0 < c) (hc_lt : c < 1)
    {β : ℝ} (hβ_pos : 0 < β) :
    ∃ (d : ℕ), ∀ n, n > 0 →
    ∃ (G : RegularGraph n d), spectralGap G ≤ β := by
  -- Find k such that c^(2^k) < β
  obtain ⟨k, hk⟩ := exists_pow_two_pow_lt hc_pos.le hc_lt hβ_pos
  -- The zig-zag family gives D²-regular graphs with gap ≤ c at every size
  -- (sorry'd in ZigZag.lean via Cauchy interlacing)
  have hfamily := explicit_expanders_exist_zigzag hβ hβ_le hbase hc_le hiter
  -- Square each graph k times to get (D²)^(2^k)-regular graphs with gap ≤ c^(2^k) < β
  refine ⟨(D * D) ^ (2 ^ k), fun n hn ↦ ?_⟩
  obtain ⟨G, hG⟩ := hfamily n hn
  refine ⟨G.squareIter k, ?_⟩
  -- spectralGap (G.squareIter k) = (spectralGap G)^(2^k) ≤ c^(2^k) < β
  rw [spectralGap_squareIter]
  exact le_of_lt (lt_of_le_of_lt (pow_le_pow_left₀ (spectralGap_nonneg G) hG (2 ^ k)) hk)


/-! **The Main Theorem** -/

/-- **AKS Sorting Networks Exist (Ajtai–Komlós–Szemerédi 1983).**

    Given a base expander `H₀` satisfying the zig-zag fixed-point conditions
    with spectral gap bound `c < 1`, there exist O(n log n) sorting networks
    for all sizes.

    The construction:
    1. Build zig-zag expander family with constant spectral gap ≤ c
    2. Repeatedly square to reduce gap below 1/2
    3. Apply `zigzag_implies_aks_network` to get sorting networks

    The spectral gap condition `c < 1` is the only requirement — the iterated
    squaring handles the gap between c and the 1/2 threshold needed by
    `aks_tree_sorting`. -/
theorem aks_sorting_networks_exist {D : ℕ}
    {H₀ : RegularGraph ((D * D) * (D * D)) D}
    {β c : ℝ}
    (hβ : spectralGap H₀ ≤ β) (hβ_le : β ≤ 1)
    (hbase : β ^ 2 ≤ c) (hc_le : c ≤ 1)
    (hiter : rvwBound (c ^ 2) β ≤ c)
    (hc_pos : 0 < c) (hc_lt : c < 1) :
    ∃ (C : ℝ), C > 0 ∧ ∀ (n : ℕ), n ≥ 2 →
    ∃ (net : ComparatorNetwork n),
      IsSortingNetwork net ∧
      (net.size : ℝ) ≤ C * n * Real.log n := by
  -- Use β_target = 1/4 < 1/2 as the target spectral gap
  obtain ⟨d, hd⟩ := expander_family_small_gap hβ hβ_le hbase hc_le hiter hc_pos hc_lt
    (show (0 : ℝ) < 1/4 from by positivity)
  exact zigzag_implies_aks_network (by positivity : (0:ℝ) < 1/4)
    (by norm_num : (1:ℝ)/4 < 1/2) ⟨d, hd⟩
