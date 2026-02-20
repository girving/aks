/-
  # Seiferas Main Assembly

  Assembles the concrete zig-zag expander family with the Seiferas (2009)
  separator-based sorting network to produce O(n log n) sorting networks.

  This is the Seiferas-path analog of `AKS/Main.lean`, which uses the
  original AKS tree-based proof. The Seiferas path replaces ε-nearsorts
  with (γ, ε)-separators and uses bag-tree convergence instead of
  tree-distance wrongness.

  The key chain:
  1. `explicit_expanders_exist_zigzag` (ZigZag/Expanders.lean): zig-zag expander family, gap ≤ c < 1
  2. Iterated squaring (`squareIter`): reduces spectral gap from c to c^(2^k) < target
  3. `expanderHalverFamily` (Halver/ExpanderToHalver.lean): expander family → halver family
  4. `halverToSeparatorFamily` (Separator/FromHalver.lean): halver family → separator family
  5. `separatorSortingNetwork` (Bags/TreeSort.lean): separator family → O(log n) depth sorting
  6. This file: plug them together in `seiferas_sorting_networks_exist`
-/

import AKS.Bags.TreeSort
import AKS.Sort.ZeroOne
import AKS.Separator.FromHalver
import AKS.Halver.ExpanderToHalver
import AKS.ZigZag.Expanders
import AKS.Graph.Square
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Real


/-! **Iterated Graph Squaring** -/

-- Reuse squaring infrastructure from Main.lean (same definitions)

/-- Helper: cast a `RegularGraph` when the degree is propositionally equal. -/
private def RegularGraph.castDeg' {n d₁ d₂ : ℕ} (h : d₁ = d₂) (G : RegularGraph n d₁) :
    RegularGraph n d₂ :=
  h ▸ G

private theorem spectralGap_castDeg' {n d₁ d₂ : ℕ} (h : d₁ = d₂) (G : RegularGraph n d₁) :
    spectralGap (G.castDeg' h) = spectralGap G := by
  subst h; rfl

/-- Iterated squaring of a regular graph.
    `G.squareIter' k` squares the graph `k` times, yielding a
    `d^(2^k)`-regular graph on the same `n` vertices. -/
noncomputable def RegularGraph.squareIter' {n d : ℕ} (G : RegularGraph n d) :
    (k : ℕ) → RegularGraph n (d ^ (2 ^ k))
  | 0 => G.castDeg' (by ring)
  | k + 1 => (G.squareIter' k).square.castDeg' (by rw [pow_succ 2, pow_mul, sq])

/-- The spectral gap of the k-th iterated square is the 2^k-th power of the original gap. -/
theorem spectralGap_squareIter' {n d : ℕ} (G : RegularGraph n d) (k : ℕ) :
    spectralGap (G.squareIter' k) = (spectralGap G) ^ (2 ^ k) := by
  induction k with
  | zero =>
    simp only [RegularGraph.squareIter', spectralGap_castDeg', pow_zero, pow_one]
  | succ k ih =>
    simp only [RegularGraph.squareIter', spectralGap_castDeg', spectralGap_square,
      ih, pow_succ 2, pow_mul, sq]


/-! **Spectral Gap Reduction** -/

/-- For `0 ≤ c < 1` and `0 < t`, there exists `k` such that `c ^ (2^k) < t`. -/
private theorem exists_pow_two_pow_lt' {c t : ℝ} (hc_nn : 0 ≤ c) (hc_lt : c < 1)
    (ht : 0 < t) : ∃ k : ℕ, c ^ (2 ^ k) < t := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one ht hc_lt
  exact ⟨m, lt_of_le_of_lt (pow_le_pow_of_le_one hc_nn hc_lt.le
    (Nat.lt_two_pow_self (n := m)).le) hm⟩


/-! **Expander Family with Small Gap** -/

/-- Given a zig-zag expander family with gap ≤ c < 1, iterated squaring
    produces an expander family with arbitrarily small spectral gap. -/
private theorem expander_family_small_gap' {D : ℕ}
    {H₀ : RegularGraph ((D * D) * (D * D)) D}
    {β_base c : ℝ}
    (hβ : spectralGap H₀ ≤ β_base) (hβ_le : β_base ≤ 1)
    (hbase : β_base ^ 2 ≤ c) (hc_le : c ≤ 1)
    (hiter : rvwBound (c ^ 2) β_base ≤ c)
    (hc_pos : 0 < c) (hc_lt : c < 1)
    {β : ℝ} (hβ_pos : 0 < β) :
    ∃ (d : ℕ), ∀ n, n > 0 →
    ∃ (G : RegularGraph n d), spectralGap G ≤ β := by
  obtain ⟨k, hk⟩ := exists_pow_two_pow_lt' hc_pos.le hc_lt hβ_pos
  have hfamily := explicit_expanders_exist_zigzag hβ hβ_le hbase hc_le hiter
  refine ⟨(D * D) ^ (2 ^ k), fun n hn ↦ ?_⟩
  obtain ⟨G, hG⟩ := hfamily n hn
  refine ⟨G.squareIter' k, ?_⟩
  rw [spectralGap_squareIter']
  exact le_of_lt (lt_of_le_of_lt (pow_le_pow_left₀ (spectralGap_nonneg G) hG (2 ^ k)) hk)


/-! **Expander → Halver → Separator Pipeline** -/

/-- Given an expander family with gap ≤ β, build a halver family with
    error parameter β and constant depth d. -/
noncomputable def expanderToHalverFamily {d : ℕ} (β : ℝ)
    (hfamily : ∀ n, n > 0 → ∃ (G : RegularGraph n d), spectralGap G ≤ β) :
    HalverFamily β d :=
  expanderHalverFamily β (fun m hm ↦ (hfamily m hm).choose)
    (fun m hm ↦ (hfamily m hm).choose_spec)

/-- Build a separator family from a halver family via iterated halving.
    Uses `t` levels of recursion, producing a (1/2^t, t*ε)-separator family
    with depth `t * d`.

    The separator correctness proof (`isSep`) requires `2^t ∣ n` and `0 ≤ ε`.
    For the sorting network application, inputs are padded to powers of 2,
    so the divisibility condition is always satisfied. -/
noncomputable def halverToSeparatorFamily' {ε : ℝ} {d : ℕ}
    (family : HalverFamily ε d) (hε : 0 ≤ ε) (t : ℕ) :
    SeparatorFamily (1 / 2 ^ t) (↑t * ε) (t * d) where
  net n := halverToSeparator n family t
  valid n := 2 ^ t ∣ n
  isSep n hdiv := halverToSeparator_isSeparator n family t hε hdiv
  depth_le n := halverToSeparator_depth_le n family t


/-! **The Seiferas Theorem** -/

/-- **Parameterized Seiferas Sorting Theorem.**

    Given an expander family with constant degree `d` and spectral gap
    bounded by `β`, there exist O(n log n) sorting networks for all sizes.

    The construction:
    1. `expanderHalverFamily`: expander family → β-halver family
    2. `halverToSeparatorFamily'`: halver family → separator family
    3. `separatorSortingNetwork`: separator family → sorting network

    The spectral gap bound determines the separator error, which
    determines convergence rate. Any `β < 1` suffices (separator
    error rate is multiplicative, so iterated halving drives it down).

    Remaining sorry: `separatorSortingNetwork_sorts` (bag-tree convergence
    → correctness) in `Bags/TreeSort.lean`. The size bound is fully proved. -/
theorem seiferas_implies_sorting_network {β : ℝ} (hβ_pos : 0 < β) (hβ_lt : β < 1) :
    (∃ (d : ℕ), ∀ n, n > 0 → ∃ (G : RegularGraph n d), spectralGap G ≤ β) →
    ∃ (C : ℝ), C > 0 ∧ ∀ (n : ℕ), n ≥ 2 →
    ∃ (net : ComparatorNetwork n),
      IsSortingNetwork net ∧
      (net.size : ℝ) ≤ C * n * Real.log n := by
  intro ⟨d, hfamily⟩
  -- Build the pipeline: expander family → halver family → separator family
  let halvers := expanderToHalverFamily β hfamily
  -- One level of halving: (1/2, β)-separator with depth 1 * d = d
  let seps := halverToSeparatorFamily' halvers hβ_pos.le 1
  -- Use 10 stages per log₂ n (constant chosen to exceed convergence threshold)
  -- C = 10 * d gives: size ≤ (10*d) * n * log n
  refine ⟨10 * (↑d + 1), by positivity, fun n hn ↦ ?_⟩
  let net := separatorSortingNetwork n seps (10 * Nat.log 2 n)
  refine ⟨net, ?_, ?_⟩
  · -- Correctness: 0-1 principle + separator sorting (sorry'd in Bags/TreeSort.lean)
    exact zero_one_principle net
      (separatorSortingNetwork_sorts seps (10 * Nat.log 2 n) trivial)
  · -- Size bound: depth bound + size_le_half_n_mul_depth + log conversion
    have hd_sep : (1 : ℕ) * d = d := one_mul d
    -- depth ≤ 10 * d * Nat.log 2 n (from separatorSortingNetwork_depth_bound, via hd_sep)
    have hdepth : net.depth ≤ 10 * d * Nat.log 2 n := by
      show (separatorSortingNetwork n seps (10 * Nat.log 2 n)).depth ≤ _
      calc (separatorSortingNetwork n seps (10 * Nat.log 2 n)).depth
          ≤ (10 * Nat.log 2 n) * (1 * d) :=
            separatorSortingNetwork_depth_le n seps (10 * Nat.log 2 n)
        _ = 10 * d * Nat.log 2 n := by ring
    -- 2 * size ≤ n * depth (from size_le_half_n_mul_depth)
    have hsize2 : 2 * net.size ≤ n * net.depth := size_le_half_n_mul_depth net
    -- Combine: 2 * size ≤ n * (10 * d * log₂ n)
    have hsize_nat : 2 * net.size ≤ n * (10 * d * Nat.log 2 n) :=
      le_trans hsize2 (Nat.mul_le_mul_left _ hdepth)
    -- Cast to ℝ: size ≤ n * (10 * d * log₂ n) / 2 ≤ 5 * d * n * log₂ n
    have hsize_real : (net.size : ℝ) ≤ 5 * ↑d * ↑n * ↑(Nat.log 2 n) := by
      have h : (2 * net.size : ℝ) ≤ ↑n * (10 * ↑d * ↑(Nat.log 2 n)) := by
        exact_mod_cast hsize_nat
      linarith
    -- Convert Nat.log to Real.log: Nat.log 2 n ≤ logb 2 n = log n / log 2 < 2 * log n
    have hlog2_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
    have hlog2_half : (1:ℝ) / 2 < Real.log 2 := by
      rw [show (1:ℝ)/2 = Real.log (Real.exp (1/2)) from (Real.log_exp (1/2)).symm]
      exact Real.log_lt_log (by positivity) (by
        calc Real.exp (1/2) < 1 / (1 - 1/2) :=
                Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
          _ = 2 := by norm_num)
    have hn_real : (1:ℝ) ≤ ↑n := by exact_mod_cast (show 1 ≤ n by omega)
    have hlog_nn : (0:ℝ) ≤ Real.log ↑n := Real.log_nonneg hn_real
    calc (net.size : ℝ)
        ≤ 5 * ↑d * ↑n * ↑(Nat.log 2 n) := hsize_real
      _ ≤ 5 * ↑d * ↑n * (Real.log ↑n / Real.log 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : (↑(Nat.log 2 n) : ℝ) ≤ Real.logb 2 ↑n := by exact_mod_cast natLog_le_logb n 2
          rwa [Real.logb, Real.log_div_log] at this
      _ ≤ 5 * ↑d * ↑n * (2 * Real.log ↑n) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_iff₀ hlog2_pos]
          nlinarith
      _ = 10 * ↑d * ↑n * Real.log ↑n := by ring
      _ ≤ 10 * (↑d + 1) * ↑n * Real.log ↑n := by nlinarith

/-- **Seiferas Sorting Networks Exist (Seiferas 2009 via Zig-Zag Expanders).**

    Given a base expander `H₀` satisfying the zig-zag fixed-point conditions
    with spectral gap bound `c < 1`, there exist O(n log n) sorting networks
    for all sizes.

    The construction:
    1. Build zig-zag expander family with constant spectral gap ≤ c
    2. Repeatedly square to reduce gap to any target β < 1
    3. Build halver family from expander family
    4. Build separator family from halver family
    5. Apply Seiferas's bag-tree argument to get sorting networks

    Compare with `aks_sorting_networks_exist` in `Main.lean`, which uses
    the original AKS tree-distance wrongness argument. -/
theorem seiferas_sorting_networks_exist {D : ℕ}
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
  -- Get an expander family with gap < 1/2 (any target < 1 works for Seiferas)
  obtain ⟨d, hd⟩ := expander_family_small_gap' hβ hβ_le hbase hc_le hiter hc_pos hc_lt
    (show (0 : ℝ) < 1/2 from by positivity)
  -- Apply the Seiferas pipeline
  exact seiferas_implies_sorting_network (by positivity : (0:ℝ) < 1/2)
    (by norm_num : (1:ℝ)/2 < 1) ⟨d, hd⟩
