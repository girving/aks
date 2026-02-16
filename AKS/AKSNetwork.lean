/-
  # AKS Sorting Network Construction

  The Ajtai–Komlós–Szemerédi (1983) O(n log n) sorting network.

  Main results:
  • `zigzag_implies_aks_network` : Expander family → O(n log n) sorting networks.
  • Helper lemmas for iterated halvers (`epsHalverMerge`).

  This file is parameterized over the expander family (taken as a hypothesis).
  For the concrete instantiation with the zig-zag construction, see `Main.lean`.
-/

import AKS.ComparatorNetwork
import AKS.Depth
import AKS.Halver
import AKS.TreeSorting
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Finset BigOperators Real


/-! **Iterated Halver Properties** -/

/-- Executing `epsHalverMerge` is the same as iterating the halver's `exec`. -/
theorem epsHalverMerge_exec_eq_iterate {n : ℕ} {α : Type*} [LinearOrder α]
    (halver : ComparatorNetwork n) (ε : ℝ) (k : ℕ) (v : Fin n → α) :
    (epsHalverMerge n ε k halver).exec v =
    Nat.iterate (fun w ↦ halver.exec w) k v := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    simp only [epsHalverMerge, ComparatorNetwork.exec, List.replicate_succ,
      List.flatten_cons, List.foldl_append]
    show _ = Nat.iterate _ k (halver.exec v)
    exact ih (halver.exec v)

/-- The size of `epsHalverMerge` is `k * halver.size`. -/
theorem epsHalverMerge_size {n : ℕ} (halver : ComparatorNetwork n) (ε : ℝ) (k : ℕ) :
    (epsHalverMerge n ε k halver).size = k * halver.size := by
  simp only [epsHalverMerge, ComparatorNetwork.size, List.length_flatten,
    List.map_replicate, List.sum_replicate, smul_eq_mul]

/-- If iterating a function `k₁` times produces a monotone result,
    and the function preserves monotonicity, then iterating `k₂ ≥ k₁` times
    also produces a monotone result. -/
theorem mono_of_iterate_mono {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) (v : Fin n → α) (k₁ k₂ : ℕ)
    (hle : k₁ ≤ k₂)
    (hmono : Monotone (Nat.iterate (fun w ↦ net.exec w) k₁ v)) :
    Monotone (Nat.iterate (fun w ↦ net.exec w) k₂ v) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction j with
  | zero => simpa
  | succ j ih =>
    have : k₁ + (j + 1) = (k₁ + j) + 1 := by omega
    rw [this, Function.iterate_succ']
    exact net.exec_preserves_monotone _ (ih (by omega))


/-! **Comparator Network Embedding** -/

/-- Embed a `ComparatorNetwork m` into `ComparatorNetwork n` for `m ≤ n`.
    The extra wires `m..n-1` are never touched by any comparator. -/
def ComparatorNetwork.embed {m : ℕ} (net : ComparatorNetwork m) (n : ℕ) (h : m ≤ n) :
    ComparatorNetwork n :=
  { comparators := net.comparators.map fun c ↦
      { i := ⟨c.i.val, by omega⟩
        j := ⟨c.j.val, by omega⟩
        h := by show c.i.val < c.j.val; exact c.h } }

theorem ComparatorNetwork.embed_size {m : ℕ} (net : ComparatorNetwork m) (n : ℕ) (h : m ≤ n) :
    (net.embed n h).size = net.size := by
  simp [embed, size, List.length_map]

/-! **Size Bound Helper** -/

/-- Key arithmetic for the AKS size bound: `100 * Nat.log 2 n * s ≤ c * n * log n`
    when `s ≤ n/2 * d` and `c = 100 * (d + 1)`.
    Uses `Nat.log 2 n ≤ log n / log 2` and `log 2 > 1/2`. -/
private theorem aks_size_bound (m d : ℕ) (hm : 0 < m) (s : ℕ) (hs : s ≤ m * d) :
    (↑(100 * Nat.log 2 (2 * m) * s) : ℝ) ≤
    100 * (↑d + 1) * ↑(2 * m) * Real.log ↑(2 * m) := by
  push_cast
  have hm_r : (0 : ℝ) < ↑m := Nat.cast_pos.mpr hm
  have hs_r : (↑s : ℝ) ≤ ↑m * ↑d := by exact_mod_cast hs
  have h2m_gt1 : (1 : ℝ) < 2 * ↑m := by
    have : (1 : ℝ) ≤ ↑m := Nat.one_le_cast.mpr hm; linarith
  have hlog_pos : (0 : ℝ) < Real.log (2 * ↑m) := Real.log_pos h2m_gt1
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  -- Step 1: Nat.log 2 (2*m) ≤ logb 2 (2*m) = log(2*m) / log 2
  have hnatlog : (↑(Nat.log 2 (2 * m)) : ℝ) ≤ Real.log (2 * ↑m) / Real.log 2 := by
    have h := natLog_le_logb (2 * m) 2
    simp only [Real.logb] at h
    exact_mod_cast h
  -- Step 2: log 2 > 1/2, via exp(1/2) < 1/(1-1/2) = 2
  have hlog2_half : (1 : ℝ) / 2 < Real.log 2 := by
    rw [show (1:ℝ)/2 = Real.log (Real.exp (1/2)) from (Real.log_exp (1/2)).symm]
    exact Real.log_lt_log (by positivity) (by
      calc Real.exp (1/2) < 1 / (1 - 1/2) :=
              Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
        _ = 2 := by norm_num)
  -- Step 3: Chain the inequalities
  calc 100 * ↑(Nat.log 2 (2 * m)) * ↑s
      ≤ 100 * ↑(Nat.log 2 (2 * m)) * (↑m * ↑d) := by nlinarith
    _ ≤ 100 * (Real.log (2 * ↑m) / Real.log 2) * (↑m * ↑d) := by nlinarith
    _ = 100 * ↑m * ↑d * Real.log (2 * ↑m) / Real.log 2 := by ring
    _ ≤ 100 * (↑d + 1) * (2 * ↑m) * Real.log (2 * ↑m) := by
        rw [div_le_iff₀ hlog2_pos]
        -- Need: 100 * m * d * log(2m) ≤ 100 * (d+1) * 2m * log(2m) * log 2
        -- i.e., d ≤ 2*(d+1)*log 2, i.e., d ≤ (2d+2)*log 2
        -- Since log 2 > 1/2: (2d+2)*log 2 > (2d+2)/2 = d+1 ≥ d
        have hd_r : (0 : ℝ) ≤ ↑d := Nat.cast_nonneg d
        -- Key: d*m < (d+1) * 2m * log 2 (since 2*log 2 > 1)
        have hkey : (↑d : ℝ) * ↑m < (↑d + 1) * (2 * ↑m) * Real.log 2 := by nlinarith
        -- Multiply both sides of hkey by 100*log(2m)
        nlinarith [mul_lt_mul_of_pos_right hkey (show (0:ℝ) < 100 * Real.log (2 * ↑m) from by positivity)]


/-! **The Parameterized AKS Theorem** -/

/-- **Connection to AKS (Ajtai–Komlós–Szemerédi 1983).**

    Given an explicit expander family with constant degree `d` and spectral gap
    bounded by `β < 1/2`, there exist O(n log n) sorting networks for all sizes.

    The construction:
    1. `expander_gives_halver`: expander at each size → β-halver family
    2. `aks_tree_sorting`: recursive nearsort with halver family sorts in O(n log n)

    The spectral gap requirement `β < 1/2` comes from `aks_tree_sorting`. -/
theorem zigzag_implies_aks_network {β : ℝ} (hβ_pos : 0 < β) (hβ_half : β < 1/2) :
    (∃ (d : ℕ), ∀ n, n > 0 → ∃ (G : RegularGraph n d), spectralGap G ≤ β) →
    ∃ (c : ℝ), c > 0 ∧ ∀ (n : ℕ), n ≥ 2 →
    ∃ (net : ComparatorNetwork n),
      IsSortingNetwork net ∧
      (net.size : ℝ) ≤ c * n * Real.log n := by
  intro ⟨d, hfamily⟩
  -- c = 400*(d+1): factor of 200 from aks_tree_sorting, factor of 2 for 1/log 2 < 2
  refine ⟨400 * (↑d + 1), by positivity, ?_⟩
  intro n hn
  -- Build halver family: for each m, get a β-halver on 2*m wires from the expander at size m.
  have halver_exists : ∀ m, ∃ (net : ComparatorNetwork (2 * m)),
      IsEpsilonHalver net β ∧ net.size ≤ m * d := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · -- m = 0: empty network on 0 wires, Fin 0 is empty so everything is vacuous
      exact ⟨{ comparators := [] },
        fun v => ⟨fun k hk => by simp at hk; subst hk; simp,
                  fun k hk => by simp at hk; subst hk; simp⟩,
        by simp [ComparatorNetwork.size]⟩
    · obtain ⟨G, hG⟩ := hfamily m hm
      exact expander_gives_halver m d G β hG
  set halvers := fun m ↦ (halver_exists m).choose
  have hhalvers_eps : ∀ m, IsEpsilonHalver (halvers m) β :=
    fun m ↦ ((halver_exists m).choose_spec).1
  have hhalvers_size : ∀ m, (halvers m).size ≤ m * d :=
    fun m ↦ ((halver_exists m).choose_spec).2
  -- Apply aks_tree_sorting with the halver family
  obtain ⟨net, hsize, hmono⟩ := aks_tree_sorting β d hβ_pos hβ_half halvers hhalvers_eps hhalvers_size
  refine ⟨net, ?_, ?_⟩
  · -- Correctness via 0-1 principle
    exact zero_one_principle net hmono
  · -- Size bound: 200*(d+1)*n*log₂(n) ≤ 400*(d+1)*n*log(n)
    -- Key: Nat.log 2 n ≤ logb 2 n = log n / log 2, and 1/log 2 < 2 (since log 2 > 1/2).
    have hlog2_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
    have hlog2_half : (1:ℝ) / 2 < Real.log 2 := by
      rw [show (1:ℝ)/2 = Real.log (Real.exp (1/2)) from (Real.log_exp (1/2)).symm]
      exact Real.log_lt_log (by positivity) (by
        calc Real.exp (1/2) < 1 / (1 - 1/2) :=
                Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
          _ = 2 := by norm_num)
    have hn_real : (1:ℝ) ≤ ↑n := by exact_mod_cast (show 1 ≤ n by omega)
    have hlog_nn : (0:ℝ) ≤ Real.log ↑n := Real.log_nonneg hn_real
    calc (net.size : ℝ) ≤ 200 * (↑d + 1) * ↑n * ↑(Nat.log 2 n) := hsize
      _ ≤ 200 * (↑d + 1) * ↑n * (Real.log ↑n / Real.log 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : (↑(Nat.log 2 n) : ℝ) ≤ Real.logb 2 ↑n := by exact_mod_cast natLog_le_logb n 2
          rwa [Real.logb, Real.log_div_log] at this
      _ ≤ 200 * (↑d + 1) * ↑n * (2 * Real.log ↑n) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_iff₀ hlog2_pos]
          -- Need: log n ≤ 2 * log n * log 2, i.e. 1 ≤ 2 * log 2 (when log n ≥ 0)
          nlinarith
      _ = 400 * (↑d + 1) * ↑n * Real.log ↑n := by ring
