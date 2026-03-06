/-
  # Main Theorem: O(log n)-Depth Sorting Networks

  Assembles the Seiferas (2009) separator-based sorting network construction
  into a single `network n : ComparatorNetwork n` for all `n`.

  For `n ≥ 1024` (i.e., `10 ≤ ⌈log₂ n⌉`), uses `seiferasNetwork` at
  power-of-2 size `2^⌈log₂ n⌉`, then `restrictWires` down to `n`.
  For `n < 1024`, uses `bitonicNetwork` (Batcher's bitonic sort).

  Three results:
  1. `network_sorts`: the network sorts all inputs
  2. `network_depth_le`: `depth ≤ 2 ^ 214 * ⌈log₂ n⌉`  (O(log n))
  3. `network_size_le`: `size ≤ 2 ^ 213 * n * ⌈log₂ n⌉`  (O(n log n))
-/

import AKS.Bags.Depth
import AKS.Sort.ZeroOne

/-! **Definition** -/

/-- O(log n)-depth sorting network for any `n`.
    Uses Seiferas's separator-based construction for `n ≥ 1024`,
    Batcher's bitonic sort for smaller inputs. -/
def network (n : ℕ) : ComparatorNetwork n :=
  if h : 1024 ≤ n then
    (seiferasNetwork seiferasParams (Nat.clog 2 n)).restrictWires n
      (Nat.le_pow_clog (by omega) n)
  else
    bitonicNetwork n

/-! **Correctness** -/

theorem network_sorts (n : ℕ) : (network n).Sorts := by
  unfold network; split
  case isTrue h =>
    have hk : 10 ≤ Nat.clog 2 n :=
      (show (10 : ℕ) = Nat.clog 2 1024 by decide +kernel) ▸ Nat.clog_mono_right 2 h
    exact restrictWires_sorts _ _ _ (fun v ↦ (seiferasNetwork_sorts _ _ hk) _ v)
  case isFalse => exact bitonicNetwork_sorts n

/-! **Depth** -/

theorem network_depth_le (n : ℕ) :
    (network n).depth ≤ 2 ^ 214 * Nat.clog 2 n := by
  unfold network; split
  case isTrue h =>
    have hk : 10 ≤ Nat.clog 2 n :=
      (show (10 : ℕ) = Nat.clog 2 1024 by decide +kernel) ▸ Nat.clog_mono_right 2 h
    exact (restrictWires_depth_le _ _ _).trans
      ((seiferasNetwork_depth_le _ _ hk).trans
        (Nat.mul_le_mul_right _ seiferasParams_depth_le))
  case isFalse h =>
    set k := Nat.clog 2 n
    calc (bitonicNetwork n).depth
        ≤ k ^ 2 := bitonicNetwork_depth_le n
      _ = k * k := by ring
      _ ≤ 2 ^ 214 * k := by
          apply Nat.mul_le_mul_right
          calc k ≤ Nat.clog 2 1023 := Nat.clog_mono_right 2 (by omega)
            _ ≤ 2 ^ 214 := by
                set_option maxRecDepth 100000 in decide +kernel

/-! **Size** -/

theorem network_size_le (n : ℕ) :
    (network n).size ≤ 2 ^ 213 * n * Nat.clog 2 n := by
  have h := (size_le_half_n_mul_depth (network n)).trans
    (Nat.mul_le_mul_left _ (network_depth_le n))
  set k := Nat.clog 2 n
  -- h : 2 * size ≤ n * (2^214 * k)
  -- Goal: size ≤ 2^213 * n * k
  have h2 : n * (2 ^ 214 * k) = 2 * (2 ^ 213 * n * k) := by ring
  linarith

/-! **Axiom audit** -/

/-- info: 'network' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms network
/-- info: 'network_sorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms network_sorts
/-- info: 'network_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms network_depth_le
/-- info: 'network_size_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms network_size_le
