module
/-
  # Bitonic Sort for Arbitrary n

  Restricts `bitonicSort k` (which operates on `2^k` wires) to arbitrary `n`
  wires via `restrictWires`, using `k = ⌈log₂ n⌉`.

  Main results:
  - `bitonicNetwork`          : computable sorting network for any n
  - `bitonicNetwork_sorts`    : it sorts
  - `bitonicNetwork_depth_le` : depth ≤ (⌈log₂ n⌉)²
-/

public import AKS.Bitonic.Correctness
public import AKS.Bitonic.Depth
public import AKS.Sort.Shrink

@[expose] public section

/-- Bitonic sorting network for arbitrary `n`, by restricting `bitonicSort ⌈log₂ n⌉`
    from `2^⌈log₂ n⌉` wires down to `n`. -/
def bitonicNetwork (n : ℕ) : ComparatorNetwork n :=
  (bitonicSort (Nat.clog 2 n)).restrictWires n (Nat.le_pow_clog (by omega) n)

/-- `bitonicNetwork` sorts all inputs. -/
theorem bitonicNetwork_sorts (n : ℕ) : (bitonicNetwork n).Sorts := by
  unfold bitonicNetwork
  exact restrictWires_sorts _ _ _ (fun v ↦ bitonicSort_sorts _ Bool v)

/-- `bitonicNetwork n` has depth at most `(⌈log₂ n⌉)²`. -/
theorem bitonicNetwork_depth_le (n : ℕ) :
    (bitonicNetwork n).depth ≤ (Nat.clog 2 n) ^ 2 := by
  unfold bitonicNetwork
  exact (restrictWires_depth_le _ _ _).trans (bitonicSort_depth_le _)

end
