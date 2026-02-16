/-
  # ε-Nearsort Definition

  Defines ε-nearsortedness and the `Nearsort` predicate for comparator networks.

  Key definitions:
  • `EpsilonInitialNearsorted`, `EpsilonFinalNearsorted`, `EpsilonNearsorted`:
    permutation-based nearsortedness (AKS Section 4, equation (i))
  • `Nearsort`: a comparator network is an ε-nearsort if for every permutation
    input, the output is ε-nearsorted

  `rank` is defined in `Fin.lean`.
-/

import AKS.ComparatorNetwork
import AKS.Fin

open Finset BigOperators


/-! **ε-Nearsortedness (Permutation-Based, AKS Section 4)** -/

/-- Initial-segment nearsortedness (AKS Section 4, equation (i)):
    for each initial segment S = {a | rank a < k}, at most ε·k elements
    of S are missing from the image of the blown-up segment S^ε under w.

    Concretely: |S \ w(S^ε)| ≤ ε·k, where S^ε = {a | rank a < k + ⌊εn⌋}.

    This is the permutation-based definition, working on the full sequence
    rather than half. Uses `⌊εn⌋₊` (natural floor) for the blow-up radius,
    matching the paper. -/
def EpsilonInitialNearsorted {α : Type*} [Fintype α] [LinearOrder α]
    (w : α → α) (ε : ℝ) : Prop :=
  let n := Fintype.card α
  ∀ k, k ≤ n →
    let S  := Finset.univ.filter (fun a : α ↦ rank a < k)
    let Sε := Finset.univ.filter (fun a : α ↦ rank a < k + ⌊ε * ↑n⌋₊)
    ((S \ Sε.image w).card : ℝ) ≤ ε * ↑k

/-- End-segment nearsortedness: dual of `EpsilonInitialNearsorted` via order reversal.
    Captures the AKS condition (i) for end segments S = {k,...,m}. -/
def EpsilonFinalNearsorted {α : Type*} [Fintype α] [LinearOrder α]
    (w : α → α) (ε : ℝ) : Prop :=
  EpsilonInitialNearsorted (α := αᵒᵈ) w ε

/-- A function is ε-nearsorted if both initial and end segment bounds hold.
    (AKS Section 4, equation (i)): for all initial segments S = {1,...,k}
    and end segments S = {k,...,m}, |S \ πS^ε| ≤ ε|S|. -/
def EpsilonNearsorted {α : Type*} [Fintype α] [LinearOrder α]
    (w : α → α) (ε : ℝ) : Prop :=
  EpsilonInitialNearsorted w ε ∧ EpsilonFinalNearsorted w ε


/-! **Network Predicate** -/

/-- A comparator network is an ε-nearsort if for every permutation input,
    the output is ε-nearsorted.

    (AKS Section 4) This tracks labeled elements via permutations rather than
    0-1 values, which is essential for the segment-wise bounds — in the 0-1 case,
    same-valued elements are indistinguishable, making segment-wise counting
    impossible. -/
def Nearsort {n : ℕ} (net : ComparatorNetwork n) (ε : ℝ) : Prop :=
  ∀ (v : Equiv.Perm (Fin n)),
    EpsilonNearsorted (net.exec v) ε
