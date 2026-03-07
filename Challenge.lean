/-
  # A challenge file for O(log n)-depth sorting networks

  This is a Mathlib-only specification of the main `Seiferas.lean` theorems,
  suitable for use with [comparator](https://github.com/leanprover/comparator)
  and similar tools.
-/

import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Order.Fin.Basic

/-! **Comparator network definitions: depth, size, and sorting** -/

/-- A comparator on `n` wires swaps positions `i` and `j` if out of order. -/
structure Comparator (n : ℕ) where
  i : Fin n
  j : Fin n
  h : i < j

/-- Apply a single comparator to a vector. -/
def Comparator.apply {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (v : Fin n → α) : Fin n → α :=
  fun k ↦
    if k = c.i then min (v c.i) (v c.j)
    else if k = c.j then max (v c.i) (v c.j)
    else v k

/-- A comparator network is a sequence of comparators applied in order. -/
@[ext] structure ComparatorNetwork (n : ℕ) where
  comparators : List (Comparator n)

/-- The size of a network is the total number of comparators. -/
def ComparatorNetwork.size {n : ℕ} (net : ComparatorNetwork n) : ℕ :=
  net.comparators.length

def depthStep {n : ℕ} (state : (Fin n → ℕ) × ℕ) (c : Comparator n) :
    (Fin n → ℕ) × ℕ :=
  let wt := state.1
  let t := max (wt c.i) (wt c.j) + 1
  (Function.update (Function.update wt c.i t) c.j t, max state.2 t)

/-- The depth of a comparator network, computed via greedy critical-path scheduling.

    Each comparator is assigned time step `max(wireTime c.i, wireTime c.j) + 1`,
    then both wires are updated to that time. The network depth is the maximum
    assigned time step.

    This is an upper bound on the minimum number of parallel rounds needed to
    execute the network (see `depth_le_of_decomposition`). -/
def ComparatorNetwork.depth {n : ℕ} (net : ComparatorNetwork n) : ℕ :=
  (net.comparators.foldl depthStep (fun _ ↦ 0, 0)).2

/-- Execute an entire comparator network on an input vector. -/
def ComparatorNetwork.exec {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) (v : Fin n → α) : Fin n → α :=
  net.comparators.foldl (fun acc c ↦ c.apply acc) v

/-- A network is a *sorting network* if it sorts every input. -/
def ComparatorNetwork.Sorts {n : ℕ} (net : ComparatorNetwork n) : Prop :=
  ∀ (α : Type*) [LinearOrder α] (v : Fin n → α),
    Monotone (net.exec v)

/-! **O(log n)-depth, O(n log n)-size networks exist**

    Formally this is weaker than we'd like, as it doesn't show the networks exist
    as an efficiently computable, uniform family. That will have to come later. -/

/-- Efficient networks exist -/
theorem networks_exist (n : ℕ) : ∃ net : ComparatorNetwork n, net.Sorts ∧
    net.depth ≤ 141 * 10 ^ 62 * Nat.clog 2 n ∧
    net.size ≤ 705 * 10 ^ 61 * n * Nat.clog 2 n := sorry
