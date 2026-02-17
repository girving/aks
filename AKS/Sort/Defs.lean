/-
  # Comparator Network Definitions

  Core definitions for comparator networks: comparators, networks, execution,
  embedding, injectivity preservation, and asymptotic notation.
-/

import AKS.Fin

import Mathlib.Data.List.Sort
import Mathlib.Data.List.Perm.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Basic

open Finset BigOperators


/-! **Comparator Networks** -/

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
structure ComparatorNetwork (n : ℕ) where
  comparators : List (Comparator n)

/-- The size of a network is the total number of comparators. -/
def ComparatorNetwork.size {n : ℕ} (net : ComparatorNetwork n) : ℕ :=
  net.comparators.length

/-- Execute an entire comparator network on an input vector. -/
def ComparatorNetwork.exec {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) (v : Fin n → α) : Fin n → α :=
  net.comparators.foldl (fun acc c ↦ c.apply acc) v


/-! **Comparator Network Embedding** -/

/-- Shift all comparator indices by `offset` and embed into a larger network.
    Maps each comparator `(i, j)` to `(offset + i, offset + j)`. -/
def ComparatorNetwork.shiftEmbed {m : ℕ} (net : ComparatorNetwork m)
    (n offset : ℕ) (h : offset + m ≤ n) : ComparatorNetwork n :=
  { comparators := net.comparators.map fun c ↦
      { i := ⟨offset + c.i.val, by omega⟩
        j := ⟨offset + c.j.val, by omega⟩
        h := by show offset + c.i.val < offset + c.j.val
                have := c.h; simp only [Fin.lt_def] at this; omega } }

theorem ComparatorNetwork.shiftEmbed_size {m : ℕ} (net : ComparatorNetwork m)
    (n offset : ℕ) (h : offset + m ≤ n) :
    (net.shiftEmbed n offset h).size = net.size := by
  simp [shiftEmbed, size, List.length_map]


/-! **Injectivity Preservation** -/

/-- A single comparator preserves injectivity: either no swap (identity)
    or a transposition, both of which compose injectively. -/
theorem Comparator.apply_injective {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) {v : Fin n → α} (hv : Function.Injective v) :
    Function.Injective (c.apply v) := by
  by_cases h : v c.i ≤ v c.j
  · -- No swap: c.apply v = v
    suffices heq : c.apply v = v by rw [heq]; exact hv
    ext k; unfold Comparator.apply
    by_cases hki : k = c.i
    · subst hki; rw [if_pos rfl, min_eq_left h]
    · rw [if_neg hki]
      by_cases hkj : k = c.j
      · subst hkj; rw [if_pos rfl, max_eq_right h]
      · rw [if_neg hkj]
  · -- Swap: c.apply v = v ∘ Equiv.swap c.i c.j
    push_neg at h
    suffices heq : c.apply v = v ∘ ⇑(Equiv.swap c.i c.j) by
      rw [heq]; exact hv.comp (Equiv.injective _)
    ext k; unfold Comparator.apply; simp only [Function.comp]
    by_cases hki : k = c.i
    · subst hki; rw [if_pos rfl, min_eq_right h.le, Equiv.swap_apply_left]
    · rw [if_neg hki]
      by_cases hkj : k = c.j
      · subst hkj; rw [if_pos rfl, max_eq_left h.le, Equiv.swap_apply_right]
      · rw [if_neg hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]

/-- Executing a comparator network preserves injectivity. -/
theorem ComparatorNetwork.exec_injective {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) {v : Fin n → α} (hv : Function.Injective v) :
    Function.Injective (net.exec v) := by
  unfold ComparatorNetwork.exec
  induction net.comparators generalizing v with
  | nil => exact hv
  | cons c cs ih =>
    simp only [List.foldl_cons]
    exact ih (c.apply_injective hv)

/-- Folding comparators that don't touch position `j` leaves `v j` unchanged. -/
private theorem foldl_comparators_outside {n : ℕ} {α : Type*} [LinearOrder α]
    (cs : List (Comparator n)) (v : Fin n → α) (j : Fin n)
    (hj : ∀ c ∈ cs, j ≠ c.i ∧ j ≠ c.j) :
    cs.foldl (fun acc c ↦ c.apply acc) v j = v j := by
  induction cs generalizing v with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    have ⟨hji, hjj⟩ := hj c (.head cs)
    have hstep : c.apply v j = v j := by
      unfold Comparator.apply; rw [if_neg hji, if_neg hjj]
    rw [ih (c.apply v) (fun c' hc' => hj c' (.tail c hc')), hstep]

/-- A shifted+embedded network does not modify positions outside its range. -/
theorem ComparatorNetwork.shiftEmbed_exec_outside {m : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork m) (n offset : ℕ) (h : offset + m ≤ n)
    (v : Fin n → α) (j : Fin n) (hj : j.val < offset ∨ offset + m ≤ j.val) :
    (net.shiftEmbed n offset h).exec v j = v j := by
  unfold shiftEmbed exec
  apply foldl_comparators_outside
  intro c' hc'
  simp only [List.mem_map] at hc'
  obtain ⟨c, _, rfl⟩ := hc'
  exact ⟨by intro heq; have := congr_arg Fin.val heq; dsimp at this; omega,
         by intro heq; have := congr_arg Fin.val heq; dsimp at this; omega⟩


/-! **Complexity Notation** -/

/-- Asymptotic notation for stating complexity bounds. -/
def IsBigO (f g : ℕ → ℝ) : Prop :=
  ∃ (C : ℝ) (n₀ : ℕ), C > 0 ∧ ∀ n, n ≥ n₀ → |f n| ≤ C * |g n|

notation f " =O(" g ")" => IsBigO f g
