/-
  # Comparator Network Depth

  Depth (minimum parallel rounds) of a comparator network.
  The AKS (1983) network achieves O(log n) depth in addition to O(n log n) size.

  Main results:
  • `ComparatorNetwork.depth` : Critical-path depth via greedy scheduling.
  • `depth_nil`               : Empty network has depth 0.
  • `depth_le_size`           : Depth is at most the number of comparators.
  • `depth_eq_min_layers`     : Depth equals minimum layers in any parallel decomposition (sorry).
-/

import AKS.ComparatorNetwork

open Finset BigOperators


/-! **Comparator Overlap** -/

/-- Two comparators overlap if they share a wire. -/
def Comparator.overlaps {n : ℕ} (c₁ c₂ : Comparator n) : Prop :=
  c₁.i = c₂.i ∨ c₁.i = c₂.j ∨ c₁.j = c₂.i ∨ c₁.j = c₂.j

instance {n : ℕ} (c₁ c₂ : Comparator n) : Decidable (c₁.overlaps c₂) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))


/-! **Network Depth** -/

private def depthStep {n : ℕ} (state : (Fin n → ℕ) × ℕ) (c : Comparator n) :
    (Fin n → ℕ) × ℕ :=
  let wt := state.1
  let t := max (wt c.i) (wt c.j) + 1
  (Function.update (Function.update wt c.i t) c.j t, max state.2 t)

/-- The depth of a comparator network, computed via greedy critical-path scheduling.

    Each comparator is assigned time step `max(wireTime c.i, wireTime c.j) + 1`,
    then both wires are updated to that time. The network depth is the maximum
    assigned time step.

    This equals the minimum number of parallel rounds needed to execute
    the network (see `depth_eq_min_layers`). -/
def ComparatorNetwork.depth {n : ℕ} (net : ComparatorNetwork n) : ℕ :=
  (net.comparators.foldl depthStep (fun _ ↦ 0, 0)).2


/-! **Basic Properties** -/

/-- The empty network has depth 0. -/
theorem depth_nil {n : ℕ} : (⟨[]⟩ : ComparatorNetwork n).depth = 0 := rfl

/-- After processing `cs` starting from `(wt, d)` with `∀ k, wt k ≤ d`,
    the running max is at most `d + cs.length`. -/
private lemma depth_foldl_le_length {n : ℕ} (cs : List (Comparator n))
    (wt : Fin n → ℕ) (d : ℕ) (hwt : ∀ k, wt k ≤ d) :
    (cs.foldl depthStep (wt, d)).2 ≤ d + cs.length := by
  induction cs generalizing wt d with
  | nil => simp [List.foldl]
  | cons c cs ih =>
    simp only [List.foldl_cons, List.length_cons]
    have hi := hwt c.i
    have hj := hwt c.j
    -- After one step: state = (wt', max d t) where t = max (wt c.i) (wt c.j) + 1
    -- Wire times satisfy wt' k ≤ max d t for all k
    have hwt' : ∀ k, (depthStep (wt, d) c).1 k ≤ (depthStep (wt, d) c).2 := by
      intro k; have hk := hwt k
      simp only [depthStep, Function.update_apply]
      split_ifs <;> omega
    -- The running max after one step is ≤ d + 1
    have hd' : (depthStep (wt, d) c).2 ≤ d + 1 := by
      simp only [depthStep]; omega
    -- Apply IH, then chain with hd'
    have step := ih ((depthStep (wt, d) c).1) ((depthStep (wt, d) c).2) hwt'
    rw [Prod.mk.eta] at step
    omega

/-- Network depth is at most the number of comparators. -/
theorem depth_le_size {n : ℕ} (net : ComparatorNetwork n) :
    net.depth ≤ net.size := by
  unfold ComparatorNetwork.depth ComparatorNetwork.size
  have h := depth_foldl_le_length net.comparators (fun _ ↦ 0) 0 (fun _ ↦ le_refl 0)
  simp at h
  exact h


/-! **Parallel Decomposition** -/

/-- A layer is a list of pairwise non-overlapping comparators. -/
def IsParallelLayer {n : ℕ} (layer : List (Comparator n)) : Prop :=
  ∀ (i j : Fin layer.length), i < j →
    ¬(layer.get i).overlaps (layer.get j)

/-- A parallel decomposition of a network is a list of layers whose
    concatenation (in order) equals the network's comparator list. -/
def IsParallelDecomposition {n : ℕ} (net : ComparatorNetwork n)
    (layers : List (List (Comparator n))) : Prop :=
  (∀ layer ∈ layers, IsParallelLayer layer) ∧
    layers.flatten = net.comparators

/-- The greedy depth equals the minimum number of layers in any valid
    parallel decomposition. This connects the computable definition to
    the mathematical meaning. -/
theorem depth_eq_min_layers {n : ℕ} (net : ComparatorNetwork n) :
    net.depth = sInf {k | ∃ layers : List (List (Comparator n)),
      IsParallelDecomposition net layers ∧ layers.length = k} := by
  sorry
