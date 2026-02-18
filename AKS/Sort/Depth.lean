/-
  # Comparator Network Depth

  Depth (minimum parallel rounds) of a comparator network.
  The AKS (1983) network achieves O(log n) depth in addition to O(n log n) size.

  Main results:
  • `ComparatorNetwork.depth` : Critical-path depth via greedy scheduling.
  • `depth_nil`               : Empty network has depth 0.
  • `depth_le_size`           : Depth is at most the number of comparators.
  • `depth_le_of_decomposition` : Any parallel decomposition upper-bounds depth.
-/

import AKS.Sort.Defs

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

    This is an upper bound on the minimum number of parallel rounds needed to
    execute the network (see `depth_le_of_decomposition`). -/
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
    have hwt' : ∀ k, (depthStep (wt, d) c).1 k ≤ (depthStep (wt, d) c).2 := by
      intro k; have hk := hwt k
      simp only [depthStep, Function.update_apply]
      split_ifs <;> omega
    have hd' : (depthStep (wt, d) c).2 ≤ d + 1 := by
      simp only [depthStep]; omega
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
  layer.Pairwise (fun c₁ c₂ ↦ ¬c₁.overlaps c₂)

/-- A parallel decomposition of a network is a list of layers whose
    concatenation (in order) equals the network's comparator list. -/
def IsParallelDecomposition {n : ℕ} (net : ComparatorNetwork n)
    (layers : List (List (Comparator n))) : Prop :=
  (∀ layer ∈ layers, IsParallelLayer layer) ∧
    layers.flatten = net.comparators


/-! **Depth Upper Bound from Parallel Decomposition** -/

/-- `depthStep` for a non-overlapping comparator preserves the other's wire times. -/
private lemma depthStep_preserves_nonoverlap {n : ℕ}
    {c₁ c₂ : Comparator n} (hno : ¬c₁.overlaps c₂)
    (wt : Fin n → ℕ) (d : ℕ) :
    (depthStep (wt, d) c₁).1 c₂.i = wt c₂.i ∧
    (depthStep (wt, d) c₁).1 c₂.j = wt c₂.j := by
  unfold Comparator.overlaps at hno; push_neg at hno
  obtain ⟨h1, h2, h3, h4⟩ := hno
  simp only [depthStep, Function.update_apply]
  refine ⟨?_, ?_⟩
  · rw [if_neg (Ne.symm h3), if_neg (Ne.symm h1)]
  · rw [if_neg (Ne.symm h4), if_neg (Ne.symm h2)]

/-- Processing one non-overlapping layer: if all wire times relevant to the
    layer's comparators are ≤ `d`, then afterward all wire times are ≤ `d + 1`
    and the running max is ≤ `d + 1`.

    Key invariant: within a non-overlapping layer, each comparator's wires
    haven't been touched by earlier comparators in the same layer (since they
    don't share any wires), so they still see the pre-layer bound `d`. -/
private lemma layer_foldl_bound {n : ℕ} (cs : List (Comparator n))
    (hcs : IsParallelLayer cs)
    (wt : Fin n → ℕ) (d dm : ℕ)
    (hwt_layer : ∀ c ∈ cs, wt c.i ≤ d ∧ wt c.j ≤ d)
    (hwt_all : ∀ k, wt k ≤ d + 1)
    (hdm : dm ≤ d + 1) :
    (∀ k, (cs.foldl depthStep (wt, dm)).1 k ≤ d + 1) ∧
    (cs.foldl depthStep (wt, dm)).2 ≤ d + 1 := by
  induction cs generalizing wt dm with
  | nil =>
    simp only [List.foldl_nil]
    exact ⟨hwt_all, hdm⟩
  | cons c cs ih =>
    simp only [List.foldl_cons]
    have ⟨hci, hcj⟩ := hwt_layer c (List.mem_cons.mpr (.inl rfl))
    have hcs_tail := (List.pairwise_cons.mp hcs).2
    have hc_nonoverlap := (List.pairwise_cons.mp hcs).1
    -- After processing c: all wire times ≤ d + 1
    have hwt_all' : ∀ k, (depthStep (wt, dm) c).1 k ≤ d + 1 := by
      intro k; have hk := hwt_all k
      simp only [depthStep, Function.update_apply]
      split_ifs <;> omega
    have hdm' : (depthStep (wt, dm) c).2 ≤ d + 1 := by
      simp only [depthStep]; omega
    -- For remaining comparators, their wires are unchanged (non-overlapping with c)
    have hwt_layer' : ∀ c' ∈ cs, (depthStep (wt, dm) c).1 c'.i ≤ d ∧
        (depthStep (wt, dm) c).1 c'.j ≤ d := by
      intro c' hc'
      have ⟨hpi, hpj⟩ := depthStep_preserves_nonoverlap (hc_nonoverlap c' hc') wt dm
      have ⟨hi', hj'⟩ := hwt_layer c' (List.mem_cons_of_mem c hc')
      exact ⟨hpi ▸ hi', hpj ▸ hj'⟩
    exact ih hcs_tail _ _ hwt_layer' hwt_all' hdm'

/-- Processing multiple layers starting from wire times ≤ d gives depth ≤ d + layers.length. -/
private lemma layers_foldl_bound {n : ℕ} (layers : List (List (Comparator n)))
    (hlayers : ∀ layer ∈ layers, IsParallelLayer layer)
    (wt : Fin n → ℕ) (d dm : ℕ)
    (hwt : ∀ k, wt k ≤ d) (hdm : dm ≤ d) :
    (layers.flatten.foldl depthStep (wt, dm)).2 ≤ d + layers.length := by
  induction layers generalizing wt d dm with
  | nil =>
    simp only [List.flatten_nil, List.foldl_nil, List.length_nil, Nat.add_zero]
    exact hdm
  | cons layer layers ih =>
    have hpar := hlayers layer (List.mem_cons.mpr (.inl rfl))
    have hlayers' : ∀ l ∈ layers, IsParallelLayer l :=
      fun l hl ↦ hlayers l (List.mem_cons_of_mem layer hl)
    -- Unfold flatten and use foldl_append to split into layer ++ rest
    simp only [List.flatten_cons, List.foldl_append, List.length_cons]
    -- After processing one layer: wire times ≤ d + 1
    have hwt_layer : ∀ c ∈ layer, wt c.i ≤ d ∧ wt c.j ≤ d :=
      fun c _ ↦ ⟨hwt c.i, hwt c.j⟩
    have hwt_d1 : ∀ k, wt k ≤ d + 1 := fun k ↦ Nat.le_succ_of_le (hwt k)
    have hdm1 : dm ≤ d + 1 := Nat.le_succ_of_le hdm
    have bound := layer_foldl_bound layer hpar wt d dm hwt_layer hwt_d1 hdm1
    -- Apply IH with d' = d + 1
    have step := ih hlayers' _ (d + 1) _ bound.1 bound.2
    rw [Prod.mk.eta] at step
    omega

/-- **Any parallel decomposition upper-bounds depth.** If a network can be
    decomposed into `k` layers of pairwise non-overlapping comparators, then
    its greedy depth is at most `k`. -/
theorem depth_le_of_decomposition {n : ℕ} (net : ComparatorNetwork n)
    (layers : List (List (Comparator n)))
    (hd : IsParallelDecomposition net layers) :
    net.depth ≤ layers.length := by
  unfold ComparatorNetwork.depth
  rw [← hd.2]
  have h := layers_foldl_bound layers hd.1 (fun _ ↦ 0) 0 0
    (fun _ ↦ le_refl 0) (le_refl 0)
  omega


/-! **Size–Depth Bound** -/

/-- Updating at index `i` and summing: the new sum plus the old value at `i`
    equals the old sum plus the new value. -/
private lemma sum_update_add {n : ℕ} (f : Fin n → ℕ) (i : Fin n) (v : ℕ) :
    ∑ k : Fin n, Function.update f i v k + f i = ∑ k : Fin n, f k + v := by
  have h1 := Finset.add_sum_erase Finset.univ (Function.update f i v) (Finset.mem_univ i)
  have h2 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)
  rw [Function.update_self] at h1
  have h3 : ∑ x ∈ Finset.univ.erase i, Function.update f i v x =
      ∑ x ∈ Finset.univ.erase i, f x :=
    Finset.sum_congr rfl fun k hk ↦
      Function.update_of_ne (Finset.ne_of_mem_erase hk) v f
  omega

/-- A single `depthStep` increases `∑ wt` by at least 2. -/
private lemma depthStep_sum_ge {n : ℕ} (wt : Fin n → ℕ) (dm : ℕ) (c : Comparator n) :
    ∑ k : Fin n, wt k + 2 ≤ ∑ k : Fin n, (depthStep (wt, dm) c).1 k := by
  simp only [depthStep]
  set t := max (wt c.i) (wt c.j) + 1
  have hne : c.i ≠ c.j := Fin.ne_of_lt c.h
  have h1 := sum_update_add wt c.i t
  have h2 := sum_update_add (Function.update wt c.i t) c.j t
  rw [Function.update_of_ne hne.symm t wt] at h2
  -- h1: ∑ (update wt i t) + wt i = ∑ wt + t
  -- h2: ∑ (double update) + wt j = ∑ (update wt i t) + t
  -- ht: wt i + wt j + 2 ≤ 2 * t
  have ht : wt c.i + wt c.j + 2 ≤ 2 * t := by simp only [t]; omega
  omega

/-- Through a full foldl, `∑ wt` increases by at least `2 * cs.length`. -/
private lemma foldl_sum_increase {n : ℕ} (cs : List (Comparator n))
    (wt : Fin n → ℕ) (dm : ℕ) :
    ∑ k : Fin n, wt k + 2 * cs.length ≤
    ∑ k : Fin n, (cs.foldl depthStep (wt, dm)).1 k := by
  induction cs generalizing wt dm with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h_step := depthStep_sum_ge wt dm c
    have h_rest := ih (depthStep (wt, dm) c).1 (depthStep (wt, dm) c).2
    rw [Prod.mk.eta] at h_rest
    omega

/-- Wire times are bounded by the running max throughout the fold. -/
private lemma wt_le_running_max {n : ℕ} (cs : List (Comparator n))
    (wt : Fin n → ℕ) (dm : ℕ) (hwt : ∀ k, wt k ≤ dm) :
    ∀ k, (cs.foldl depthStep (wt, dm)).1 k ≤ (cs.foldl depthStep (wt, dm)).2 := by
  induction cs generalizing wt dm with
  | nil => exact hwt
  | cons c cs ih =>
    simp only [List.foldl_cons]
    apply ih
    intro k
    have hk := hwt k
    set t := max (wt c.i) (wt c.j) + 1
    by_cases hkj : k = c.j
    · subst hkj; rw [Function.update_self]; exact le_max_right dm t
    · rw [Function.update_of_ne hkj t (Function.update wt c.i t)]
      by_cases hki : k = c.i
      · subst hki; rw [Function.update_self]; exact le_max_right dm t
      · rw [Function.update_of_ne hki t wt]
        exact le_trans hk (le_max_left dm t)

/-- **Size–depth bound**: `2 * size ≤ n * depth` for any comparator network.
    Each comparator uses 2 of the `n` wires, contributing ≥ 2 to the total
    wire-time sum. The sum is bounded by `n * depth` since each wire ends
    at time ≤ depth. -/
theorem size_le_half_n_mul_depth {n : ℕ} (net : ComparatorNetwork n) :
    2 * net.size ≤ n * net.depth := by
  unfold ComparatorNetwork.depth ComparatorNetwork.size
  have h_sum := foldl_sum_increase net.comparators (fun _ ↦ 0) 0
  simp only [Finset.sum_const_zero, zero_add] at h_sum
  have h_wt := wt_le_running_max net.comparators (fun _ ↦ 0) 0 (fun _ ↦ le_refl 0)
  have h_bound : ∑ k : Fin n, (net.comparators.foldl depthStep (fun _ ↦ 0, 0)).1 k ≤
      n * (net.comparators.foldl depthStep (fun _ ↦ 0, 0)).2 := by
    calc ∑ k : Fin n, (net.comparators.foldl depthStep (fun _ ↦ 0, 0)).1 k
        ≤ ∑ _k : Fin n, (net.comparators.foldl depthStep (fun _ ↦ 0, 0)).2 :=
          Finset.sum_le_sum fun k _ ↦ h_wt k
      _ = n * (net.comparators.foldl depthStep (fun _ ↦ 0, 0)).2 := by
          simp [Finset.sum_const, Finset.card_univ]
  omega
