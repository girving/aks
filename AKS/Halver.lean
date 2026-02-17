/-
  # ε-Halver Theory

  Defines ε-halvers and the expander → halver bridge.

  Key results:
  • `countOnes`, `sortedVersion`: Boolean sequence sorting infrastructure
  • `rank`, `EpsilonInitialHalved`, `EpsilonHalved`: permutation-based halver definitions
  • `IsEpsilonHalver`: permutation-based ε-halver definition (AKS Section 3)
  • `expander_gives_halver`: expanders yield ε-halvers (proved, in `ExpanderToHalver.lean`)
  • `IsEpsilonSorted`, `Monotone.bool_pattern`: sortedness infrastructure

  ## Proof strategy for `expander_gives_halver`

  Given a d-regular graph G on m vertices with spectral gap ≤ β, the bipartite
  comparator network (m·d comparators, depth d) is a β-halver. The proof:

  1. **Construction**: `bipartiteComparators G` — compare position v with m + G.neighbor(v,p)
  2. **Edge monotonicity** (proved): `exec_bipartite_edge_mono` — output[v] ≤ output[m+u]
     for each edge (v, m+u)
  3. **Counting**: for segment k ≤ m, let T = {bottom positions with output rank < k}.
     Edge monotonicity forces N(T) ⊆ {top positions with rank < k}, so |N(T)| ≤ k - |T|.
  4. **Tanner's bound** (needed, not yet formalized): |N(T)| ≥ |T|·m/(|T| + β²(m-|T|)).
     This is strictly stronger than the expander mixing lemma for small sets.
  5. **Contradiction**: if |T| > βk, Tanner gives |N(T)| > k - |T|, using only β < 2.

  The expander mixing lemma alone is insufficient — it is tight at k = m and too
  weak for intermediate k. Tanner's bound uses Cauchy-Schwarz on the codegree
  distribution and is derived from the spectral gap independently.

  The actual AKS correctness proof (geometric decrease of unsortedness)
  uses the tree-based approach in `TreeSorting.lean`, not single-halver
  composition.
-/

import AKS.ComparatorNetwork
import AKS.RegularGraph
import AKS.Mixing

open Finset BigOperators


/-! **Sorted Version and Counting** -/

/-- Count the number of `true` values in a Boolean sequence. -/
def countOnes {n : ℕ} (v : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => v i = true)).card

/-- Count ones is bounded by `n`. -/
lemma countOnes_le {n : ℕ} (v : Fin n → Bool) : countOnes v ≤ n := by
  unfold countOnes
  trans (Finset.univ : Finset (Fin n)).card
  · exact Finset.card_filter_le _ _
  · exact le_of_eq (Finset.card_fin n)

/-- The globally sorted version of a Boolean sequence: all 0s then all 1s.
    The threshold is `n - countOnes v`, so positions `[0, threshold)` are false
    and positions `[threshold, n)` are true. -/
def sortedVersion {n : ℕ} (v : Fin n → Bool) : Fin n → Bool :=
  fun i => decide (n - countOnes v ≤ i.val)

/-- The sorted version is monotone. -/
lemma sortedVersion_monotone {n : ℕ} (v : Fin n → Bool) : Monotone (sortedVersion v) := by
  intro i j hij
  unfold sortedVersion
  by_cases h : n - countOnes v ≤ i.val
  · have hj : n - countOnes v ≤ j.val := le_trans h hij
    rw [decide_eq_true_eq.mpr h, decide_eq_true_eq.mpr hj]
  · push_neg at h
    rw [show decide (n - countOnes v ≤ i.val) = false from by simp; omega]
    exact Bool.false_le _


/-! **ε-Halvers (Permutation-Based Definition)** -/

/-- The rank of an element: the number of strictly smaller elements.
    For `Fin n`, this equals the element's value. -/
def rank {α : Type*} [Fintype α] [LinearOrder α] (a : α) : ℕ :=
  (Finset.univ.filter (· < a)).card

/-- Initial-segment halver property (AKS Section 3, permutation-based):
    for each initial segment `{0,...,k-1}` with `k ≤ n/2`, the number of
    positions from the bottom half (`rank pos ≥ n/2`) whose output element
    has rank < k is at most `ε · k`. -/
def EpsilonInitialHalved {α : Type*} [Fintype α] [LinearOrder α]
    (w : α → α) (ε : ℝ) : Prop :=
  let n := Fintype.card α
  ∀ k : ℕ, k ≤ n / 2 →
    ((Finset.univ.filter (fun pos : α ↦
        n / 2 ≤ rank pos ∧ rank (w pos) < k)).card : ℝ) ≤ ε * k

/-- End-segment halver property: dual of `EpsilonInitialHalved` via order reversal. -/
def EpsilonFinalHalved {α : Type*} [Fintype α] [LinearOrder α]
    (w : α → α) (ε : ℝ) : Prop :=
  EpsilonInitialHalved (α := αᵒᵈ) w ε

/-- A function is ε-halved if it satisfies both initial and final segment bounds. -/
def EpsilonHalved {α : Type*} [Fintype α] [LinearOrder α]
    (w : α → α) (ε : ℝ) : Prop :=
  EpsilonInitialHalved w ε ∧ EpsilonFinalHalved w ε

/-- A comparator network is an ε-halver if for every permutation input,
    the output is ε-halved.

    (AKS Section 3) This tracks labeled elements via permutations rather than
    0-1 values, which is essential for the segment-wise bounds — in the 0-1 case,
    same-valued elements are indistinguishable, making segment-wise counting
    impossible. -/
def IsEpsilonHalver {n : ℕ} (net : ComparatorNetwork n) (ε : ℝ) : Prop :=
  ∀ (v : Equiv.Perm (Fin n)),
    EpsilonHalved (net.exec v) ε


/-! **ε-Nearsortedness (Permutation-Based, AKS Section 4)** -/

/-- Initial-segment nearsortedness (AKS Section 4, equation (i)):
    for each initial segment S = {a | rank a < k}, at most ε·k elements
    of S are missing from the image of the blown-up segment S^ε under w.

    Concretely: |S \ w(S^ε)| ≤ ε·k, where S^ε = {a | rank a < k + ⌊εn⌋}.

    This is the permutation-based analogue of `EpsilonInitialHalved`, working
    on the full sequence rather than half. Uses `⌊εn⌋₊` (natural floor) for
    the blow-up radius, matching the paper. -/
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

/-- A permutation is ε-nearsorted if both initial and end segment bounds hold.
    (AKS Section 4, equation (i)): for all initial segments S = {1,...,k}
    and end segments S = {k,...,m}, |S \ πS^ε| ≤ ε|S|. -/
def EpsilonNearsorted {α : Type*} [Fintype α] [LinearOrder α]
    (w : α → α) (ε : ℝ) : Prop :=
  EpsilonInitialNearsorted w ε ∧ EpsilonFinalNearsorted w ε


/-- Merge two sorted halves using iterated ε-halvers.
    After k rounds of ε-halving, the "unsortedness" decreases
    geometrically: at most (2ε)^k · n elements are out of place. -/
def epsHalverMerge (n : ℕ) (ε : ℝ) (k : ℕ)
    (halver : ComparatorNetwork n) : ComparatorNetwork n :=
  { comparators := (List.replicate k halver.comparators).flatten }


/-! **Top/Bottom Half Partitioning** -/

/-- Top half: positions with index < n/2 -/
def topHalf (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i ↦ (i : ℕ) < n / 2)

/-- Bottom half: positions with index ≥ n/2 -/
def bottomHalf (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i ↦ n / 2 ≤ (i : ℕ))

/-- Top and bottom halves cover all positions -/
lemma topHalf_union_bottomHalf (n : ℕ) :
    topHalf n ∪ bottomHalf n = Finset.univ := by
  ext i
  simp [topHalf, bottomHalf]
  omega

/-- Top and bottom halves are disjoint -/
lemma topHalf_disjoint_bottomHalf (n : ℕ) :
    (topHalf n ∩ bottomHalf n) = ∅ := by
  ext i
  simp [topHalf, bottomHalf]

/-- Cardinality of top half -/
lemma card_topHalf (n : ℕ) : (topHalf n).card = n / 2 := by
  by_cases hn : n = 0
  · subst hn; simp [topHalf]
  · have hn2 : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) one_lt_two
    have : topHalf n = Finset.Iio ⟨n / 2, hn2⟩ := by
      ext ⟨i, hi⟩
      simp only [topHalf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio,
        Fin.lt_iff_val_lt_val]
    rw [this, Fin.card_Iio]

/-- Cardinality of bottom half -/
lemma card_bottomHalf (n : ℕ) : (bottomHalf n).card = n - n / 2 := by
  have h_union := topHalf_union_bottomHalf n
  have h_disj : Disjoint (topHalf n) (bottomHalf n) :=
    Finset.disjoint_iff_inter_eq_empty.mpr (topHalf_disjoint_bottomHalf n)
  have h_card := Finset.card_union_of_disjoint h_disj
  rw [h_union, Finset.card_univ, Fintype.card_fin, card_topHalf] at h_card
  omega

/-! **Halver Composition** -/

/-- An ε-sorted vector: at most εn elements are not in their
    correct sorted position. -/
def IsEpsilonSorted {n : ℕ} (v : Fin n → Bool) (ε : ℝ) : Prop :=
  ∃ (w : Fin n → Bool), Monotone w ∧
    ((Finset.univ.filter (fun i ↦ v i ≠ w i)).card : ℝ) ≤ ε * n

/-! **Basic Properties of IsEpsilonSorted** -/

/-- Witness extraction helper -/
lemma IsEpsilonSorted.exists_witness {n : ℕ} {v : Fin n → Bool} {ε : ℝ}
    (h : IsEpsilonSorted v ε) :
    ∃ (w : Fin n → Bool), Monotone w ∧
      ((Finset.univ.filter (fun i ↦ v i ≠ w i)).card : ℝ) ≤ ε * n :=
  h

/-- Monotone Boolean sequences have the pattern 0* 1* (zeros then ones) -/
lemma Monotone.bool_pattern {n : ℕ} (w : Fin n → Bool) (hw : Monotone w) :
    ∃ k : ℕ, (∀ i : Fin n, (i : ℕ) < k → w i = false) ∧
             (∀ i : Fin n, k ≤ (i : ℕ) → w i = true) := by
  -- k = number of false values = size of the downward-closed false set
  use (Finset.univ.filter (fun i : Fin n ↦ w i = false)).card
  set k := (Finset.univ.filter (fun i : Fin n ↦ w i = false)).card
  constructor
  · -- For i.val < k: w i = false
    intro ⟨i, hi⟩ h_lt
    by_contra h_not
    have h_true : w ⟨i, hi⟩ = true := by
      match h : w ⟨i, hi⟩ with
      | true => rfl
      | false => exact absurd h h_not
    -- Every j ≥ i has w j = true (by monotonicity)
    have h_above : ∀ j : Fin n, i ≤ j.val → w j = true := by
      intro ⟨j, hj⟩ h_ij
      have := hw (show (⟨i, hi⟩ : Fin n) ≤ ⟨j, hj⟩ from h_ij)
      rw [h_true] at this
      match h : w ⟨j, hj⟩ with
      | true => rfl
      | false => rw [h] at this; exact absurd this (by decide)
    -- So false set ⊆ {j | j.val < i}
    have h_sub : Finset.univ.filter (fun j : Fin n ↦ w j = false) ⊆
        Finset.Iio ⟨i, hi⟩ := by
      intro ⟨j, hj⟩ hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      simp only [Finset.mem_Iio, Fin.lt_iff_val_lt_val]
      by_contra h_ge; push_neg at h_ge
      exact absurd (h_above ⟨j, hj⟩ h_ge) (by simp [hm])
    -- Card of false set ≤ card of Iio = i
    have := Finset.card_le_card h_sub
    rw [Fin.card_Iio] at this; omega
  · -- For k ≤ i.val: w i = true
    intro ⟨i, hi⟩ h_ge
    by_contra h_not
    have h_false : w ⟨i, hi⟩ = false := by
      match h : w ⟨i, hi⟩ with
      | false => rfl
      | true => exact absurd h h_not
    -- Every j ≤ i has w j = false (by monotonicity)
    have h_below : ∀ j : Fin n, j.val ≤ i → w j = false := by
      intro ⟨j, hj⟩ h_ji
      have := hw (show (⟨j, hj⟩ : Fin n) ≤ ⟨i, hi⟩ from h_ji)
      rw [h_false] at this
      match h : w ⟨j, hj⟩ with
      | false => rfl
      | true => rw [h] at this; exact absurd this (by decide)
    -- So Iic ⟨i, hi⟩ ⊆ false set
    have h_sub : Finset.Iic ⟨i, hi⟩ ⊆
        Finset.univ.filter (fun j : Fin n ↦ w j = false) := by
      intro ⟨j, hj⟩ hm
      simp only [Finset.mem_Iic, Fin.le_iff_val_le_val] at hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h_below ⟨j, hj⟩ hm
    -- Card of Iic = i + 1 ≤ card of false set = k
    have := Finset.card_le_card h_sub
    rw [Fin.card_Iic] at this; omega

/-- Relaxation: if ε₁ ≤ ε₂, then ε₁-sorted implies ε₂-sorted -/
lemma IsEpsilonSorted.mono {n : ℕ} {v : Fin n → Bool} {ε₁ ε₂ : ℝ}
    (h : IsEpsilonSorted v ε₁) (hle : ε₁ ≤ ε₂) :
    IsEpsilonSorted v ε₂ := by
  obtain ⟨w, hw_mono, hw_card⟩ := h
  refine ⟨w, hw_mono, ?_⟩
  calc ((Finset.univ.filter (fun i ↦ v i ≠ w i)).card : ℝ)
      ≤ ε₁ * n := hw_card
    _ ≤ ε₂ * n := by apply mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)

/-- Every sequence is trivially 1-sorted -/
lemma isEpsilonSorted_one {n : ℕ} (v : Fin n → Bool) :
    IsEpsilonSorted v 1 := by
  -- Use the all-false sequence as witness
  refine ⟨fun _ ↦ false, ?_, ?_⟩
  · -- Constant false function is monotone
    intro a b _
    rfl
  · -- At most n positions can differ
    calc ((Finset.univ.filter (fun i ↦ v i ≠ false)).card : ℝ)
        ≤ Finset.univ.card := by
          exact_mod_cast Finset.card_mono (Finset.filter_subset _ _)
      _ = Fintype.card (Fin n) := by simp
      _ = n := by simp
      _ = 1 * n := by ring
