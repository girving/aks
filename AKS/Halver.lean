/-
  # ε-Halver Theory

  Defines ε-halvers and proves their composition properties.
  This is the engine that drives AKS correctness: each halver round
  geometrically reduces unsortedness, yielding a fully sorted output
  after O(log n) rounds.

  Factored from `Basic.lean` for faster incremental checking during
  proof iteration on `halver_composition`.
-/

import AKS.Basic
import AKS.RegularGraph

open Finset BigOperators


/-! **ε-Halvers** -/

/-- A comparator network is an ε-halver if, for every 0-1 input,
    after applying the network, the excess of 1s in the top half
    (beyond fair share) is at most `ε · (n / 2)`.

    Concretely: `onesInTop ≤ totalOnes / 2 + ε · (n / 2)`.

    Intuitively: it balances 1s between the two halves, up to
    an ε-fraction error. -/
def IsEpsilonHalver {n : ℕ} (net : ComparatorNetwork n) (ε : ℝ) : Prop :=
  ∀ (v : Fin n → Bool),
    let w := net.exec v
    let topHalf := Finset.univ.filter (fun i : Fin n ↦ (i : ℕ) < n / 2)
    let onesInTop := (topHalf.filter (fun i ↦ w i = true)).card
    let totalOnes := (Finset.univ.filter (fun i : Fin n ↦ w i = true)).card
    (onesInTop : ℝ) ≤ totalOnes / 2 + ε * (n / 2)

/-- **Expanders yield ε-halvers.**
    Given a `d`-regular graph `G` on `m` vertices with spectral gap `≤ β`,
    a single round of compare-and-swap along bipartite edges
    (pairing vertex `v` with `m + G.neighbor v i`) produces an
    ε-halver on `2m` wires with `ε = β`.

    The bipartite structure comes from the *construction*, not the
    graph type: every comparator connects a top wire (`< m`) to a
    bottom wire (`≥ m`). This ensures bipartite monotonicity (top
    values can only decrease, bottom values can only increase),
    which — combined with the expander mixing lemma — yields the bound. -/
theorem expander_gives_halver (m d : ℕ) (G : RegularGraph m d)
    (β : ℝ) (hβ : spectralGap G ≤ β) :
    ∃ (net : ComparatorNetwork (2 * m)),
      IsEpsilonHalver net β ∧ net.size ≤ m * d := by
  -- Proof sketch:
  -- 1. Construct the network: for each vertex v : Fin m and port i : Fin d,
  --    add comparator (v, m + G.neighbor v i).
  -- 2. Bipartite monotonicity: in the output, for each edge (v, u) of G,
  --    w v ≤ w (m + u). (Top values only decrease; bottom values only increase.)
  -- 3. Let S = {top 1s}, T = {bottom 0s}. By monotonicity, e(S,T) = 0.
  -- 4. By the expander mixing lemma (Mixing.lean):
  --    |S|·|T|/m ≤ β · √(|S|·|T|), so |S|·|T| ≤ β²·m².
  -- 5. With s = |S|, k = total ones, |T| = m - k + s:
  --    s(m - k + s) ≤ β²m² implies s ≤ k/2 + βm.
  sorry

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
  -- Use the fact that filtering gives exactly the first n/2 elements
  have : topHalf n = Finset.filter (fun i ↦ i.val < n / 2) Finset.univ := rfl
  rw [this]
  -- Count elements with val < n / 2
  sorry

/-- Cardinality of bottom half -/
lemma card_bottomHalf (n : ℕ) : (bottomHalf n).card = n - n / 2 := by
  -- Use complementary counting
  sorry

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
  -- Proof: For monotone Boolean sequences, false < true in the ordering.
  -- So if w i = true and i ≤ j, then w j = true (by monotonicity).
  -- This means all trues cluster at high indices, all falses at low indices.
  -- The transition point is characterized by the cardinality of the false set.
  sorry

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

/-! **Displaced Elements** -/

/-- Count elements differing between two sequences -/
def displaced {n : ℕ} (v w : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i ↦ v i ≠ w i)

/-- Displaced set is symmetric -/
lemma card_displaced_symm {n : ℕ} (v w : Fin n → Bool) :
    (displaced v w).card = (displaced w v).card := by
  congr 1
  ext i
  simp [displaced]
  tauto

/-- Membership in displaced set -/
lemma mem_displaced_iff {n : ℕ} (v w : Fin n → Bool) (i : Fin n) :
    i ∈ displaced v w ↔ v i ≠ w i := by
  simp [displaced]

/-- Displaced set can be partitioned by value in witness -/
lemma displaced_partition {n : ℕ} (v w : Fin n → Bool) :
    displaced v w =
      (displaced v w).filter (fun i ↦ w i = false) ∪
      (displaced v w).filter (fun i ↦ w i = true) := by
  ext i
  simp [displaced]
  cases w i <;> simp

/-- Cardinality bound from IsEpsilonSorted -/
lemma IsEpsilonSorted.card_displaced_bound {n : ℕ} {v : Fin n → Bool} {ε : ℝ}
    (h : IsEpsilonSorted v ε) :
    ∃ (w : Fin n → Bool), Monotone w ∧
      ((displaced v w).card : ℝ) ≤ ε * n := by
  obtain ⟨w, hw_mono, hw_card⟩ := h
  exact ⟨w, hw_mono, by simp [displaced]; exact hw_card⟩

/-! **Wrong-Half Elements** -/

/-- Elements that "should" be in bottom half (according to witness w)
    but are actually in top half.
    These are positions where w says 1 (bottom) but the position is in top half. -/
def wrongHalfTop {n : ℕ} (v w : Fin n → Bool) : Finset (Fin n) :=
  (displaced v w).filter (fun i ↦ (i : ℕ) < n / 2 ∧ w i = true)

/-- Elements that "should" be in top half (according to witness w)
    but are actually in bottom half.
    These are positions where w says 0 (top) but the position is in bottom half. -/
def wrongHalfBottom {n : ℕ} (v w : Fin n → Bool) : Finset (Fin n) :=
  (displaced v w).filter (fun i ↦ n / 2 ≤ (i : ℕ) ∧ w i = false)

/-- Wrong-half elements are a subset of displaced elements -/
lemma wrongHalfTop_subset {n : ℕ} (v w : Fin n → Bool) :
    wrongHalfTop v w ⊆ displaced v w := by
  exact Finset.filter_subset _ _

lemma wrongHalfBottom_subset {n : ℕ} (v w : Fin n → Bool) :
    wrongHalfBottom v w ⊆ displaced v w := by
  exact Finset.filter_subset _ _

/-- Wrong-half elements are disjoint (can't be in both top and bottom) -/
lemma wrongHalf_disjoint {n : ℕ} (v w : Fin n → Bool) :
    Disjoint (wrongHalfTop v w) (wrongHalfBottom v w) := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  ext i
  simp [wrongHalfTop, wrongHalfBottom]
  omega

/-- Total wrong-half elements are bounded by total displaced elements -/
lemma card_wrongHalf_le_displaced {n : ℕ} (v w : Fin n → Bool) :
    (wrongHalfTop v w).card + (wrongHalfBottom v w).card ≤
    (displaced v w).card := by
  have h1 := wrongHalfTop_subset v w
  have h2 := wrongHalfBottom_subset v w
  have hdisj := wrongHalf_disjoint v w
  calc (wrongHalfTop v w).card + (wrongHalfBottom v w).card
      = (wrongHalfTop v w ∪ wrongHalfBottom v w).card := by
          rw [Finset.card_union_of_disjoint hdisj]
    _ ≤ (displaced v w).card := by
          apply Finset.card_le_card
          intro i
          simp [wrongHalfTop, wrongHalfBottom, displaced]
          tauto

/-- **Halver composition lemma**: Applying an ε-halver to a
    δ-sorted sequence yields a (δ·2ε)-sorted sequence.
    This geometric decrease is the engine of AKS correctness. -/
theorem halver_composition {n : ℕ} (net : ComparatorNetwork n)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1/2)
    (hnet : IsEpsilonHalver net ε)
    (v : Fin n → Bool) (hv : IsEpsilonSorted v δ) :
    IsEpsilonSorted (net.exec v) (δ * 2 * ε) := by
  -- Step 1: Extract witness w₁ from v being δ-sorted
  obtain ⟨w₁, hw₁_mono, hw₁_card⟩ := hv.exists_witness

  -- Step 2: Construct output witness w₂ = net.exec w₁
  let w₂ := net.exec w₁

  -- w₂ is monotone (by Phase 2: network preserves monotonicity)
  have hw₂_mono : Monotone w₂ := ComparatorNetwork.exec_preserves_monotone net w₁ hw₁_mono

  -- Step 3: Show net.exec v is (δ·2ε)-sorted using w₂ as witness
  refine ⟨w₂, hw₂_mono, ?_⟩

  -- Need to show: |{i : (net.exec v) i ≠ w₂ i}| ≤ δ·2ε·n
  -- This follows from bounding wrong-half elements

  -- Key insight: wrong-half elements in the output are bounded by
  -- the halver property combined with the input displacement
  sorry

/-- **Convergence**: After O(log n) rounds of ε-halving (with ε < 1/2),
    starting from an arbitrary input (which is trivially 1-sorted),
    the sequence becomes 0-sorted, i.e., fully sorted. -/
theorem halver_convergence {n : ℕ} (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1/2)
    (k : ℕ) (hk : (2 * ε) ^ k * n < 1) :
    ∀ (v : Fin n → Bool),
    ∃ (net : ComparatorNetwork n),
      Monotone (net.exec v) := by
  -- After k rounds: unsortedness ≤ (2ε)^k · n < 1.
  -- Since unsortedness is a natural number, it must be 0.
  -- Therefore the output is exactly sorted.
  sorry
