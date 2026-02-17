/-
  # Halver → Nearsort

  Proves that a family of ε-halvers yields a δ-nearsort network.
  (AKS Section 4, page 5)

  ## The ε → δ relationship

  Given ε-halvers, recursive halving for `depth` levels produces a δ-nearsort
  where **δ = ε · depth**. Errors accumulate additively: at each level, the
  halver introduces at most ε fraction of errors per initial segment; over
  `depth` levels, the union bound gives δ = ε · depth.

  The paper's formulation (Section 4, page 5):
  > "To construct an ε-nearsort network, apply an ε₁-halver (network), with
  > ε₁ < ε/(log 1/ε), to the whole set of registers, then apply ε₁-halvers
  > to the top and bottom half of registers, then to each quarter, eighth,
  > sixteenth, until the pieces have size w < εm."

  Equivalently: given ε₁-halvers, choose depth = ⌈log₂(1/ε₁)⌉ to get a
  (ε₁ · depth)-nearsort with δ ≈ ε₁ · log₂(1/ε₁).

  ## Construction

  `halverNetwork` applies halvers at each level of a binary tree.
  At level `l`, there are `2^l` sub-intervals of size `⌊n/2^l⌋`,
  each halved by the appropriate halver from the family.

  ## Size bound

  At each level, total halver wires ≤ n, so halver sizes sum to ≤ n · d
  per level (conservative bound). Over `depth` levels: total size ≤ depth · d · n.

  ## Proof outline (AKS Section 4: "It is easy to see")

  Goal: for any permutation input and initial segment S = {rank < k},
  |S \ π(S^δ)| ≤ δ · k, where δ = ε · depth and S^δ = {rank < k + ⌊δn⌋}.

  1. **Sub-interval structure.** After `depth` levels, elements are organized
     into sub-intervals of size n/2^depth. The blow-up condition ensures
     n/2^depth ≤ ⌊δn⌋, so the blow-up radius covers one sub-interval.

  2. **Correct classification.** An element is "correctly classified at level l"
     if the halver at level l places it in the half of its sub-interval that
     contains its target position. By induction: elements correctly classified
     at all levels end up in the correct sub-interval of size n/2^depth,
     hence within the blow-up radius δn of their target.

  3. **Per-level halver bound.** At level l, the halver guarantee (which holds
     for every permutation input, regardless of earlier rearrangements) gives:
     for each initial segment of size j ≤ (sub-interval size)/2, at most ε · j
     elements from the wrong half end up in the initial segment.

  4. **Boundary analysis.** For global initial segment S = {rank < k} at level l:
     - Sub-intervals entirely within S: misclassification moves elements
       between halves of the sub-interval, but they stay in S. No new errors.
     - Sub-intervals entirely outside S: no effect on S.
     - The one sub-interval straddling position k: the halver can introduce
       at most ε · k_local errors, where k_local ≤ k is the size of S
       within this sub-interval.

  5. **Error accumulation.** Summing the per-level boundary errors over `depth`
     levels: total ≤ ε · depth · k = δ · k. (This is conservative — it uses
     a union bound over the boundary errors at each level.)

  6. **End-segment symmetry.** The same argument applies to end segments
     S = {rank ≥ k} by the `EpsilonFinalHalved` property, giving the
     `FinalNearsorted` half of the `Nearsorted` predicate.

  Key results:
  • `halverNearsortQuality`: the δ = ε · depth relationship
  • `halver_family_gives_nearsort`: ε-halver family → δ-nearsort
-/

import AKS.Halver
import AKS.Nearsort

open Finset BigOperators


/-! **Quality relationship** -/

/-- The nearsort quality achieved by recursive halving with ε-halvers.

    After `depth` levels of recursive halving, errors accumulate additively:
    each level contributes at most ε errors per initial-segment element,
    giving total quality δ = ε · depth.

    AKS Section 4 chooses depth = ⌈log₂(1/ε)⌉, giving δ ≈ ε · log₂(1/ε).
    For the blow-up radius ⌊δn⌋ to cover the finest sub-interval size
    n/2^depth, we need n/2^depth ≤ δn, i.e., 1 ≤ ε · depth · 2^depth.
    This holds for depth ≥ ⌈log₂(1/ε)⌉ when ε < 1/2.

    Example: ε = 1/100 halvers with depth = 7 give δ = 7/100 nearsort. -/
def halverNearsortQuality (ε : ℝ) (depth : ℕ) : ℝ := ε * depth


/-! **Network construction** -/

/-- Apply a halver to sub-interval `[offset, offset + 2*m)` within an `n`-wire
    network. The halver operates on `2*m` wires and is shifted to the correct
    position via `shiftEmbed`. -/
def applyHalverToSubinterval (n : ℕ)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (m offset : ℕ) (h : offset + 2 * m ≤ n) : ComparatorNetwork n :=
  (halvers m).shiftEmbed n offset h

/-- Apply halvers to all sub-intervals at a given tree level.
    At level `l`: there are `2^l` sub-intervals, each of size `⌊n / 2^l⌋`.
    Each sub-interval is halved by applying the appropriate halver
    via `shiftEmbed`. -/
def halverAtLevel (n : ℕ)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (level : ℕ) : ComparatorNetwork n :=
  let chunkSize := n / 2 ^ level
  let halfChunk := chunkSize / 2
  let numChunks := 2 ^ level
  { comparators := (List.range numChunks).flatMap fun k ↦
      let offset := k * chunkSize
      if h : offset + 2 * halfChunk ≤ n then
        (applyHalverToSubinterval n halvers halfChunk offset h).comparators
      else [] }

/-- The recursive halver network: applies halvers at each tree level
    from coarsest (level 0) to finest (level depth-1).

    This is the AKS Section 4 construction: at level `l`, there are `2^l`
    sub-intervals of size `⌊n / 2^l⌋`, each halved by the family halver
    for that sub-interval size. -/
def halverNetwork (n : ℕ)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (depth : ℕ) : ComparatorNetwork n :=
  { comparators := (List.range depth).flatMap fun l ↦
      (halverAtLevel n halvers l).comparators }


/-! **Size bounds** -/

/-- `2^l * (n / 2^l / 2) ≤ n`: the total number of halver wires at one level
    does not exceed `n`. -/
private lemma chunks_times_halfChunk_le (n level : ℕ) :
    2 ^ level * (n / 2 ^ level / 2) ≤ n :=
  calc 2 ^ level * (n / 2 ^ level / 2)
      ≤ 2 ^ level * (n / 2 ^ level) :=
        Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
    _ = n / 2 ^ level * 2 ^ level := by ring
    _ ≤ n := Nat.div_mul_le_self n (2 ^ level)

/-- Size of the per-chunk comparator list: either `(halvers halfChunk).size`
    or 0 (if the chunk doesn't fit). -/
private lemma chunk_comparators_le {n : ℕ}
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m)) (d : ℕ)
    (hhalver_size : ∀ m, (halvers m).size ≤ m * d)
    (halfChunk : ℕ) (chunkSize : ℕ) (k : ℕ) :
    (if h : k * chunkSize + 2 * halfChunk ≤ n then
      (applyHalverToSubinterval n halvers halfChunk (k * chunkSize) h).comparators
    else []).length ≤ halfChunk * d := by
  split
  · -- Active chunk: size = shiftEmbed size = original halver size ≤ halfChunk * d
    change ComparatorNetwork.size _ ≤ halfChunk * d
    simp only [applyHalverToSubinterval, ComparatorNetwork.shiftEmbed_size]
    exact hhalver_size halfChunk
  · simp

/-- The sub-interval halver sizes sum to at most `n * d` at each level.

    At level `l`: `2^l` chunks of size `chunkSize = ⌊n / 2^l⌋`, each with
    a halver on `2 * halfChunk` wires where `halfChunk = chunkSize / 2`.
    Each halver has size ≤ `halfChunk * d`. Total per level:
    `2^l * halfChunk * d ≤ (n/2) * d ≤ n * d`. -/
theorem halverAtLevel_size (n : ℕ)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m)) (d : ℕ)
    (hhalver_size : ∀ m, (halvers m).size ≤ m * d)
    (level : ℕ) :
    (halverAtLevel n halvers level).size ≤ n * d := by
  unfold halverAtLevel ComparatorNetwork.size
  simp only
  set chunkSize := n / 2 ^ level
  set halfChunk := chunkSize / 2
  set numChunks := 2 ^ level
  rw [List.length_flatMap]
  -- Each chunk contributes ≤ halfChunk * d comparators
  calc ((List.range numChunks).map fun k ↦
          (if h : k * chunkSize + 2 * halfChunk ≤ n then
            (applyHalverToSubinterval n halvers halfChunk (k * chunkSize) h).comparators
          else []).length).sum
      ≤ ((List.range numChunks).map fun _ ↦ halfChunk * d).sum :=
        List.sum_le_sum (fun k _ ↦ chunk_comparators_le halvers d hhalver_size halfChunk chunkSize k)
    _ = numChunks * (halfChunk * d) := by
        simp [List.map_const', List.sum_replicate, List.length_range]
    _ = numChunks * halfChunk * d := (Nat.mul_assoc ..).symm
    _ ≤ n * d := Nat.mul_le_mul_right d (chunks_times_halfChunk_le n level)

/-- The total halver network size is at most `depth * (n * d)`. -/
theorem halverNetwork_size (n : ℕ)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m)) (d : ℕ)
    (hhalver_size : ∀ m, (halvers m).size ≤ m * d)
    (depth : ℕ) :
    (halverNetwork n halvers depth).size ≤ depth * (n * d) := by
  unfold halverNetwork ComparatorNetwork.size
  simp only
  rw [List.length_flatMap]
  calc ((List.range depth).map fun l ↦
          (halverAtLevel n halvers l).comparators.length).sum
      ≤ ((List.range depth).map fun _ ↦ n * d).sum :=
        List.sum_le_sum (fun l _ ↦ halverAtLevel_size n halvers d hhalver_size l)
    _ = depth * (n * d) := by
        simp [List.map_const', List.sum_replicate, List.length_range]


/-! **Correctness infrastructure** -/

/-- The state after applying the first `levels` levels of the halver network. -/
def halverNetworkPartial (n : ℕ)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (levels : ℕ) : ComparatorNetwork n :=
  { comparators := (List.range levels).flatMap fun l ↦
      (halverAtLevel n halvers l).comparators }

/-! **Correctness proof outline**

The proof tracks individual element trajectories through the recursive halving:

1. **Correctly classified.** Value `b` is "correctly classified at level `l`" if
   the halver at level `l` places it in the sub-interval containing `b.val` at the
   level-`(l+1)` partition. Since level `l` splits sub-intervals of size `n/2^l`
   into halves of size `n/2^(l+1)`, correct classification means `b` goes to the
   half containing position `b.val`.

2. **All-correct → near target.** If `b` is correctly classified at every level
   `0, ..., depth-1`, then after `depth` levels, `b` is at a position within
   `n/2^depth` of `b.val`.

3. **Blow-up covers displacement.** The hypothesis `1 ≤ ε · depth · 2^depth`
   ensures `n/2^depth ≤ ⌊(ε · depth) · n⌋`, so correctly-classified values
   are within the blow-up radius.

4. **Per-level misclassification bound.** At level `l`, the halver at the
   boundary sub-interval (straddling the threshold for initial segment `k`)
   misclassifies at most `ε · k` values in `[0, k)`. This uses `IsEpsilonHalver`
   applied to the local permutation within the sub-interval.

5. **Union bound.** Each value is assigned to at most one level (the first level
   where it's misclassified). Total misclassified ≤ `Σ_l ε·k = depth · ε · k`.

6. **Assembly.** `|S \ Sδ.image w| ≤ (# misclassified values < k) ≤ δ · k`.

Key difficulty: Step 4 requires connecting the halver's LOCAL guarantee (on
the sub-interval's values) to the GLOBAL misclassification count. The `exec`
on the sub-interval acts on the values via their local ranking, and
`exec_comp_monotone` bridges local and global behavior. -/

/-- The initial-segment nearsort bound: after `depth` levels of recursive halving,
    at most `ε · depth · k` elements of each initial segment `[0, k)` are displaced
    beyond the blow-up radius. -/
theorem halverNetwork_initialNearsorted {n : ℕ} (ε : ℝ) (depth d : ℕ)
    (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hdepth : (1 : ℝ) ≤ ε * ↑depth * 2 ^ depth)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (hhalvers : ∀ m, IsEpsilonHalver (halvers m) ε)
    (hhalver_size : ∀ m, (halvers m).size ≤ m * d)
    (v : Equiv.Perm (Fin n)) :
    InitialNearsorted ((halverNetwork n halvers depth).exec v) (ε * ↑depth) := by
  sorry

/-- The dual: final-segment nearsortedness follows from `EpsilonFinalHalved`
    (which is part of `IsEpsilonHalver`). The same per-level argument applies
    with reversed order. -/
theorem halverNetwork_finalNearsorted {n : ℕ} (ε : ℝ) (depth d : ℕ)
    (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hdepth : (1 : ℝ) ≤ ε * ↑depth * 2 ^ depth)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (hhalvers : ∀ m, IsEpsilonHalver (halvers m) ε)
    (hhalver_size : ∀ m, (halvers m).size ≤ m * d)
    (v : Equiv.Perm (Fin n)) :
    FinalNearsorted ((halverNetwork n halvers depth).exec v) (ε * ↑depth) := by
  sorry


/-! **Main theorem** -/

/-- Given ε-halvers, recursive halving for `depth` levels produces a
    (ε · depth)-nearsort of size O(depth · d · n).

    The `hdepth` condition ensures the blow-up radius covers the finest
    sub-interval: n/2^depth ≤ ⌊(ε · depth) · n⌋. This simplifies to
    1 ≤ ε · depth · 2^depth (when n > 0), which holds for
    depth = ⌈log₂(1/ε)⌉ since then 2^depth ≥ 1/ε and ε · depth ≥ 1.

    (AKS Section 4: "apply ε₁-halvers recursively...it is easy to see
    that the obtained network of bounded depth is an ε-nearsort") -/
theorem halver_family_gives_nearsort {n : ℕ} (ε : ℝ) (depth d : ℕ)
    (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hdepth : (1 : ℝ) ≤ ε * ↑depth * 2 ^ depth)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (hhalvers : ∀ m, IsEpsilonHalver (halvers m) ε)
    (hhalver_size : ∀ m, (halvers m).size ≤ m * d) :
    ∃ (net : ComparatorNetwork n),
      Nearsort net (halverNearsortQuality ε depth) ∧
        (net.size : ℝ) ≤ ↑depth * ↑d * ↑n := by
  refine ⟨halverNetwork n halvers depth, ?_, ?_⟩
  · -- Nearsort: for every permutation, output is nearsorted
    intro v
    exact ⟨halverNetwork_initialNearsorted ε depth d hε hε1 hdepth halvers hhalvers hhalver_size v,
           halverNetwork_finalNearsorted ε depth d hε hε1 hdepth halvers hhalvers hhalver_size v⟩
  · -- Size bound
    calc ((halverNetwork n halvers depth).size : ℝ)
        ≤ ↑(depth * (n * d)) := by
          exact_mod_cast halverNetwork_size n halvers d hhalver_size depth
      _ = ↑depth * ↑d * ↑n := by push_cast; ring
