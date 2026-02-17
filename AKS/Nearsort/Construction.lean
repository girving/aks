/-
  # Halver Network Construction & Size Bounds

  Defines the recursive halving network and proves its size is O(depth · d · n).
  (AKS Section 4, page 5)

  At level `l`, there are `2^l` sub-intervals of size `⌊n/2^l⌋`, each halved
  by the appropriate halver from the family. Over `depth` levels, total size
  is at most `depth · d · n`.

  Key definitions:
  • `applyHalverToSubinterval`: embed one halver at a given offset
  • `halverAtLevel`: all halvers at one tree level
  • `halverNetwork`: the full recursive halving network

  Key results:
  • `halverAtLevel_size`: per-level size ≤ n · d
  • `halverNetwork_size`: total size ≤ depth · (n · d)
-/

import AKS.Halver.Defs
import AKS.Nearsort

open Finset BigOperators


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
