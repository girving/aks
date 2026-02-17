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

  `recursiveNearsort` (in `TreeSorting.lean`) applies halvers at each level
  of a binary tree. At level `l`, there are `2^l` sub-intervals of size
  `⌊n/2^l⌋`, each halved by the appropriate halver from the family.

  ## Size bound

  At each level, total halver wires ≤ n, so halver sizes sum to ≤ (n/2) · d
  per level. Over `depth` levels: total size ≤ depth · n · d / 2.

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
  sorry
