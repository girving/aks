/-
  # Halver → Nearsort Assembly

  Assembles the construction, size bounds, and correctness into the main theorem:
  a family of ε-halvers yields a δ-nearsort network with δ = ε · depth.
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
-/

import AKS.Nearsort.Correctness

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
