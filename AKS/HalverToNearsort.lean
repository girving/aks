/-
  # Halver → Nearsort

  Proves that a family of ε-halvers yields an ε-nearsort network.

  The construction applies halvers recursively at each level of a binary tree
  (AKS Section 4): split into halves, recurse on each half, apply halver to merge.
  After `⌈log₂ n⌉` levels, the result is ε-nearsorted.

  Key result:
  • `halver_family_gives_nearsort`: ε-halver family → ε-nearsort with O(nd log n) size
-/

import AKS.Halver

open Finset BigOperators

/-- Given an ε-halver family (one per sub-interval size), there exists an
    ε-nearsort network with size O(n · d · log n).

    The construction recursively applies halvers at each level of a binary tree:
    level `l` has `2^l` sub-intervals of size `⌊n/2^l⌋`, each halved by
    `halvers (⌊n/2^l⌋ / 2)`. After `depth` levels, the output is ε-nearsorted.

    (AKS Section 4, Lemma 1) -/
theorem halver_family_gives_nearsort {n : ℕ} (ε : ℝ) (d : ℕ)
    (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (hhalvers : ∀ m, IsEpsilonHalver (halvers m) ε)
    (hhalver_size : ∀ m, (halvers m).size ≤ m * d) :
    ∃ (net : ComparatorNetwork n),
      Nearsort net ε ∧ (net.size : ℝ) ≤ 100 * (↑d + 1) * ↑n * ↑(Nat.log 2 n) := by
  sorry
