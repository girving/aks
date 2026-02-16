/-
  # Tree Damage Improvement (Lemma 2b)

  Proves that the even-level recursive nearsort satisfies `HasImprovedBound`:
  elements at tree-distance ≥ `r` AFTER are bounded by elements at
  tree-distance ≥ `r+1` BEFORE, plus `ε` times elements at `r-2`.

  This is the KEY cherry-parity lemma from AKS (1983) Section 6/8.
  The halvers at each even level push elements whose critical level is
  even one step closer to their sorted positions. The even/odd partition
  ensures no double-counting across levels.

  ## Parallel work note

  This file is designed to be worked on independently of:
  - `TreeDamageStability.lean` (Lemma 2a — stability property)
  - `Halver.lean` (`expander_gives_halver`)

  All three can be proved in parallel by different Claude Code instances.
-/

import AKS.TreeSorting

open Finset BigOperators

/-- **Lemma 2b (AKS Section 8):** Even-level nearsort has the improvement property.
    The even-parity component of the recursive nearsort satisfies `HasImprovedBound`:
    elements at tree-distance ≥ `r` after the network are bounded by elements at
    tree-distance ≥ `r+1` BEFORE, plus `ε` times elements at `r-2`.

    This is the KEY construction-specific lemma capturing the cherry-parity structure
    of AKS Section 6. The halvers at each even level push elements whose critical
    level is even one step closer to their sorted positions. The even/odd partition
    ensures no double-counting across levels.

    Note: by symmetry, the odd-level component also satisfies `HasImprovedBound`,
    but only one improvement hypothesis is needed for `bounded_tree_damage_pair_gives_zigzag`. -/
lemma parity_nearsort_has_improved_bound {n : ℕ}
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hhalvers : ∀ m, IsEpsilonHalver (halvers m) ε)
    (t depth : ℕ) :
    HasImprovedBound (recursiveNearsortParity n halvers depth 0) ε t := by
  sorry
