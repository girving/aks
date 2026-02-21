/-
  # Invariant Maintenance for the Concrete Split

  Assembles the concrete split definition (`Split.lean`), cardinality bounds
  (`SplitCard.lean`), and stranger bounds (`SplitStranger.lean`) to instantiate
  `invariant_maintained` with `concreteSplit`.

  Key result:
  - `concreteSplit_maintains_invariant`: the invariant holds at stage `t+1`
    on `rebag (concreteSplit lam perm bags)`

  Remaining gaps (3):
  - `concreteSplit_fromParent_filtered` (SplitStranger.lean) — ε-filtering
  - `concreteSplit_cnative_bound` (SplitStranger.lean) — sibling-native bound
  - `small_cap_even` maintenance (Invariant.lean) — even bag sizes when cap < A
-/

import AKS.Bags.SplitCard
import AKS.Bags.SplitStranger

open Finset

/-- The concrete split maintains the Seiferas invariant.

    Given:
    - `SeifInvariant` at stage `t` on `bags`
    - `SatisfiesConstraints` on the parameters
    - `perm` is injective (needed for cardinality bounds via `rankInBag`)

    Then `SeifInvariant` holds at stage `t+1` on `rebag (concreteSplit lam perm bags)`.

    This is the central maintenance theorem that drives the O(log n)-stage
    convergence argument in `TreeSort.lean`. -/
theorem concreteSplit_maintains_invariant {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hparams : SatisfiesConstraints A ν lam ε)
    (hperm : Function.Injective perm) :
    SeifInvariant n A ν lam ε (t + 1) perm
      (rebag (concreteSplit lam perm bags)) := by
  have hlam : (0 : ℝ) ≤ lam := le_of_lt hparams.2.2.2.1
  have hε : (0 : ℝ) ≤ ε := le_of_lt hparams.2.2.2.2.2.1
  have hν : (0 : ℝ) ≤ ν := le_of_lt hparams.2.1
  exact invariant_maintained (concreteSplit lam perm bags) inv hparams
    -- hsplit_sub: components ⊆ bags
    (concreteSplit_hsplit_sub lam perm bags)
    -- hsplit_leaf: leaf bags don't send to children
    (concreteSplit_hsplit_leaf lam perm bags)
    -- hkick: parent kick ≤ 2λ·cap + 1
    (concreteSplit_hkick inv hlam hperm)
    -- hsend_left: left child ≤ cap/2
    (concreteSplit_hsend_left inv hperm)
    -- hsend_right: right child ≤ cap/2
    (concreteSplit_hsend_right inv hperm)
    -- hkick_pair: paired kick when cap < A
    (concreteSplit_hkick_pair inv hparams.1 hlam (le_of_lt hparams.2.2.2.2.1) hperm)
    -- hkick_stranger: stranger count in kicked items
    (fun l i j hj ↦ kick_stranger_bound _ inv hlam hε hν
      (concreteSplit_hsplit_sub lam perm bags) l i j hj)
    -- hparent_stranger: parent strangers for j ≥ 2 (uses filtering sorry)
    (fun l i j hj ↦ concreteSplit_parent_stranger_bound inv hlam hε l i j hj)
    -- hparent_1stranger: parent 1-strangers (uses filtering + cnative sorry's)
    (fun l i ↦ concreteSplit_parent_1stranger inv hparams l i)
    -- hrebag_uniform: uniform rebag sizes (proved)
    (concreteSplit_hrebag_uniform inv hperm (by linarith [hparams.2.2.2.2.1]))
    -- hrebag_disjoint: disjoint rebag bags (proved)
    (concreteSplit_hrebag_disjoint inv)
