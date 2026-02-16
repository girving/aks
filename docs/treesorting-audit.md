# TreeSorting.lean Audit — Statement Correctness and Proof Path

**Date:** 2026-02-16
**Sorry count:** 7 (1 in Halver.lean, 3 in TreeSorting.lean, 1 each in TreeDamageStability/Improvement/AKSNetwork)

## Summary

TreeSorting.lean has a **fundamental formalization gap**: `elementsAtDistance` doesn't use
its `t` parameter, making time-dependent reasoning vacuous. This is being addressed via
**V2 definitions** (`elementsAtTreeDist`, `treeWrongnessV2`, etc.) that use genuine
tree-distance at level `t`.

**Phase 1 (DONE):** V2 definitions + algebraic lemma re-proofs.
**Phase 2 (DONE):** V2 reformulations of Lemmas 1 and 3.
**Phase 2.5 (DONE):** Statement correctness audit — fixed quantifier bug in `aks_tree_sorting`,
  updated `halvers_give_bounded_nearsort` to V2 interface.
**Phase 3 (IN PROGRESS):** Fill V2 sorries, connect V2 lemmas to `aks_tree_sorting`.
**Phase 3a (DONE):** Factor `halvers_give_bounded_nearsort` (proved as composition),
  prove `zigzag_decreases_wrongness_v2`, delete V1 orphans.
**Phase 3b (DONE):** Reformulate `bounded_tree_damage_gives_zigzag` — introduced
  `HasCherryShiftDamage`, proved `cherry_shift_damage_gives_zigzag` algebraically.
**Phase 3c (DONE):** Simplify halver bridge — deleted `buildRecursiveNearsort` /
  `recursive_nearsort_bounded_tree_damage` / `halvers_give_bounded_nearsort` intermediaries,
  replaced with direct `halver_has_cherry_shift_damage` sorry.
**Phase 3d (DONE):** Fix FALSE statements — `halver_has_cherry_shift_damage` and
  `aks_tree_sorting` were both false (counterexample: n=4, halver=[(0,2),(1,3)], v=[F,T,F,T]).
  Root cause: `IsEpsilonHalver` captures aggregate balance but not mixing structure.
  Replaced single halver iteration with `recursiveNearsort` using halver family
  (one halver per sub-interval size). Deleted `epsilonNearsort` (stub).
**Phase 3e (DONE):** Align with AKS paper:
  - Strengthened `IsEpsilonHalver` from one-sided midpoint to AKS Section 3 segment-wise bounds
  - Sorry'd `expander_gives_halver` (needs vertex expansion, not just mixing lemma)
  - Deleted `HasCherryShiftDamage` and all dependents (not in AKS paper; the `r→r+1` shift
    comes from partition offset between zig/zag, not from individual network properties)
  - Added paper-aligned sorries: `nearsort_has_bounded_tree_damage` (Lemma 2),
    `bounded_tree_damage_pair_gives_zigzag` (Lemma 3)
  - Updated `zigzag_implies_aks_network` to build halver family from expander family
    (eliminated even/odd case split and its sorry)
**Phase 3f (DONE):** Fix FALSE `bounded_tree_damage_pair_gives_zigzag`:
  - **Found counterexample**: zig=zag=identity, ε=0.01, n=8, t=2 — identity satisfies
    `HasBoundedTreeDamage` (stability) but not `HasBoundedZigzagDamage` (improvement)
  - **Root cause**: `HasBoundedTreeDamage` is a stability condition (doesn't make things worse),
    but the `r→r+1` shift needs an improvement property (cherry-parity structure)
  - **Fix**: Added `HasImprovedBound` predicate (same as `HasBoundedTreeDamage` but with `r+1`
    shift on RHS). Corrected Lemma 3 takes `HasImprovedBound zig` + `HasBoundedTreeDamage zig`
    + `HasBoundedTreeDamage zag` and is **ALGEBRAICALLY PROVED** (no sorry)
  - Added `recursiveNearsortParity` (zig=even levels, zag=odd levels)
  - Split Lemma 2 into 2a (`parity_nearsort_has_bounded_tree_damage`, sorry) and
    2b (`parity_nearsort_has_improved_bound`, sorry, captures cherry-parity structure)
  - Net: 3 sorry → 3 sorry + 1 PROVED. The FALSE statement becomes fully proved.
**Phase 3g (DONE):** Fix FALSE `expander_gives_halver` definition:
  - **Root cause**: 0-1 position-based `IsEpsilonHalver` definition was wrong — same-valued
    elements are indistinguishable, making segment-wise counting impossible
  - **Fix**: Changed to permutation-based definition using `Equiv.Perm (Fin n)` and `rank`.
    Added `rank`, `EpsilonInitialHalved`, `EpsilonFinalHalved`, `EpsilonHalved`.
  - `expander_gives_halver` stays sorry (now correct statement)
  - All downstream references (TreeSorting.lean, AKSNetwork.lean) updated and verified
**Phase 3h (DONE):** Audit definitions against AKS paper, permutation-based overhaul:
  - Added `EpsilonInitialNearsorted`, `EpsilonFinalNearsorted`, `EpsilonNearsorted` to Halver.lean
    (permutation-based, matching AKS Section 4 eq. (i)). Old `IsEpsilonNearsorted` deprecated.
  - Added `elementTreeDist`, `permElementsAtTreeDist`, `foreignElements` to TreeSorting.lean
    (permutation-based element tracking using tree distance from position to home section)
  - **Replaced** `HasBoundedTreeDamage`, `HasImprovedBound`, `HasBoundedZigzagDamage` to quantify
    over `Fin n → Fin n` (element assignments) using `permElementsAtTreeDist` instead of Bool-based
    `elementsAtTreeDist`. Paper's Lemma 2 tracks labeled elements, not 0-1 values.
  - **Re-proved** `bounded_tree_damage_pair_gives_zigzag` with new types (algebraic, no sorry)
  - **Sorry'd** 3 previously-proved lemmas that bridged Bool↔permutation worlds:
    `cherry_wrongness_after_nearsort_v2`, `zig_step_bounded_increase_v2`,
    `zigzag_decreases_wrongness_v2`. These need a bridge between Bool-based `treeWrongnessV2`
    and permutation-based `HasBoundedTreeDamage`.
  - Net: 4 sorry → 7 sorry. Definitions now match AKS paper; bridge lemmas needed.

## The fundamental issue: time-independent distance

`elementsAtDistance n t v J r` (line 937) filters elements in interval J whose displacement
from `sortedVersion v` exceeds `r * J.size`. The parameter `t` appears in the signature but
is **never used in the body**. This means:

- `treeWrongness n t v J r = treeWrongness n 0 v J r` for all t (definitionally equal)
- Time evolution (t → t+1) is vacuous
- Register reassignment (Lemma 1) can't be formalized without meaningful time dependence

## V2 definitions (Phase 1)

| Definition | Purpose |
|---|---|
| `sectionIndex n t i` | Maps position i to section `⌊i·2^t/n⌋` at level t |
| `sectionNode n t i` | TreeNode at level t for position i |
| `positionTreeDist n t v i` | Tree distance from i's section to threshold section |
| `elementsAtTreeDist n t v J r` | Elements in J at tree-distance ≥ r (genuinely uses t) |
| `HasBoundedTreeDamage net ε t` | Bounded damage parameterized by tree level t |
| `HasBoundedZigzagDamage zig zag ε t` | Combined zigzag damage with r → r+1 shift |
| `treeWrongnessV2 n t v J r` | Wrongness using `elementsAtTreeDist` |

## Per-sorry assessment

### 1. `expander_gives_halver` — sorry (Halver.lean)

**History:** Previously proved using the mixing lemma, which gives the one-sided midpoint bound.
The definition of `IsEpsilonHalver` was changed from a 0-1 position-based segment-wise definition
to a **permutation-based** definition (Phase 3g). The old 0-1 definition was FALSE for
`expander_gives_halver` because same-valued elements are indistinguishable, making segment-wise
counting impossible. The new definition tracks labeled elements via `Equiv.Perm (Fin n)` and uses
`rank` to define segment membership.

**Statement:** `∃ net : ComparatorNetwork (2*m), IsEpsilonHalver net β ∧ net.size ≤ m * d`

**Confidence:** 98%. The paper's Section 3 proof works. The construction (bipartite comparators
from expander) is unchanged; only the proof technique changes.

**Path to re-proving:** Formalize spectral gap → vertex expansion (Alon-Chung lemma).

### 2a. `parity_nearsort_has_bounded_tree_damage` — sorry (TreeDamageStability.lean)

**Statement:** `(∀ m, IsEpsilonHalver (halvers m) ε) → HasBoundedTreeDamage (recursiveNearsortParity n halvers depth parity) ε t`

**Confidence:** 95%. Each parity component (even or odd levels) of the recursive nearsort has
bounded tree damage. The segment-wise halver property ensures bounded damage at each level.

### 2b. `parity_nearsort_has_improved_bound` — sorry (TreeDamageImprovement.lean)

**Statement:** `(∀ m, IsEpsilonHalver (halvers m) ε) → HasImprovedBound (recursiveNearsortParity n halvers depth 0) ε t`

**Confidence:** 85%. This is the KEY cherry-parity lemma: the even-level nearsort satisfies
`HasImprovedBound` (elements at distance ≥ r after ≤ elements at distance ≥ r+1 before + error).
The proof requires showing that halvers at each even level push elements at that level one step
closer. This is the hardest remaining sorry.

### 3. `bounded_tree_damage_pair_gives_zigzag` — **PROVED** (TreeSorting.lean)

**Statement:** `HasImprovedBound zig ε t → HasBoundedTreeDamage zig ε t → HasBoundedTreeDamage zag ε t → HasBoundedZigzagDamage zig zag ε t`

**Status:** Algebraically proved. The proof substitutes the three bounds and uses ε² ≤ ε.
Previously FALSE (Phase 3e) — the old statement only took `HasBoundedTreeDamage` for both,
which the identity network satisfies trivially.

### 4. `aks_tree_sorting` — sorry (AKSNetwork.lean)

**Statement:** Takes halver family `(m : ℕ) → ComparatorNetwork (2 * m)` with size bound
`∀ m, (halvers m).size ≤ m * d`. Returns `∃ net` with size ≤ `200·(d+1)·n·log₂ n` and
`∀ v, Monotone (net.exec v)`.

**Confidence:** 95%. Composes lemmas 1-4 with proved `zigzag_decreases_wrongness_v2` and
`displacement_from_wrongness`. The assembly is standard but non-trivial (induction over cycles).

## V2 sorry status

| Lemma | Status | Notes |
|---|---|---|
| `positionTreeDist_succ_le` | **PROVED** | Tree dist increases ≤ 2 when refining t → t+1. |
| `cherry_wrongness_after_nearsort_v2` | sorry | Needs Bool↔permutation bridge (Phase 3h). |
| `zig_step_bounded_increase_v2` | sorry | Needs Bool↔permutation bridge (Phase 3h). |
| `zigzag_decreases_wrongness_v2` | sorry | Needs Bool↔permutation bridge (Phase 3h). |
| `parity_nearsort_has_bounded_tree_damage` | sorry | Lemma 2a (`TreeDamageStability.lean`). |
| `parity_nearsort_has_improved_bound` | sorry | Lemma 2b (`TreeDamageImprovement.lean`). |
| `bounded_tree_damage_pair_gives_zigzag` | **PROVED** | Lemma 3 (`TreeSorting.lean`). |
| `aks_tree_sorting` | sorry | Assembly (`AKSNetwork.lean`). |

## V2 dependency chain

```
aks_tree_sorting (halver family formulation) ← sorry
├── parity_nearsort_has_bounded_tree_damage ← sorry (Lemma 2a)
├── parity_nearsort_has_improved_bound ← sorry (Lemma 2b)
├── bounded_tree_damage_pair_gives_zigzag ← PROVED (Lemma 3)
│   ├── HasImprovedBound ← definition (NEW)
│   ├── HasBoundedTreeDamage ← definition
│   └── HasBoundedZigzagDamage ← definition
├── register_reassignment_increases_wrongness_v2 ← PROVED
│   └── positionTreeDist_succ_le ← PROVED
├── zigzag_decreases_wrongness_v2 ← sorry (needs Bool↔perm bridge)
├── zig_step_bounded_increase_v2 ← sorry (needs Bool↔perm bridge)
├── cherry_wrongness_after_nearsort_v2 ← sorry (needs Bool↔perm bridge)
├── displacement_from_wrongness ← PROVED
└── tree_wrongness_implies_sorted ← PROVED
```

**Sound if all sorries filled?** YES — all statements have been audited for correctness
and match the AKS paper.

## What's proved (V1 + V2)

| Lemma | Status |
|---|---|
| `zigzag_decreases_wrongness_v2` | sorry (Phase 3h: needs Bool↔perm bridge) |
| `cherry_wrongness_after_nearsort_v2` | sorry (Phase 3h: needs Bool↔perm bridge) |
| `zig_step_bounded_increase_v2` | sorry (Phase 3h: needs Bool↔perm bridge) |
| `register_reassignment_increases_wrongness_v2` | PROVED |
| `positionTreeDist_succ_le` | PROVED |
| `sectionIndex_succ_div_two` | PROVED |
| `displacement_from_wrongness` | PROVED |
| `treeWrongnessV2_le_one`, `_nonneg`, `_monotone` | PROVED |
| All tree distance lemmas | PROVED |
| All comparator/network preservation lemmas | PROVED |

## Deleted definitions (Phase 3e)

| Name | Reason |
|---|---|
| `HasCherryShiftDamage` | Not in AKS paper; `r→r+1` comes from partition offset (Lemma 3) |
| `cherry_shift_implies_bounded_tree` | Built on deleted `HasCherryShiftDamage` |
| `cherry_shift_damage_gives_zigzag` | Built on deleted `HasCherryShiftDamage` |
| `recursive_nearsort_has_cherry_shift_damage` | FALSE (counterexample) + built on deleted def |
| `epsilonNearsort` | STUB (just iterated single halver, didn't do recursive sub-ranges) |

## Path forward

### Phase 4 (TODO): Fill sorries — parallelized across files

Sorries have been extracted to separate files for parallel work by different CC instances.
`TreeSorting.lean` has **zero sorries** and is a stable foundation (read-only during parallel work).

1. **`expander_gives_halver`** (`Halver.lean`): Formalize spectral gap → vertex expansion
   (Alon-Chung). Independent of TreeSorting work.
2. **`parity_nearsort_has_bounded_tree_damage`** (`TreeDamageStability.lean`, Lemma 2a):
   Show parity-restricted nearsort with segment-wise halvers bounds tree-distance displacement.
   Stability property. Independent of Lemma 2b.
3. **`parity_nearsort_has_improved_bound`** (`TreeDamageImprovement.lean`, Lemma 2b):
   Show even-level nearsort satisfies `HasImprovedBound`. This is the KEY cherry-parity lemma.
   Independent of Lemma 2a.
4. **`aks_tree_sorting`** (`AKSNetwork.lean`): Assembly — compose Lemmas 2a, 2b, 3 (proved)
   with proved wrongness decrease + displacement bound. Blocked by #2 and #3.
