# TreeSorting.lean Audit — Statement Correctness and Proof Path

**Date:** 2026-02-15
**Sorry count:** 3 (1 in Halver.lean, 2 in TreeSorting.lean)

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
The definition of `IsEpsilonHalver` was strengthened (Phase 3e) to the AKS Section 3 segment-wise
bound. The segment-wise bound requires **vertex expansion** (spectral gap → expansion via
Alon-Chung or similar), not just the mixing lemma.

**Statement:** `∃ net : ComparatorNetwork (2*m), IsEpsilonHalver net β ∧ net.size ≤ m * d`

**Confidence:** 98%. The paper's Section 3 proof works. The construction (bipartite comparators
from expander) is unchanged; only the proof technique changes.

**Path to re-proving:** Formalize spectral gap → vertex expansion (Alon-Chung lemma).

### 2. `nearsort_has_bounded_tree_damage` — sorry (TreeSorting.lean)

**Statement:** `(∀ m, IsEpsilonHalver (halvers m) ε) → HasBoundedTreeDamage (recursiveNearsort n halvers (log₂ n)) ε t`

**Confidence:** 95%. With the strengthened halver (segment-wise bounds), the recursive nearsort
produces locally near-sorted output at each tree level. The tree-damage bound follows from the
nearsort property applied recursively.

### 3. `bounded_tree_damage_pair_gives_zigzag` — sorry (TreeSorting.lean)

**Statement:** `HasBoundedTreeDamage zig ε t → HasBoundedTreeDamage zag ε t → HasBoundedZigzagDamage zig zag ε t`

**Confidence:** 90%. Paper's Lemma 3 — the `r→r+1` shift comes from the partition offset
between zig and zag cherry decompositions (even/odd cherry levels).

### 4. `aks_tree_sorting` — sorry (TreeSorting.lean)

**Statement:** Takes halver family `(m : ℕ) → ComparatorNetwork (2 * m)` with size bound
`∀ m, (halvers m).size ≤ m * d`. Returns `∃ net` with size ≤ `200·(d+1)·n·log₂ n` and
`∀ v, Monotone (net.exec v)`.

**Confidence:** 95%. Composes lemmas 1-4 with proved `zigzag_decreases_wrongness_v2` and
`displacement_from_wrongness`. The assembly is standard but non-trivial (induction over cycles).

## V2 sorry status

| Lemma | Status | Notes |
|---|---|---|
| `positionTreeDist_succ_le` | **PROVED** | Tree dist increases ≤ 2 when refining t → t+1. |
| `zigzag_decreases_wrongness_v2` | **PROVED** | From `HasBoundedZigzagDamage` + anti-monotonicity. |
| `nearsort_has_bounded_tree_damage` | sorry | Recursive nearsort w/ halver family → BoundedTreeDamage (Lemma 2). |
| `bounded_tree_damage_pair_gives_zigzag` | sorry | BoundedTreeDamage pair → Zigzag (Lemma 3). |
| `aks_tree_sorting` | sorry | Main assembly: halver family → O(n log n) sorting network. |

## V2 dependency chain

```
aks_tree_sorting (halver family formulation) ← sorry
├── nearsort_has_bounded_tree_damage ← sorry (Lemma 2)
├── bounded_tree_damage_pair_gives_zigzag ← sorry (Lemma 3)
│   └── HasBoundedZigzagDamage ← definition
├── register_reassignment_increases_wrongness_v2 ← PROVED
│   └── positionTreeDist_succ_le ← PROVED
├── zigzag_decreases_wrongness_v2 ← PROVED
├── zig_step_bounded_increase_v2 ← PROVED
├── cherry_wrongness_after_nearsort_v2 ← PROVED
├── displacement_from_wrongness ← PROVED
└── tree_wrongness_implies_sorted ← PROVED
```

**Sound if all sorries filled?** YES — all statements have been audited for correctness
and match the AKS paper.

## What's proved (V1 + V2)

| Lemma | Status |
|---|---|
| `zigzag_decreases_wrongness_v2` | PROVED |
| `cherry_wrongness_after_nearsort_v2` | PROVED |
| `zig_step_bounded_increase_v2` | PROVED |
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

### Phase 4 (TODO): Fill sorries

1. **`expander_gives_halver`** (Halver.lean): Formalize spectral gap → vertex expansion
   (Alon-Chung). Independent of TreeSorting work.
2. **`nearsort_has_bounded_tree_damage`**: Show recursive nearsort with segment-wise halvers
   bounds tree-distance displacement. Induction on tree depth.
3. **`bounded_tree_damage_pair_gives_zigzag`**: Show two BoundedTreeDamage steps (zig/zag on
   complementary cherry partitions) give BoundedZigzagDamage. Key: partition offset yields `r→r+1`.
4. **`aks_tree_sorting`**: Assembly — compose above with proved wrongness decrease + displacement
   bound. Induction over zigzag cycles for geometric decay.
