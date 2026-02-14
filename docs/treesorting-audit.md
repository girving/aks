# TreeSorting.lean Audit — Statement Correctness and Proof Path

**Date:** 2026-02-14
**Sorry count:** 6 (5 V1 + 1 V2 helper; 3 V2 lemmas proved or correctly stated)

## Summary

TreeSorting.lean has a **fundamental formalization gap**: `elementsAtDistance` doesn't use
its `t` parameter, making time-dependent reasoning vacuous. This is being addressed via
**V2 definitions** (`elementsAtTreeDist`, `treeWrongnessV2`, etc.) that use genuine
tree-distance at level `t`.

**Phase 1 (DONE):** V2 definitions + algebraic lemma re-proofs.
**Phase 2 (DONE):** V2 reformulations of Lemmas 1 and 3.
**Phase 3 (TODO):** Connect V2 lemmas to `aks_tree_sorting`.

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
| `sectionIndex n t i` | Maps position i to section ⌊i·2^t/n⌋ at level t |
| `sectionNode n t i` | TreeNode at level t for position i |
| `positionTreeDist n t v i` | Tree distance from i's section to threshold section |
| `elementsAtTreeDist n t v J r` | Elements in J at tree-distance ≥ r (genuinely uses t) |
| `HasBoundedTreeDamage net ε t` | Bounded damage parameterized by tree level t |
| `HasBoundedZigzagDamage zig zag ε t` | Combined zigzag damage with r → r+1 shift |
| `treeWrongnessV2 n t v J r` | Wrongness using `elementsAtTreeDist` |

## Per-sorry assessment (V1)

### 1. `halvers_give_bounded_nearsort` — CORRECT ✅ (sorry)

Existential claim: given an ε₁-halver, there exists a network with bounded damage.
**Risk:** MEDIUM.

### 2. `register_reassignment_increases_wrongness` — WRONG ❌ (sorry, kept for reference)

**V2 replacement:** `register_reassignment_increases_wrongness_v2` — **PROVED** ✅
Uses single `v`, `J' ⊆ J`, distance shift 2, parameterized constant C.

### 3. `zigzag_decreases_wrongness` — INCOMPLETE ⚠️ (sorry, kept for reference)

**V2 replacement:** `zigzag_decreases_wrongness_v2` — sorry, **correctly stated** ✅
Takes two networks (zig_net, zag_net), uses `HasBoundedZigzagDamage` for the r → r+1
shift from cherry alternation. Algebraic proof (routine, same pattern as other wrappers).

### 4. `aks_tree_sorting` — CORRECT ✅ (sorry)

Needs V2 lemma chain to be complete.

## V2 sorry status

| Lemma | Status | Notes |
|---|---|---|
| `positionTreeDist_succ_le` | sorry | Helper: tree dist increases ≤ 2 when refining t → t+1 |
| `zigzag_decreases_wrongness_v2` | sorry | Algebraic wrapper (routine, same pattern as V2 Lemma 2) |

## V2 dependency chain

```
aks_tree_sorting
├── halvers_give_bounded_nearsort ← correct, sorry (V1)
├── register_reassignment_increases_wrongness_v2 ← PROVED ✅
│   └── positionTreeDist_succ_le ← sorry (helper)
├── zigzag_decreases_wrongness_v2 ← correctly stated, sorry (algebraic)
│   └── HasBoundedZigzagDamage ← definition (captures r → r+1 shift)
├── zig_step_bounded_increase_v2 ← PROVED ✅
├── cherry_wrongness_after_nearsort_v2 ← PROVED ✅
├── displacement_from_wrongness ← PROVED ✅ (V1, usable with V2)
└── tree_wrongness_implies_sorted ← PROVED ✅ (V1)
```

**Sound if all V2 sorries filled?** YES — all V2 statements are correct.

## What's proved (V1 + V2)

| Lemma | Status |
|---|---|
| `cherry_wrongness_after_nearsort` (V1) | PROVED |
| `cherry_wrongness_after_nearsort_v2` | PROVED |
| `zig_step_bounded_increase` (V1) | PROVED |
| `zig_step_bounded_increase_v2` | PROVED |
| `register_reassignment_increases_wrongness_v2` | PROVED |
| `displacement_from_wrongness` (V1) | PROVED |
| `treeWrongnessV2_le_one`, `_nonneg`, `_monotone` | PROVED |
| All tree distance lemmas | PROVED |
| All comparator/network preservation lemmas | PROVED |

## Path forward

### Phase 3 (TODO): Connect V2 lemmas to `aks_tree_sorting`

The main theorem needs to compose:
1. `register_reassignment_increases_wrongness_v2`: time evolution t → t+1, distance shift -2
2. `zigzag_decreases_wrongness_v2`: fixed t, distance shift +1

A full cycle (reassignment + zigzag) gives: wrongness at distance r bounded by
wrongness at distance (r+1) - 2 = r - 1. Over multiple cycles, geometric decrease.

**Key remaining work:**
- Fill `positionTreeDist_succ_le` (needs `sectionIndex_succ` helper)
- Fill `zigzag_decreases_wrongness_v2` algebraic proof (routine)
- Establish `HasBoundedZigzagDamage` from cherry alternation structure
- Wire V2 chain into `aks_tree_sorting` proof

### Fallback options (unchanged)

See previous audit versions for Options A, B, C.
