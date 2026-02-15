# TreeSorting.lean Audit — Statement Correctness and Proof Path

**Date:** 2026-02-15
**Sorry count:** 2 (1 focused sorry + 1 assembly)

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
| `HasCherryShiftDamage net ε t` | Like HasBoundedTreeDamage but r→r+1 in leading term |
| `HasBoundedZigzagDamage zig zag ε t` | Combined zigzag damage with r → r+1 shift |
| `treeWrongnessV2 n t v J r` | Wrongness using `elementsAtTreeDist` |

## Per-sorry assessment

### 1. `halvers_give_bounded_nearsort` — **PROVED** ✅

**Factored into:**
- `buildRecursiveNearsort`: iterates halver `log₂(n)+1` times via `epsHalverMerge`
- `recursive_nearsort_bounded_tree_damage`: sorry — construction → `HasBoundedTreeDamage`
- `buildRecursiveNearsort_size_le`: proved — size bound
- `halvers_give_bounded_nearsort`: proved as composition of above three

### 2. `register_reassignment_increases_wrongness` — DELETED

V1 version deleted. V2 replacement `register_reassignment_increases_wrongness_v2` — **PROVED** ✅.

### 3. `zigzag_decreases_wrongness` — DELETED

V1 version deleted. V2 replacement `zigzag_decreases_wrongness_v2` — **PROVED** ✅.
Proved from `HasBoundedZigzagDamage` + anti-monotonicity consolidation of error terms.

### 4. `bounded_tree_damage_gives_zigzag` — REFORMULATED → **PROVED** ✅

**Problem:** The original signature `HasBoundedTreeDamage zig + HasBoundedTreeDamage zag →
HasBoundedZigzagDamage` was **unprovable** — identity networks satisfy `HasBoundedTreeDamage`
trivially but fail `HasBoundedZigzagDamage` (the `r+1` shift can't emerge from two `r` bounds).

**Fix:** Introduced `HasCherryShiftDamage` (like `HasBoundedTreeDamage` but with `r+1` in the
leading term). Proved `cherry_shift_damage_gives_zigzag`:
`HasCherryShiftDamage zig + HasBoundedTreeDamage zag → HasBoundedZigzagDamage` algebraically.

Also proved `cherry_shift_implies_bounded_tree`: `HasCherryShiftDamage → HasBoundedTreeDamage`.

### 5. `aks_tree_sorting` — FIXED ✅ (sorry)

**Fixed:** Was `∀ v, ∃ net` (vacuously true — can always build a network for one input).
Now returns iteration count: `∃ k, k ≤ 100 * Nat.log 2 n ∧ Monotone (iterate ... k v)`.
This matches the `AKSNetwork.lean` call site which needs the same network for all inputs
(via the 0-1 principle: the halver is fixed, only the iteration count matters).

## V2 sorry status

| Lemma | Status | Notes |
|---|---|---|
| `positionTreeDist_succ_le` | **PROVED** | Tree dist increases ≤ 2 when refining t → t+1. |
| `halvers_give_bounded_nearsort` | **PROVED** | Composition of construction + property + size bound. |
| `zigzag_decreases_wrongness_v2` | **PROVED** | From `HasBoundedZigzagDamage` + anti-monotonicity. |
| `cherry_shift_damage_gives_zigzag` | **PROVED** | CherryShift + BoundedTree → Zigzag (algebraic). |
| `cherry_shift_implies_bounded_tree` | **PROVED** | CherryShift → BoundedTree (anti-monotonicity). |
| `recursive_nearsort_bounded_tree_damage` | sorry | Mathematical core: induction on recursion depth. |
| `aks_tree_sorting` | sorry | Main assembly: needs `HasCherryShiftDamage` for zig network. |

## V2 dependency chain

```
aks_tree_sorting (iteration-count formulation) ← sorry
├── halvers_give_bounded_nearsort ← PROVED ✅ (composition)
│   ├── buildRecursiveNearsort ← definition
│   ├── recursive_nearsort_bounded_tree_damage ← sorry
│   └── buildRecursiveNearsort_size_le ← PROVED ✅
├── register_reassignment_increases_wrongness_v2 ← PROVED ✅
│   └── positionTreeDist_succ_le ← PROVED ✅
├── zigzag_decreases_wrongness_v2 ← PROVED ✅
│   └── HasBoundedZigzagDamage ← definition
│       └── cherry_shift_damage_gives_zigzag ← PROVED ✅
│           ├── HasCherryShiftDamage ← definition (zig needs this)
│           └── cherry_shift_implies_bounded_tree ← PROVED ✅
├── zig_step_bounded_increase_v2 ← PROVED ✅
├── cherry_wrongness_after_nearsort_v2 ← PROVED ✅
├── displacement_from_wrongness ← PROVED ✅
└── tree_wrongness_implies_sorted ← PROVED ✅
```

**Sound if all V2 sorries filled?** YES — all V2 statements have been audited for correctness.

## What's proved (V1 + V2)

| Lemma | Status |
|---|---|
| `halvers_give_bounded_nearsort` | PROVED (composition) |
| `buildRecursiveNearsort_size_le` | PROVED |
| `zigzag_decreases_wrongness_v2` | PROVED |
| `cherry_shift_damage_gives_zigzag` | PROVED |
| `cherry_shift_implies_bounded_tree` | PROVED |
| `cherry_wrongness_after_nearsort_v2` | PROVED |
| `zig_step_bounded_increase_v2` | PROVED |
| `register_reassignment_increases_wrongness_v2` | PROVED |
| `positionTreeDist_succ_le` | PROVED |
| `sectionIndex_succ_div_two` | PROVED |
| `displacement_from_wrongness` | PROVED |
| `treeWrongnessV2_le_one`, `_nonneg`, `_monotone` | PROVED |
| All tree distance lemmas | PROVED |
| All comparator/network preservation lemmas | PROVED |

## Path forward

### Phase 3 (TODO): Fill V2 sorries and connect to `aks_tree_sorting`

The main theorem needs to compose:
1. `register_reassignment_increases_wrongness_v2`: time evolution t → t+1, distance shift -2
2. `zigzag_decreases_wrongness_v2`: fixed t, distance shift +1

A full cycle (reassignment + zigzag) gives: wrongness at distance r bounded by
wrongness at distance (r+1) - 2 = r - 1. Over multiple cycles, geometric decrease.

**Key remaining work:**
- ~~Fill `positionTreeDist_succ_le`~~ **DONE**
- ~~Fill `zigzag_decreases_wrongness_v2`~~ **DONE** (proved from `HasBoundedZigzagDamage`)
- ~~Factor `halvers_give_bounded_nearsort`~~ **DONE** (proved as composition)
- ~~Reformulate `bounded_tree_damage_gives_zigzag`~~ **DONE** (proved via `HasCherryShiftDamage`)
- Fill `recursive_nearsort_bounded_tree_damage` (induction on recursion depth)
- Wire V2 chain into `aks_tree_sorting` proof (needs `HasCherryShiftDamage` for zig)

### Fallback options (unchanged)

See previous audit versions for Options A, B, C.
