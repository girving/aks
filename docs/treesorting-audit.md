# TreeSorting.lean Audit — Statement Correctness and Proof Path

**Date:** 2026-02-14
**Sorry count:** 4 (down from 9 after reformulation + proving 3 lemmas + deleting 2 wrong ones)

## Summary

TreeSorting.lean has a **fundamental formalization gap**: `elementsAtDistance` doesn't use
its `t` parameter, making time-dependent reasoning vacuous. This blocks 2 of the 4 remaining
sorries. The other 2 (bridge lemma, main theorem) have correct statements.

## The fundamental issue: time-independent distance

`elementsAtDistance n t v J r` (line 937) filters elements in interval J whose displacement
from `sortedVersion v` exceeds `r * J.size`. The parameter `t` appears in the signature but
is **never used in the body**. This means:

- `treeWrongness n t v J r = treeWrongness n 0 v J r` for all t (definitionally equal)
- Time evolution (t → t+1) is vacuous
- Register reassignment (Lemma 1) can't be formalized without meaningful time dependence

The AKS paper's wrongness Δᵣ(J) measures elements in J that belong to sections at
tree-distance ≥ r. "Sections" are determined by the interval tree at time t. When time
advances, the interval tree refines, changing what counts as "displaced." This time-dependent
aspect is not captured.

## Per-sorry assessment

### 1. `halvers_give_bounded_nearsort` (line 1048) — CORRECT ✅

```lean
∃ (net : ComparatorNetwork n), HasBoundedDamage net ε ∧
  net.comparators.length ≤ halver.comparators.length * (Nat.log 2 n + 1)
```

Existential claim: given an ε₁-halver, there exists a network with bounded damage.
This is independent of the `epsilonNearsort` stub. The AKS recursive construction
(apply halver to full range, then top/bottom halves, etc.) provides the witness.

**Risk:** MEDIUM. The proof requires implementing the recursive construction as a
witness and showing it satisfies `HasBoundedDamage`. The HasBoundedDamage definition
itself might need adjustment (currently uses t=0 which equals all t due to unused t).

### 2. `register_reassignment_increases_wrongness` (line 2452) — WRONG ❌

```lean
treeWrongness n (t+1) v' J' r ≤ 6 * A * treeWrongness n t v J (r - 4)
```

**Problems:**
- `t` vs `t+1` is vacuous (both sides reduce to time-0)
- No tree structure hypotheses explain the r-4 shift
- `h_reassign` and `h_contain` are insufficient — they say WHERE changes happen but not the
  structural relationship between J (old interval) and J' (new interval) in the tree

**To fix:** Either (a) make `elementsAtDistance` time-dependent, or (b) add hypotheses like
`J' = refine(J, t+1)` that encode the tree level relationship.

### 3. `zigzag_decreases_wrongness` (line 2535) — INCOMPLETE ⚠️

```lean
treeWrongness n t v'' J r ≤
  64 * A^2 * (treeWrongness n t v J (r + 1) + ...)
```

The r → r+1 improvement (Δᵣ(after) bounded by Δᵣ₊₁(before)) is the core geometric
decrease mechanism. It requires that zig operates on even tree levels and zag on odd
levels. The current hypothesis `v'' = net.exec (net.exec v)` applies the same network
twice, which can't achieve this improvement (chaining gives Δᵣ, not Δᵣ₊₁).

**To fix:** Either (a) take two different networks (zig_net, zag_net) with hypotheses
about which tree levels they operate on, or (b) add a hypothesis expressing the tree
alternation property.

### 4. `aks_tree_sorting` (line 2605) — CORRECT ✅

```lean
∃ (net : ComparatorNetwork n),
  net.comparators.length ≤ 100 * n * Nat.log 2 n ∧
  Monotone (net.exec v)
```

The statement is mathematically correct as a theorem. Proving it requires all sub-lemmas
to be correct and filled in.

## Dependency chain

```
aks_tree_sorting
├── halvers_give_bounded_nearsort ← correct, sorry
├── register_reassignment_increases_wrongness ← WRONG, sorry
├── zigzag_decreases_wrongness ← incomplete, sorry
├── zig_step_bounded_increase ← PROVED ✅
├── displacement_from_wrongness ← PROVED ✅
└── cherry_wrongness_after_nearsort ← PROVED ✅
```

**Sound if all sorries filled?** NO — two sorries have incorrect/incomplete statements.

## What's proved (correctly)

| Lemma | Line | Status |
|---|---|---|
| `cherry_wrongness_after_nearsort` | 2418 | PROVED |
| `zig_step_bounded_increase` | 2483 | PROVED |
| `displacement_from_wrongness` | 2561 | PROVED |
| `treeWrongness_le_one` | 1471 | PROVED |
| `treeWrongness_nonneg` | 1487 | PROVED |
| `treeWrongness_monotone` | 1572 | PROVED |
| `treeWrongness_zero_eq_displacement` | 1498 | PROVED |
| `tree_wrongness_implies_sorted` | 1515 | PROVED |
| All tree distance lemmas | 537-816 | PROVED |
| All comparator/network preservation lemmas | 2043-2299 | PROVED |

## What's deleted (correctly)

| Item | Reason |
|---|---|
| `exception_distance_bound` | Provably false (counterexample) |
| `fringe_amplification_bound` | Orphaned, mathematically incorrect |
| `halver_implies_nearsort_property` | Conflated aggregate balance with positional damage |
| `epsilonNearsort_correct` | Applied to stub definition, redundant with bridge lemma |

## Path forward

### Option A: Fix `elementsAtDistance` (major, correct)

Make `elementsAtDistance` take the interval tree as a parameter (or make `t` meaningful
by computing sections from `intervalsAt n t`). This would:
- Fix Lemma 1 (register reassignment)
- Enable time-dependent induction in `aks_tree_sorting`
- Require updating all proved lemmas that use `elementsAtDistance`

**Effort:** Weeks. Many proved lemmas need re-verification.

### Option B: Restructure around the gap (moderate)

Accept that `elementsAtDistance` is a time-independent approximation. Reformulate:
- Lemma 1 as a local bound (without time evolution)
- Main theorem to not require time-based induction
- This may require a different proof strategy than the AKS paper

**Effort:** Weeks. Requires creative reformulation.

### Option C: Leave as documented skeleton (minimal)

Keep the current state with detailed comments about what's wrong and what's needed.
The 3 proved lemmas and the bridge lemma are correct building blocks. The rest
needs the time-dependent reformulation before it can be completed.

**Effort:** Done (this audit document).
