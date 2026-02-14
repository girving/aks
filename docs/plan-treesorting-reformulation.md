# Plan: Reformulate TreeSorting.lean Incorrect Lemma Statements

**Status:** DONE

## Context

Several lemma statements in `AKS/TreeSorting.lean` are mathematically incorrect:

1. **`exception_distance_bound` (line 2478)** is **provably false** — concrete counterexample: comparator (18,19) on n=20 displaces correctly-placed position 18, violating the subset claim.

2. **`halver_implies_nearsort_property` (line 1054)** is **likely false for a single halver** — `IsEpsilonHalver` is an aggregate balance property (bounded ones in top half), not a per-position displacement bound. A single halver can increase distance-based wrongness.

3. **`epsilonNearsort_correct` (line 1690)** is **unprovable with current definition** — `epsilonNearsort` just iterates a halver (simple concatenation), which doesn't achieve ε-sorted output.

4. **`cherry_wrongness_after_nearsort`, `zig_step_bounded_increase`, `zigzag_decreases_wrongness`** (Lemmas 2-3) incorrectly take `IsEpsilonHalver` — they need the stronger **bounded damage** property that only the recursive ε-nearsort construction provides (AKS Section 4).

The root cause: the AKS proof's Lemmas 2-4 operate on **ε-nearsort networks** (composite constructions from many ε₁-halver applications), not individual halvers. The property these lemmas need is **bounded positional damage**, not **aggregate balance**.

## Approach

Introduce `HasBoundedDamage` as the key interface between the halver world (aggregate) and the tree-sorting world (positional). This cleanly separates concerns:

- **Halver side**: `IsEpsilonHalver halver ε₁` → `HasBoundedDamage (nearsort halver) ε` (bridge lemma)
- **Tree sorting side**: Lemmas 2-4 use `HasBoundedDamage`, not `IsEpsilonHalver`

## Changes

All changes are in `AKS/TreeSorting.lean`.

### 1. Add `HasBoundedDamage` definition (~line 943, after `elementsAtDistance`)

```lean
/-- The bounded-damage property: applying the network increases element
    count at distance ≥ r by at most ε times count at distance ≥ (r-2).
    This is the key property that recursive ε-nearsort (AKS Section 4)
    provides. Unlike `IsEpsilonHalver` (aggregate balance), this bounds
    positional displacement — the property needed by Lemmas 2-4. -/
def HasBoundedDamage {n : ℕ} (net : ComparatorNetwork n) (ε : ℝ) : Prop :=
  ∀ (v : Fin n → Bool) (J : Interval n) (r : ℕ),
    ((elementsAtDistance n 0 (net.exec v) J r).card : ℝ) ≤
      (elementsAtDistance n 0 v J r).card +
        ε * (elementsAtDistance n 0 v J (if r ≥ 2 then r - 2 else 0)).card
```

### 2. Replace `halver_implies_nearsort_property` (line 1054-1061) with bridge lemma

Delete the old lemma (lines 1025-1061) and replace with:

```lean
/-- From an ε₁-halver, construct a composite network with bounded damage.
    This encapsulates the recursive ε-nearsort construction (AKS Section 4).
    The composite network applies the halver recursively to sub-ranges,
    yielding the positional bounded-damage property from the aggregate
    balance property.

    The size bound says the composite uses O(log n) copies of the halver. -/
lemma halvers_give_bounded_nearsort
    {n : ℕ} (ε ε₁ : ℝ) (hε : 0 < ε) (hε₁ : 0 < ε₁)
    (hε₁_small : ε₁ ≤ ε / (2 * (Nat.log 2 n + 1)))
    (halver : ComparatorNetwork n) (hhalver : IsEpsilonHalver halver ε₁) :
    ∃ (net : ComparatorNetwork n), HasBoundedDamage net ε ∧
      net.comparators.length ≤ halver.comparators.length * (Nat.log 2 n + 1) := by
  sorry
```

### 3. Update `epsilonNearsort_correct` (line 1690-1697)

Change from `IsEpsilonSorted` to `HasBoundedDamage`:

```lean
/-- The recursive nearsort satisfies the bounded-damage property.
    After applying epsilonNearsort, positional displacement at each
    distance level is controlled. -/
lemma epsilonNearsort_correct {m : ℕ} (ε ε₁ : ℝ) (hε : 0 < ε)
    (halver : ComparatorNetwork m)
    (hε₁ : ε₁ < ε / (Nat.log 2 m) ^ 4)
    (hhalver : IsEpsilonHalver halver ε₁)
    (depth : ℕ) (hdepth : depth ≥ Nat.log 2 m) :
    HasBoundedDamage (epsilonNearsort m ε ε₁ halver depth) ε := by
  sorry
```

### 4. Delete `exception_distance_bound` (lines 2469-2483)

Remove entirely — it's provably false and nothing depends on it.

### 5. Update `cherry_wrongness_after_nearsort` (lines 2419-2430)

Replace `IsEpsilonHalver net ε` with `HasBoundedDamage net ε`:

```lean
lemma cherry_wrongness_after_nearsort
    {n t : ℕ} (net : ComparatorNetwork n) (ε : ℝ) (hnet : HasBoundedDamage net ε)
    (cherry : Cherry n) (v : Fin n → Bool) (J : Interval n) (r : ℕ)
    (h_in_cherry : J = cherry.parent ∨ J = cherry.leftChild ∨ J = cherry.rightChild) :
    treeWrongness n t (net.exec v) J r ≤
      treeWrongness n t v J r + ε * treeWrongness n t v J (if r ≥ 2 then r - 2 else 0) := by
  sorry
```

### 6. Update `register_reassignment_increases_wrongness` (lines 2445-2450)

Add missing `J ⊆ J'` hypothesis:

```lean
lemma register_reassignment_increases_wrongness
    {n t : ℕ} (v v' : Fin n → Bool) (J J' : Interval n) (r : ℕ) (ε : ℝ)
    (h_reassign : ∀ i : Fin n, v' i ≠ v i → i ∈ J'.toFinset)
    (h_contain : J.toFinset ⊆ J'.toFinset)
    (hr : r ≥ 4) :
    treeWrongness n (t+1) v' J' r ≤ 6 * A * treeWrongness n t v J (r - 4) := by
  sorry
```

### 7. Update `zig_step_bounded_increase` (lines 2508-2524)

Replace `IsEpsilonHalver net ε` with `HasBoundedDamage net ε`:

```lean
lemma zig_step_bounded_increase
    {n t : ℕ} (v v' : Fin n → Bool) (net : ComparatorNetwork n)
    (ε : ℝ) (hnet : HasBoundedDamage net ε) (r : ℕ) (J : Interval n)
    (h_zig : v' = net.exec v) :
    treeWrongness n t v' J r ≤
      8 * A * (treeWrongness n t v J r +
               if r ≥ 3 then ε * treeWrongness n t v J (r - 2)
               else ε) := by
  sorry
```

### 8. Update `zigzag_decreases_wrongness` (lines 2540-2549)

Replace `IsEpsilonHalver net ε` with `HasBoundedDamage net ε`:

```lean
lemma zigzag_decreases_wrongness
    {n t : ℕ} (v v'' : Fin n → Bool) (net : ComparatorNetwork n)
    (ε : ℝ) (hnet : HasBoundedDamage net ε) (r : ℕ) (J : Interval n)
    (h_zigzag : v'' = net.exec (net.exec v)) :
    treeWrongness n t v'' J r ≤
      64 * A^2 * (treeWrongness n t v J (r + 1) +
                  if r ≥ 5 then 3 * ε * treeWrongness n t v J (r - 4)
                  else 3 * ε) := by
  sorry
```

### 9. Update `aks_tree_sorting` (lines 2607-2615)

Keep `IsEpsilonHalver` as the top-level hypothesis, but restructure to use the bridge lemma internally. Add ε₁ parameter:

```lean
theorem aks_tree_sorting {n : ℕ} (ε ε₁ : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1/2) (hε₁ : 0 < ε₁)
    (hε₁_small : ε₁ ≤ ε / (2 * (Nat.log 2 n + 1)))
    (halver : ComparatorNetwork n) (hhalver : IsEpsilonHalver halver ε₁)
    (v : Fin n → Bool) :
    ∃ (net : ComparatorNetwork n),
      net.comparators.length ≤ 100 * n * Nat.log 2 n ∧
      Monotone (net.exec v) := by
  sorry
```

### 10. Update roadmap comment (lines 2360-2384)

Update to reflect the new structure with `HasBoundedDamage`.

### 11. Update visualization (`docs/index.html`)

- Rename `halver_implies_nearsort_property` node to `halvers_give_bounded_nearsort`
- Add `HasBoundedDamage` definition node
- Update edges accordingly

## Verification

```bash
scripts/lean-check AKS/TreeSorting.lean    # Must compile with no errors
scripts/sorries | grep TreeSorting          # Sorry count should stay ~9
```

## Summary of sorry changes

| Lemma | Before | After |
|---|---|---|
| `halver_implies_nearsort_property` | sorry (wrong statement) | DELETED |
| `halvers_give_bounded_nearsort` | (new) | sorry (correct statement) |
| `epsilonNearsort_correct` | sorry (wrong: `IsEpsilonSorted`) | sorry (correct: `HasBoundedDamage`) |
| `exception_distance_bound` | sorry (provably false) | DELETED |
| `cherry_wrongness_after_nearsort` | sorry (`IsEpsilonHalver`) | sorry (`HasBoundedDamage`) |
| `register_reassignment_increases_wrongness` | sorry (missing hyp) | sorry (added `h_contain`) |
| `zig_step_bounded_increase` | sorry (`IsEpsilonHalver`) | sorry (`HasBoundedDamage`) |
| `zigzag_decreases_wrongness` | sorry (`IsEpsilonHalver`) | sorry (`HasBoundedDamage`) |
| `aks_tree_sorting` | sorry (wrong structure) | sorry (correct structure) |

Net: 9 sorry's → 8 sorry's (deleted 2 false/wrong, added 1 new bridge lemma)
