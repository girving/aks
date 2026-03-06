> **OBSOLETE:** Superseded by docs/bags.md. Sorry resolution plan from earlier formulation.

# Plan: Resolving Sorries in Strange.lean

## Current State

**5 sorries** in `AKS/Bags/Strange.lean` (updated 2026-03-03):
- ~~`separator_injective_final`: COMPLETED~~
- ~~`stage_exec_on_regs`: COMPLETED~~ — proves stage execution on a bag's registers acts like that bag's separator
- ~~`separator_middle_stranger_le`: REMOVED~~ — optional cruder bound, not needed for main proof
- `separator_filter_strangers` (line ~1155): tighter ε × T bound, used by parent_stranger_j2_le
  - Even case: needs applying separator_injective_initial/final
  - Odd case (line ~1225, 1229): needs handling (may be impossible by construction)
- `parent_stranger_eq1_le` (line ~1410): complex j=1 coefficient

All theorem statements pass empirical testing (rust/test-stranger-bound.rs).

## Key Insight from Seiferas (2009) Section 5

### The Separator Filtering Argument

For j ≥ 2, j-strangers of bag b come from (j-1)-strangers of b.parent that "leak through"
the separator into the middle portion. The key insight from Seiferas:

**The bound is `ε × T`, NOT `separatorMiddleBound`.**

From `separator_injective_initial` and `separator_injective_final`:
- Low strangers (value < anc.lo) in middle ≤ ε × L
- High strangers (value ≥ anc.hi) in middle ≤ ε × H
- Total: strangers in middle ≤ ε × (L + H) = ε × T

### The "Factor of 2 Discrepancy" Resolved

The earlier analysis was confused about two different bounds:

1. **`separatorMiddleBound`**: A worst-case bound that doesn't use the ε factor directly.
   ```
   separatorMiddleBound ≈ min(L, εThresh) + min(H, εThresh) ≤ 2·ε·γ·size
   ```

2. **Actual separator filtering**: The direct bound from Seiferas's argument.
   ```
   strangers in middle ≤ ε × L + ε × H = ε × T
   ```

The `ε × T` bound is TIGHTER than `separatorMiddleBound`. Under IH:
- T ≤ γ·ε^(j-2)·cap
- ε × T ≤ ε × γ·ε^(j-2)·cap = γ·ε^(j-1)·cap ✓ (exactly the target!)

**There is no factor of 2 discrepancy.** The Seiferas argument works directly.

## Proof Structure (Completed)

### `parent_stranger_j2_le` - Proof Structure Complete

The proof is now structured correctly using `separator_filter_strangers`:

1. **Level shift**: b.strangers j = parent.strangers (j-1) via `Bag.strangers_parent_eq`
2. **Separator filtering**: strangers in S ≤ ε × strangers in regs via `separator_filter_strangers`
3. **IH**: parent.strangers(j-1) ≤ γ·ε^(j-2)·cap
4. **Combine**: ε × γ·ε^(j-2)·cap = γ·ε^(j-1)·cap ✓

The only remaining sorry is in `separator_filter_strangers` itself.

## Analysis of Remaining Sorries

### 1. `separator_filter_strangers` (line ~1202)

**Purpose**: Prove the tight ε × T bound from Seiferas.

**Statement** (now with `hT_le` hypothesis for separator conditions):
```lean
(c.strangers j perm_t1 S : ℚ) ≤ p.ε * ↑(c.strangers j perm_t regs)
```

**COMPLETED infrastructure**:
- ✅ `stage_exec_on_regs`: Shows stage execution on c's registers = c's separator
- ✅ Proof structure for even case (separator exists)
- ✅ `hT_le` hypothesis (now uses regs.card for separator bound compatibility)
- ✅ `hL_le` and `hH_le`: L, H ≤ boundary (direct from hT_le)
- ✅ `hstrangers_decomp`: strangers = L + H (disjoint union of low and high)
- ✅ Full proof outline with scatterEmbed_exec_inside coordinate translation

**What remains (even case)**:
1. Formalize bijection S ↔ local positions in [f, C-f) via embed.symm
2. Show fringe f ≥ boundary (using capacity ≥ C relationship)
3. Type-correct application of separator_injective_initial/final
4. Convert between global and local stranger counts

**What remains (odd case)**:
- When C is odd, separator is empty (no filtering)
- Either prove impossible (by construction) or handle trivially

**What remains (call site in parent_stranger_j2_le)**:
- Prove hT_le: IH bound → separator boundary bound
- Requires Seiferas parameter constraints: ε^(j-1) * capacity ≤ regs.card

**Difficulty**: Medium. The structure is complete; remaining work is mechanical.

### 2. `parent_stranger_eq1_le` (line ~1367)

**Purpose**: Bound 1-strangers received from parent (most complex case).

**The coefficient**:
```
ε·γ/A + ε/(2A) + 2γεA/(1-(2εA)²) + 1/(8A³-2A)
```

This comes directly from Seiferas (2009) Section 5 and accounts for:
- Separator filtering (ε factors)
- Sibling-native equidistribution (1/(8A³-2A) term)
- Geometric series from repeated halving (1/(1-(2εA)²) term)

**Difficulty**: Very High. This requires the full paper machinery.

**Risk**: Medium. The statement passes simulation (max ratio ~0.96), so it's correct.

**Recommendation**: Tackle last, after the simpler cases are complete.

## Next Steps

### Priority 1: Complete `separator_filter_strangers` (even case)

Steps 1 and 2 from the original plan are DONE:
- ✅ `stage_exec_on_regs` fully proved
- ✅ Stranger decomposition into low/high done in proof body

Remaining work:
1. Apply separator_injective_initial/final with coordinate translation
2. The infrastructure is all in place; just need to wire it together

### Priority 2: Handle `separator_filter_strangers` (odd case)

Either:
- Prove that interior bags have even register counts (by construction), or
- Handle the trivial bound when C is odd

### Priority 3: `parent_stranger_eq1_le`

After separator_filter_strangers, this is the main remaining piece for the
stranger bound induction. It requires understanding the full Seiferas Section 5
derivation of the complex coefficient.

---

## Comprehensive Plan: `parent_stranger_eq1_le`

### Overview

The j=1 stranger bound is the most complex case in Seiferas (2009) Section 5.
Unlike j≥2, where strangers simply "leak through" the separator, j=1 strangers
are "almost native" — they belong to the parent's interval but not the child's
own interval. This means they are **sibling-native items** that got misrouted.

### Mapping Seiferas to Our Formalization

Seiferas uses parameters (λ, ε, A, ν, b). Our formalization uses:
- `γ` corresponds to Seiferas's `λ` (the stranger coefficient)
- `ε` corresponds to Seiferas's `ε` (separator error)
- `A` corresponds to Seiferas's `A` (capacity ratio between levels)
- `ν` corresponds to Seiferas's `ν` (capacity decay per stage)
- `capacity p k t b.l` corresponds to Seiferas's `b`

### The Coefficient Derivation (Seiferas Section 5, pages 4-5)

The total bound on 1-strangers from parent sources is:
```
εγ/A + ε/(2A) + 2γεA/(1-(2εA)²) + 1/(8A³-2A)
```

This comes from **four distinct sources**:

#### Source 2: Unfiltered 1-strangers from parent D → `εγ/A`

Items that were 1-strangers in the parent bag D (i.e., native to D's sibling,
which is B's "uncle"). These pass through D's separator with at most fraction ε.

- Parent D has at most `γ × (b/A)` 1-strangers (by IH on parent)
- Separator filters out all but ε fraction
- Contribution: `ε × γ × (b/A) = εγ/A × b`

#### Source 3a: Halving errors → `ε/(2A)`

When D runs its separator, items that should go to sibling C may get misrouted
to B due to separator imperfection. This is the "halving error" — items that
should have stayed in C's half but got sent to B's half.

- At most `ε × (d/2)` halving errors, where d = items in D
- d ≤ b/A (parent capacity is b/A)
- Contribution: `ε × (b/A)/2 = ε/(2A) × b`

#### Source 3b-ii: Non-C-native items in C's subtree → `2γεA/(1-(2εA)²)`

Even if there are exactly d/2 C-native items in D (no excess), some C-native
items might be "crowded out" of C's subtree by strangers. These displaced
C-native items end up in D and may be sent to B.

The number of non-C-native items in C's entire subtree is bounded by summing
stranger bounds over all descendants:
```
2γεbA + 8γε³bA³ + 32γε⁵bA⁵ + ...
= 2γεbA × (1 + (2εA)² + (2εA)⁴ + ...)
= 2γεbA / (1 - (2εA)²)
```

This requires `h2εA : (2 * p.ε * p.A) ^ 2 < 1` for convergence.

#### Source 3b-i: C-native items from above D → `1/(8A³-2A)`

Some C-native items might exist in bags *above* D in the tree. By Clause (2)
of Seiferas's invariant (equal distribution), items are spread equally among
subtrees at each level.

If there are 2^i bags at C's level, the total items above D's level is:
```
2^(i-3)×b/A³ + 2^(i-5)×b/A⁵ + ...
```

Native to C (fraction 1/2^i of total):
```
b/(2A)³ + b/(2A)⁵ + b/(2A)⁷ + ...
= b / ((2A)³ × (1 - 1/(2A)²))
= b / (8A³ - 2A)
```

### Proof Structure

#### Phase 1: Infrastructure (in Defs.lean)

**1.1 Define sibling bag:**
```lean
def Bag.sibling (b : Bag k) (hl : 1 ≤ b.l) : Bag k :=
  if b.x % 2 = 0 then b.parent.right else b.parent.left
```

**1.2 Sibling lemmas:**
- `Bag.sibling_parent_eq`: sibling's parent = b's parent
- `Bag.sibling_ne`: sibling ≠ b
- `Bag.sibling_level_eq`: sibling's level = b's level

**1.3 One-stranger characterization:**
```lean
theorem Bag.one_strange_iff_sibling_native (b : Bag k) (hl : 1 ≤ b.l)
    (r : Fin (2^k)) (perm) :
    b.Strange 1 r perm ↔ (b.sibling hl).Native r perm
```

This shows that 1-strangers in B are exactly items native to B's sibling C.

#### Phase 2: Source Decomposition (in Strange.lean)

**2.1 Define stranger sources:**
```lean
-- Source 2: items from uncle (parent's sibling)
def uncle_strangers := ...

-- Source 3a: halving errors
def halving_errors := ...

-- Source 3b: excess sibling-native items
def excess_sibling_native := ...
```

**2.2 Decomposition theorem:**
```lean
theorem one_strangers_decomp (b : Bag k) (hl : 1 ≤ b.l) (perm) (S) :
    b.strangers 1 perm S ≤
    uncle_strangers + halving_errors + excess_sibling_native
```

#### Phase 3: Bound Each Source

**3.1 Uncle stranger bound (Source 2):**
Uses `separator_filter_strangers` applied to parent's 1-strangers.

**3.2 Halving error bound (Source 3a):**
Uses the separator's halving property (`IsSeparator.halving` or similar).

**3.3 Subtree stranger bound (Source 3b-ii):**
Requires summing IH bounds over all descendants of sibling C.
```lean
theorem subtree_stranger_sum (c : Bag k) (j : ℕ) (perm) (regs) :
    (∑ desc in c.descendants, desc.strangers j perm (regs desc))
    ≤ 2γεbA / (1 - (2εA)²)
```

**3.4 Above-level native bound (Source 3b-i):**
Uses Clause (2) — equal distribution — and geometric series.
```lean
theorem above_native_bound (c : Bag k) (perm) :
    (items native to c that are above c.parent.level)
    ≤ b / (8A³ - 2A)
```

This is the most novel part, requiring the "benchmark distribution" argument.

#### Phase 4: Combine Bounds

**4.1 Assembly:**
```lean
theorem parent_stranger_eq1_le ... := by
  -- Decompose 1-strangers
  have hdec := one_strangers_decomp ...

  -- Bound each source
  have h2 := uncle_stranger_bound ...        -- εγ/A
  have h3a := halving_error_bound ...        -- ε/(2A)
  have h3bii := subtree_stranger_bound ...   -- 2γεA/(1-(2εA)²)
  have h3bi := above_native_bound ...        -- 1/(8A³-2A)

  -- Combine via calc
  calc b.strangers 1 perm S
      ≤ uncle_strangers + halving_errors + excess_sibling_native := hdec
    _ ≤ (εγ/A + ε/(2A) + 2γεA/(1-(2εA)²) + 1/(8A³-2A)) × cap := by
        -- Add up individual bounds
        ...
```

### Key Technical Challenges

#### Challenge 1: The Benchmark Distribution Argument

The hardest part is formalizing the "benchmark distribution" from page 5:
> "For this remaining estimate, we compare the current 'actual' distribution
> with a more symmetric 'benchmark' distribution that has an unchanged number
> of items in each bag, but that, for each bag C' on the same level as B,
> has only C'-native items below C'..."

This requires:
1. A predicate for "benchmark distributions"
2. A lemma that any actual distribution has excess ≤ benchmark excess
3. Geometric series bounds for the benchmark case

**Approach**: Instead of formalizing the full benchmark argument, we can use a
more direct counting argument:
- Count C-native items outside C's subtree
- Upper bound by: (items above D's level native to C) + (strangers in C's subtree)

#### Challenge 2: Clause (2) - Equal Distribution

Seiferas's Clause (2): "On each level, the number of items currently in each bag
(or in the entire subtree below) is the same."

This is a **structural invariant** of the algorithm, not currently formalized.
We need:
```lean
theorem clause2_subtree_eq (b c : Bag k) (hl : b.l = c.l) (regs) :
    subtree_size regs b = subtree_size regs c
```

Where `subtree_size` counts items in a bag's subtree.

**Mitigation**: For the `1/(8A³-2A)` term, we only need the weaker fact that
the total items above level ℓ is bounded by capacity at level ℓ-1. This follows
from Clause (3) (capacity bounds).

#### Challenge 3: Summing Over Descendants

For Source 3b-ii, we need to sum stranger bounds over a subtree:
```lean
def Bag.descendants (b : Bag k) : List (Bag k) := ...

theorem strangers_subtree_sum (c : Bag k) (j : ℕ) (hj : 1 ≤ j) ... :
    ∑ d in c.descendants, d.strangers j perm (regs d)
    ≤ 2 * γ * ε * b * A / (1 - (2 * ε * A)²)
```

The geometric series `∑_{i≥0} 2^i × γε^(j+2i) × b × A^(2i+1)` converges when
`(2εA)² < 1`, giving the factor `1/(1-(2εA)²)`.

### Risk Assessment

| Component | Risk Level | Mitigation |
|-----------|------------|------------|
| Sibling infrastructure | Low | Straightforward definitions |
| 1-strange ↔ sibling-native | Low | Direct from definitions |
| Uncle stranger bound | Medium | Depends on separator_filter_strangers |
| Halving error bound | Medium | Need separator halving property |
| Subtree stranger sum | High | Requires descendants machinery |
| Above-level native bound | Very High | Requires Clause (2) or alternative |
| Final assembly | Low | Just arithmetic |

### Estimated Effort

| Component | Lines | Time |
|-----------|-------|------|
| Sibling infrastructure | ~50 | 1 hour |
| 1-strange characterization | ~30 | 30 min |
| Uncle stranger bound | ~50 | 2 hours |
| Halving error bound | ~60 | 2 hours |
| Subtree stranger sum | ~100 | 4 hours |
| Above-level native bound | ~150 | 8+ hours |
| Final assembly | ~80 | 2 hours |
| **Total** | ~520 | 20+ hours |

### Alternative Approach: Axiomatize Clause (2)

If the Clause (2) formalization proves too difficult, we can:
1. Add Clause (2) as an explicit hypothesis to `stranger_bound_succ`
2. Prove it separately as a structural invariant of the algorithm
3. Use it to bound the `1/(8A³-2A)` term

This defers the hardest part while allowing progress on the rest.

### Next Implementation Steps

1. **Add sibling infrastructure to Defs.lean** (first)
2. **Prove 1-strange ↔ sibling-native** (validates the decomposition)
3. **Set up the decomposition skeleton** in parent_stranger_eq1_le
4. **Implement Source 2 bound** (uses existing separator infrastructure)
5. **Implement Source 3a bound** (halving errors)
6. **Assess Clause (2) formalization difficulty**
7. **Implement Sources 3b-i and 3b-ii** (or axiomatize)
8. **Final assembly**

