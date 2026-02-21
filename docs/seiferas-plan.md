# Seiferas Path: Remaining Work and Parallelism Analysis

## Current Status (2026-02-21)

The Seiferas path (expanders -> halvers -> separators -> bag-tree sorting) has
its proof skeleton fully assembled. The sorry count in the Bags subsystem is:

| File | Theorem | Status |
|------|---------|--------|
| `SplitProof.lean` | `stranger_fringe_bound` for concreteSplit | sorry (needs item conservation, see S2a) |
| `SplitProof.lean` | `small_cap_even` for concreteSplit | sorry (needs subtree counting / item conservation, see S1) |
| `SplitStranger.lean` | `concreteSplit_fromParent_filtered` | **PROVED** |
| `SplitStranger.lean` | `siblingNative_le_deviation` | **PROVED** (Sub-lemma A: rank structure) |
| `SplitStranger.lean` | `below_boundary_deviation` | sorry (Sub-lemma B: deviation bound, 75% confidence) |
| `SplitStranger.lean` | `concreteSplit_cnative_bound` level≥1 | sorry (assembly proved, chains A + B) |
| `TreeSort.lean` | `separatorSortingNetwork_sorts` | sorry (65% confidence) |

**Proved** (this session and prior):
- `concreteSplit_hkick` -- parent kick <= `2lam*cap + 1`
- `concreteSplit_hsend_left` / `hsend_right` -- child <= `cap/2`
- `concreteSplit_hkick_pair` -- paired kick <= `4lam*cap(l+1)` when `cap(l) < A`
  (proved, uses `small_cap_even` invariant clause)
- `bags_even_at_small_cap` -- even bag sizes when cap < A
  (trivial from `small_cap_even` clause)
- `concreteSplit_hrebag_uniform` -- uniform rebag sizes
- `concreteSplit_hrebag_disjoint` -- disjoint rebag bags
- `concreteSplit_fromParent_filtered` -- ε-filtering for concrete split (LHS = 0)
- `kick_stranger_bound` -- fringe strangers at parent level
- `parent_stranger_bound` -- parent strangers for j >= 2 (abstract, depends on `hfilter`)
- `parent_1stranger_from_inv` -- parent 1-strangers (abstract, depends on `hfilter` + `hcnative`)
- `invariant_maintained` -- abstract invariant maintenance (zero sorry, `Invariant.lean`)
- `concreteSplit_maintains_invariant` -- concrete invariant maintenance (assembly, `SplitProof.lean`)
- `separatorSortingNetwork_depth_le` -- depth bound `O(log n)`
- `separatorSortingNetwork_converges` -- convergence when bags <= 1 item
- `seiferas_sorting_networks_exist` -- top-level theorem (modulo `separatorSortingNetwork_sorts`)

## Architecture

```
Split.lean          -- concreteSplit definition, rankInBag, fringeSize, childSendSize
     |          |
SplitCard.lean   SplitStranger.lean  -- cardinality bounds / stranger bounds
     |          |
SplitProof.lean                     -- concreteSplit_maintains_invariant (assembly)
     |
TreeSort.lean                       -- separatorSortingNetwork_sorts
     |
Seiferas.lean                       -- seiferas_sorting_networks_exist
```

## Remaining Sorries: Detailed Analysis

### S1: `small_cap_even` maintenance — needs subtree counting

**Status:** sorry'd. The clause is TRUE (follows from Seiferas's argument)
but NOT provable from the current invariant.

**Background:** `small_cap_even` (clause 9) states: when `cap(t, level) < A`,
bags at level+1 have even card. This is used by `hkick_pair` to eliminate the
+2 additive term in paired kicks for Case 2 of `capacity_maintained`.

**Why it's not provable now:** Our `uniform_size` (clause 2) only tracks that
bags at the same level have equal card. Seiferas's Clause (2) (Section 4, p.3)
is STRONGER — it tracks subtree totals: "the number of items currently in
each bag (or in the entire subtree below) is the same." Without subtree
counting, we can't derive even-size at the child level.

**Failed approach (asymmetric split):** Sending the odd excess to a child
instead of parent would eliminate the need for `small_cap_even`, but it
BREAKS `uniform_size` — left and right children would get different item
counts, and `fromParent` for even- vs odd-indexed bags would differ.

**Seiferas's argument (Section 5, p.4):** When `cap(d) < A`:
1. `cap(j) < 1` for all `j < d`, so bags at depths 0..d-1 are empty
2. By Clause (2) + item conservation: each of the `2^(d+1)` subtrees at
   depth d+1 has `n/2^(d+1)` items
3. `n = 2^k`, so `n/2^(d+1) = 2^(k-d-1)` which is even when `d ≤ k-2`
   (true since `d < maxLevel = k-1`)
4. Each bag at depth d+1 has passed equal items to both children (by the
   equal-halving split), so `bag_card = subtree_total - 2*child_subtree_total`
   is even (difference of even numbers)
5. Therefore `toParent = 2f` (no +1), paired kick has no +2

**Fix: strengthen invariant with subtree counting.** This is the same
infrastructure needed for S2a (`stranger_fringe_bound`). The work items:

1. Add `items_partition` clause: items partition across bags (conservation)
2. Strengthen `uniform_size` to track subtree totals (Seiferas Clause 2)
3. Fix `concreteSplit` at root: `toParent = ∅` when `level = 0`
   (root has no parent — currently fringe items are lost)
4. Fix `concreteSplit` at leaf levels: `toParent = regs` when
   `maxLevel ≤ level` (currently middle items lost at leaves)
5. Derive `small_cap_even` from strengthened invariant
6. Derive `stranger_fringe_bound` from item conservation + `stranger_bound`

**Empirically validated:** Python simulation (`/tmp/test_small_cap_even_v2.py`)
with item conservation (root fix + leaf fix) shows zero `small_cap_even`
violations for n = 8..16384, 50 stages. Without conservation, the original
simulation showed violations starting at n = 128.

**Impact on I3 (cnative_bound):** None. The split definition is unchanged.

**Difficulty:** MEDIUM-HARD. 2-3 weeks. See I4 below.

**Key reference:** Seiferas Section 4 (p.3, Clause 2), Section 5 (p.4).

### S2: `concreteSplit_fromParent_filtered` (SplitStranger.lean) -- **PROVED**

**Statement:** Among items sent from parent to child (`fromParent`), the
j-stranger count at the parent level is at most `eps` times the full parent
bag's j-stranger count.

**Status: PROVED.** LHS = 0 because all j-strangers have extreme perm values
(via `isJStranger_antitone` + `isJStranger_one_perm_bound`), giving them
extreme ranks (via `rankInBag_lt_count_below` / `rankInBag_ge_count_below`),
which places them in the fringe, not in fromParent (middle items).

**Prerequisite added:** `stranger_fringe_bound` clause added to `SeifInvariant`
(clause 7): `jStrangerCount(..., 1) ≤ lam * card`. This ensures the number of
1-strangers fits in the fringe size `⌊lam * card⌋₊`. The clause's maintenance
in `invariant_maintained` is sorry'd (see below).

### S2a: `stranger_fringe_bound` maintenance (Invariant.lean)

**Statement:** After rebag, the 1-stranger count relative to (level, idx)
is at most `lam * (rebag card)`.

**Status: sorry'd.** NOT provable from the current invariant.

**Root cause:** `stranger_bound` (clause 3) gives `stranger ≤ lam * cap`, but
`stranger_fringe_bound` needs `stranger ≤ lam * card`. Since `capacity_bound`
gives `card ≤ cap` (wrong direction), `lam * cap ≥ lam * card` and the
implication fails. When `cap > card`, the stranger count can exceed
`lam * card` while satisfying `lam * cap`.

**Fix: item conservation + subtree counting.** Seiferas's paper implicitly
assumes items always occupy exactly one bag, so `∑ card = n` at every stage,
keeping `card ≈ cap`. This is the SAME infrastructure needed for S1
(`small_cap_even`). See I4 below for the unified plan.

**Difficulty:** MEDIUM-HARD. 2-3 weeks (shared with S1).

### S3: `concreteSplit_cnative_bound` (SplitStranger.lean)

**Statement:** Sibling-native items among `fromParent` are bounded by
`cnativeCoeff * cap(parent)`.

**Confidence: 75%.** Statement likely correct but relies on separator
guarantee that we may not have formalized precisely enough.

**Key insight (from Rust validation):** Only term (a) -- halving error --
is nonzero (max ratio 0.1793). Terms (b), (c), (d) are identically 0 for
the concrete split. So the proof reduces to bounding the halving error.

**Halving error argument:** Sibling-native items are 1-strangers but not
2-strangers: native to the parent but assigned to the wrong child. The
mismatch occurs when an item's native child (determined by `nativeBagIdx`)
differs from its rank-based assignment in the parent's split (determined by
`rankInBag` threshold at `f + h`).

**Proof strategy:**
1. Define "native child" formally: `nativeBagIdx n (l+1) r` determines
   which child an item with native rank `r` belongs to
2. Show the rank-based split (threshold at `f + h` where h = childSendSize)
   approximates the native-child boundary
3. Items where rank-based assignment != native assignment are bounded by
   the separator's epsilon error (misplacement count)

**Risk:** The formal connection between `nativeBagIdx` and `rankInBag`
threshold requires the separator guarantee. The `cnativeCoeff` is defined
in `Invariant.lean` and includes geometric series terms (b, c, d) that are
0 for the concrete split. The proof may be simpler if we can show terms
(b)-(d) are zero directly.

**Files touched:** `SplitStranger.lean` (proof body at line ~270), possibly
`Split.lean` (shared rank infrastructure with S2).

**Independent of S1.** Does not need item conservation or leaf-level fixes.

**Estimate:** 2-4 weeks.

### S4: `separatorSortingNetwork_sorts` (TreeSort.lean)

**Statement:** The full separator sorting network produces monotone output.

**Confidence: 65%.** Statement correct but infrastructure incomplete.

**Difficulty:** HARD. This is the main correctness theorem. Requires:
1. Connecting `concreteSplit` to `separatorStage` (currently a placeholder
   with `comparators := []`)
2. Induction: each stage maintains `SeifInvariant`
3. Convergence: after O(log n) stages, all bags have <= 1 item
4. All bags <= 1 item => output is sorted (zero strangers => monotone)

**Dependencies:** S1-S3 (for invariant maintenance at each stage).
Also needs a real `separatorStage` implementation that applies the separator
to each active bag and matches the `concreteSplit` abstraction.

**Risk:** HIGH. Step 4 (convergence => sorted) is conceptually clear but
formally requires showing that when all bags have <= 1 item, the output
permutation is the identity. This needs a bridge between the bag-tree
abstraction and the actual comparator network execution.

**NOT ready for parallel work** -- depends on S1-S3 and needs substantial
infrastructure (wire<->bag bridge).

**Estimate:** 3-6 weeks (includes implementing `separatorStage`).

## Parallel Instance Analysis

### Dependency Graph

```
S1 (small_cap_even) --------+
                             +--> I4: item conservation + subtree counting
S2a (stranger_fringe_bound) -+
S2 (fromParent_filtered) ---- DONE
S3 (cnative_bound) ----------------> S4 (assembly + convergence->sorted)
```

I3 and I4 are **fully independent** of each other:
- I3 bounds sibling-native count in `fromParent` (doesn't need item conservation)
- I4 adds `items_partition` + subtree counting to prove S1 and S2a

### Parallel Instances

| Instance | Task | Status |
|----------|------|--------|
| **I2** | S2: Prove `concreteSplit_fromParent_filtered` | **DONE** |
| **I3** | S3: Prove `concreteSplit_cnative_bound` | Sub-lemma A proved, Sub-lemma B sorry'd |
| **I4** | S1+S2a: Item conservation + subtree counting | NEXT UP |

**Conflict risks:** I4 adds new clauses to `SeifInvariant` and modifies
`concreteSplit` at leaf levels. I3 reads `concreteSplit` but only at
non-leaf levels — no conflict. I4 can proceed in parallel with I3.

### Instance I4: Item Conservation + Subtree Counting (NEXT UP)

**Goal:** Prove both `small_cap_even` and `stranger_fringe_bound`
maintenance by strengthening `SeifInvariant` with subtree counting
(Seiferas's Clause 2) and item conservation.

**Execution plan:**
1. Fix `concreteSplit` boundary cases:
   - Root (`level = 0`): `toParent = ∅` (no parent to kick to)
   - Leaf (`maxLevel ≤ level`): `toParent = regs` (no children)
2. Add `items_partition` clause to `SeifInvariant`:
   all items are in exactly one bag at each stage
3. Strengthen `uniform_size` to track subtree totals:
   `subtree_total level idx = n / 2^level` (Seiferas Clause 2)
4. Prove split is exhaustive:
   `toParent ∪ toLeftChild ∪ toRightChild = regs` (at interior levels)
5. Prove initial state satisfies new clauses
6. Prove new clauses maintained through `rebag`:
   - Item conservation: items flow from old bags to new bags bijectively
   - Subtree totals halve at each level
7. Derive `small_cap_even` from subtree counting:
   when cap(d) < A, subtree total at d+1 is `n/2^(d+1)` (even),
   bag has passed equal items to children → bag card is even
8. Derive `stranger_fringe_bound` from item conservation:
   with `∑ card = n`, `card ≈ cap`, so `stranger ≤ lam*cap ≈ lam*card`

**Estimate:** 2-3 weeks.

**Key reference:** Seiferas Section 2 (p.2), Section 4 (p.3, Clause 2),
Section 5 (p.4).

### Instance I2: **COMPLETED**

**Goal:** Prove `concreteSplit_fromParent_filtered`. **PROVED.**

Added `stranger_fringe_bound` clause to `SeifInvariant` (clause 7).
The filtering proof shows LHS = 0 via:
1. j-stranger → 1-stranger (`isJStranger_antitone`)
2. 1-stranger → perm outside native interval (`isJStranger_one_perm_bound`)
3. Extreme perm → extreme rank (`rankInBag_lt_count_below` / `rankInBag_ge_count_below`)
4. Stranger count ≤ fringeSize (from `stranger_fringe_bound`)
5. Extreme rank → in fringe → not in fromParent

**Remaining gap:** `stranger_fringe_bound` maintenance in `invariant_maintained`
is sorry'd — requires item conservation (see S2a above).

### Instance I3: Detailed Plan (IN PROGRESS)

**Goal:** Prove `concreteSplit_cnative_bound`.

**Progress:** Level=0 case proved. Factored into `below_boundary_deviation`
(sorry'd sub-lemma) + assembly for level≥1. Added `cnativeCoeff_nonneg` and
`siblingNativeCount_empty`/`siblingNativeCount_le_card` helper lemmas.

**Confidence: 75%.** Statement correct (validated by Rust). The mathematical
argument is Seiferas's benchmark distribution comparison (Section 5, p.5).

#### Mathematical Analysis

**Setup.** Parent bag D = bags(level-1, p) has b items. The `concreteSplit`
sorts items by `rankInBag perm` (exact sorted order within D), removes the
fringe (lowest f and highest f ranked items to grandparent), and splits the
middle into left child (rank [f, f+h)) and right child (rank [f+h, f+2h))
where f = ⌊λ·b⌋ and h = childSendSize = ⌊b/2⌋ - f. When b is odd, the
extra middle item goes to parent (preserving `uniform_size`).

**Four contiguous groups.** Items in D sorted by perm value partition into:
- `s_lo`: below-strangers (perm < p·bs, native to bags left of D)
- `n_L`: left-native (perm ∈ [p·bs, p·bs + bs/2), native to left child)
- `n_R`: right-native (perm ∈ [p·bs + bs/2, (p+1)·bs), native to right child)
- `s_hi`: above-strangers (perm ≥ (p+1)·bs, native to bags right of D)

where bs = bagSize n (level-1). Ranks in D match sorted perm order, so:
ranks [0, s_lo) → s_lo items; [s_lo, s_lo+n_L) → n_L; etc.

**Key quantity:** C = s_lo + n_L = count of items with perm below the child
boundary. The split point between left/right children is at rank ⌊b/2⌋.

**Rank-structure bound (Sub-lemma A, proved in Rust):**
```
siblingNativeCount(toLeftChild, level, 2p)
    = |{right-native items with rank ∈ [f, f+h)}|
    = |[C, C+n_R) ∩ [f, f+h)|
    ≤ max(0, ⌊b/2⌋ - C)     -- upper bound, exact when C ≥ f
```

Similarly for the right child: siblingNativeCount ≤ max(0, C - ⌈b/2⌉).

**Deviation formula:**
```
⌊b/2⌋ - C = ⌊(s_lo + n_L + n_R + s_hi)/2⌋ - (s_lo + n_L)
           = (n_R - n_L + s_hi - s_lo)/2     (when b is even)
```

So siblingNativeCount ≤ |C - ⌊b/2⌋| ≤ (|n_L - n_R| + |s_lo - s_hi|) / 2
                                        ≤ (|n_L - n_R| + s_lo + s_hi) / 2.

#### Rust Validation (`rust/test-cnative-decompose.rs`)

Empirical results (n = 8..16384, all stages until convergence):

| Quantity | Max ratio | Denominator | Status |
|----------|-----------|-------------|--------|
| sn / (cnc·cap) | 0.035 | cnativeCoeff·cap(parent) | **OK** (bound holds) |
| \|n_L-n_R\| / cap | 0.0018 | cap(parent) | Native imbalance is tiny |
| \|s_lo-s_hi\| / (λ·cap) | 0.013 | λ·cap(parent) | Stranger asymmetry tiny |
| native_contrib | 0.033 | 2·cnc·cap | **Dominates** (93% of bound) |
| stranger_contrib | 0.002 | 2·cnc·cap | Small (7% of bound) |

Worst case: n=16384 t=20 lev=5 idx=0, sn=29 b=974 s_lo=0 n_L=458 n_R=512
s_hi=4 C=458 b/2=487 cap=29695.

**Key finding:** Formula mismatches (1068) are all cases where formula > actual
(the fringe captures some sibling-native items). The formula is always an upper
bound. The mismatches do not affect correctness.

#### Proof Decomposition

**Sub-lemma A (Rank Structure, ~Medium):** In `Split.lean`.
```lean
theorem siblingNativeCount_fromParent_le_deviation
    ... (level idx : ℕ) (hlev : 1 ≤ level) :
    siblingNativeCount n perm (fromParent (concreteSplit lam perm bags) level idx) level idx ≤
    let B := bags (level - 1) (idx / 2)
    let boundary := (idx / 2) * bagSize n (level - 1) + bagSize n level
    let C := (B.filter (fun i => (perm i).val < boundary)).card
    Int.natAbs (↑C - ↑(B.card / 2))
```

Proof sketch:
1. Unfold fromParent → toLeftChild or toRightChild of parent bag
2. Items in toLeftChild have rank ∈ [f, f+h) where f+h = ⌊b/2⌋
3. Sibling-native items are right-native (perm ≥ boundary) with rank < ⌊b/2⌋
4. Count = max(0, ⌊b/2⌋ - C) since right-native items occupy ranks [C, C+n_R)
5. max(0, ⌊b/2⌋ - C) ≤ |C - ⌊b/2⌋|

Uses: `rankInBag_lt_count_below`, `rankInBag_ge_count_below`, exact rank
counting from `SplitCard.lean`.

**Sub-lemma B (Deviation Bound, ~Hard):** In `SplitStranger.lean`.
```lean
theorem below_boundary_deviation
    (inv : SeifInvariant ...) (hparams : SatisfiesConstraints ...)
    (level idx : ℕ) (hlev : 1 ≤ level) :
    let B := bags (level - 1) (idx / 2)
    let boundary := ...
    let C := (B.filter ...).card
    (Int.natAbs (↑C - ↑(B.card / 2)) : ℝ) ≤
    cnativeCoeff A lam ε * bagCapacity n A ν t (level - 1)
```

This is the HARD sub-lemma. Proof strategy (Seiferas Section 5, p.5):

**Decompose** |C - b/2| = |(n_L - n_R + s_lo - s_hi)| / 2 into:

**(B1) Stranger contribution:** |s_lo - s_hi| / 2 ≤ (s_lo + s_hi) / 2
    ≤ λ/2 · cap(parent) [from invariant clause 4 at j=1].
    This contributes ≤ λ/2 ≈ 0.00505 to the coefficient.

**(B2) Native imbalance:** |n_L - n_R| / 2 ≤ ?
    Bounded by Seiferas's benchmark distribution comparison:

    Compare actual tree to a "benchmark" where each bag C' at this level
    has only C'-native items below it and d/2 C'-native items in its parent.
    In the benchmark, n_L = n_R exactly. Excess comes from two sources:

    **(B2a) Subtree stranger displacement:** Non-native items entering C's
    subtree displace C-native items upward. At each level l in C's subtree,
    at most λε^(j-1)·cap(l) strangers. Summing the cascade:
    ≤ 2λεA·cap(level) / (1-(2εA)²) = 2λεA²·cap(parent) / (1-(2εA)²)
    Contributes ≈ 0.000211 to the coefficient.

    **(B2b) Above-parent items:** C-native items on levels above D
    contribute to n_R imbalance. Bounded by geometric series in 1/(2A)²:
    ≤ cap(level) / (8A³-2A) = cap(parent) / (8A²-2)
    Contributes ≈ 0.00125 to the coefficient.

    **(B2c) Halving adjustment:** For the exact sort, the rank-based split
    at ⌊b/2⌋ is exact (no separator error), but the ε/2 term in
    cnativeCoeff provides additional slack. Total needed:
    λ/2 + (B2a) + (B2b) ≤ cnativeCoeff = ε/2 + 2λεA²/(1-(2εA)²) + 1/(8A²-2).
    Since λ = ε in Seiferas's parameters, λ/2 ≤ ε/2. ✓

**Risk assessment:** Sub-lemma A is ~~MEDIUM~~ **DONE** (standard Finset combinatorics, proved).
Sub-lemma B is HIGH — the benchmark distribution argument requires multi-level
tree accounting. B2a and B2b each need geometric series summing stranger
bounds across levels. This is the hardest single proof in the entire Bags
subsystem.

**Fallback:** If the benchmark argument proves too complex to formalize,
we can sorry Sub-lemma B and prove Sub-lemma A + assembly. This reduces the
sorry surface from one opaque `concreteSplit_cnative_bound` to one clean
mathematical statement (deviation bound) with validated semantics.

**Alternative approach:** Strengthen `SeifInvariant` with a native-balance
clause (track |n_L - n_R| explicitly). This would make Sub-lemma B trivial
but requires modifying the invariant (interaction with S1 work).

#### Recommended Execution Order

1. ~~Prove level=0 case (trivial: fromParent = ∅)~~ **DONE**
2. ~~Factor into `below_boundary_deviation` sub-lemma~~ **DONE**
3. ~~Prove Sub-lemma A (rank structure → `siblingNative_le_deviation`)~~ **DONE**
4. Prove Sub-lemma B (`below_boundary_deviation`) — factor into B1 + B2a + B2b — 2-4 weeks
5. ~~Assemble level≥1 case of `concreteSplit_cnative_bound`~~ **DONE** (chains A + B)

**Total remaining estimate:** 2-4 weeks (Sub-lemma B only).

**Shared infrastructure with I2:** Both need rank-perm ordering lemmas
from `Split.lean`. If I2 and I3 run in parallel, coordinate so that shared
helpers go in `Split.lean` (avoid conflicts in `SplitStranger.lean`).

## Other Sorries (Outside Bags Subsystem)

The full project has 15 sorries total. The Bags subsystem accounts for 5.
The remainder:

| Area | Count | Key theorems |
|------|-------|-------------|
| `Graph/Quotient.lean` | 1 | `spectralGap_quotient` (Cauchy interlacing) |
| `Graph/Walk.lean` | 2 | `spectralGap_contract`, `spectralGap_toGraph` |
| `ZigZag/Expanders.lean` | 1 | `explicit_expanders_exist_zigzag` (needs quotient graphs) |
| `Seiferas.lean` | 1 | `seiferas_sorting_networks_exist` (depends on S4) |

The Tree path (AKSNetwork, DamageStability, DamageImprovement, Sorting,
Nearsort) has been deleted. Only the Seiferas path remains.

## Key Seiferas Paper References

- **Section 2** (p.2): Item conservation assumption ("always occupy one of n-1 bags")
- **Section 3** (p.3): Leaf bag handling, odd excess kicked to parent
- **Section 4** (p.3): Clause (2) -- subtree uniformity (stronger than our `uniform_size`)
- **Section 5** (p.4): Even-size argument when cap < A; the b < A capacity case
- **Section 5** (p.4-5): Stranger bound maintenance (eps-filtering, cnative)
