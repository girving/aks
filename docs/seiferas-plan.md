# Seiferas Path: Remaining Work and Parallelism Analysis

## Current Status (2026-02-20)

The Seiferas path (expanders -> halvers -> separators -> bag-tree sorting) has
its proof skeleton fully assembled. The sorry count in the Bags subsystem is:

| File | Theorem | Status |
|------|---------|--------|
| `SplitCard.lean` | `bags_even_at_small_cap` | **FALSE as stated** — needs invariant fix |
| `SplitStranger.lean` | `concreteSplit_fromParent_filtered` | sorry (90% confidence) |
| `SplitStranger.lean` | `concreteSplit_cnative_bound` | sorry (75% confidence) |
| `TreeSort.lean` | `separatorSortingNetwork_sorts` | sorry (65% confidence) |

**Proved** (this session and prior):
- `concreteSplit_hkick` -- parent kick <= `2lam*cap + 1`
- `concreteSplit_hsend_left` / `hsend_right` -- child <= `cap/2`
- `concreteSplit_hkick_pair` -- paired kick <= `4lam*cap(l+1)` when `cap(l) < A`
  (proved, modulo `bags_even_at_small_cap`)
- `concreteSplit_hrebag_uniform` -- uniform rebag sizes
- `concreteSplit_hrebag_disjoint` -- disjoint rebag bags
- `kick_stranger_bound` -- fringe strangers at parent level
- `parent_stranger_bound` -- parent strangers for j >= 2 (abstract, depends on `hfilter`)
- `parent_1stranger_from_inv` -- parent 1-strangers (abstract, depends on `hfilter` + `hcnative`)
- `concreteSplit_maintains_invariant` -- full invariant maintenance (assembly, in `SplitProof.lean`)
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

### S1: `bags_even_at_small_cap` (SplitCard.lean) -- **FALSE AS STATED**

**Statement:** When `bagCapacity n A ν t l < A`, all bags at level `l+1`
have even `card`.

**The statement is FALSE.** The current `SeifInvariant` does not contain
enough information to prove this. Counterexample: n=8, bags(1,0)={0,1,2},
bags(1,1)={4,5,6} satisfies all 6 clauses of `SeifInvariant` (alternating
empty, uniform size 3, capacity bound, stranger bound, bags disjoint,
bounded depth) but has odd card = 3.

**Root Cause 1: Missing item conservation.** Seiferas (Section 2, p.2)
assumes "we consider each of them always to occupy one of n-1 bags" --
items are NEVER lost. Our `SeifInvariant` has `bags_disjoint` (no item in
two bags) but not `items_partition` (every item in some bag). Without this,
the invariant allows states where items vanish, making the total-items-per-
subtree argument impossible.

**Root Cause 2: Leaf-level item loss in `concreteSplit`.** At leaf levels
(`maxLevel n <= level`), `toLeftChild = {}` and `toRightChild = {}`. But
`toParent` only captures fringe items (rank < f or rank >= f+2h). Items
with rank in [f, f+2h) go NOWHERE and are permanently lost. This violates
item conservation.

**Root Cause 3: Invariant too weak.** Seiferas's Clause (2) (Section 4,
p.3) is STRONGER than our `uniform_size`. It tracks: "the number of items
currently in each bag (or in the entire subtree below) is the same" --
subtree totals, not just individual bag sizes.

**Fix Plan (3 coordinated changes):**

#### A. Add item conservation to `SeifInvariant`

Add a new clause to `SeifInvariant`:

```lean
items_partition : Finset.univ = (Finset.univ.biUnion
  (fun l => (Finset.range (2^l)).biUnion (fun idx => bags l idx)))
```

Or equivalently, track that the total items across all bags at a given level
equals `n` (item count is conserved). Consider also strengthening
`uniform_size` to track subtree totals per Seiferas's Clause (2).

Key references: Seiferas Section 2 (p.2), Section 4 (p.3, Clause 2).

#### B. Fix `concreteSplit` at leaf levels

When `maxLevel n <= level`, change the split so that `toParent = regs`
(ALL items go to parent). Currently only fringe items go to parent and
middle items are lost. The fix:

```lean
toParent := if maxLevel n <= level then regs
            else regs.filter (fun i => ...)
```

**Seiferas's approach (Section 3, p.3):** At leaf levels, bags have at most
n/2^maxLevel = 2 items (from subtree uniformity + item conservation). Before
convergence, kick capacity = 2*floor(lam*b) + 1 >= 3 > 2 >= items, so ALL
items can be evacuated to parent.

This change will affect `concreteSplit_hkick` (kick bound) at leaf levels.
The bound `2*lam*cap + 1` still holds because leaf bags have at most 2 items
and `cap >= 2` at leaf level (since `cap(maxLevel) = n*nu^t * A^maxLevel`
which starts large before convergence).

#### C. Derive even-size from strengthened invariant

With item conservation + subtree uniformity:
1. When `cap(l) < A`: `cap(0) = n*nu^t < A^(l+1)`, so bags at levels
   `0..l` have cap < 1 and are empty.
2. Total items in each subtree at level `l+1` is `n / 2^(l+1)`, which
   equals `2^(k-l-1)` (even since n=2^k and k-l-1 >= 1 because l < maxLevel).
3. By subtree uniformity, left and right sub-subtrees have equal size,
   so each bag's size = subtree_total - left_child_total - right_child_total
   is even.

Key reference: Seiferas Section 5 (p.4).

#### D. Adjust `hkick` bound for leaf levels

At leaf levels, sending all items to parent instead of just fringe items
changes the kick count. But leaf bags have at most 2 items (from subtree
uniformity + n=2^k), so the kick count is at most 2, which is still
<= 2*lam*cap + 1 as long as cap >= 1 at that level.

**Impact on downstream:**
- `concreteSplit_maintains_invariant` (SplitProof.lean): needs the new
  `items_partition` clause proved for `rebag(concreteSplit(...))`. This
  requires showing the split is a partition (all items in exactly one of
  toParent/toLeftChild/toRightChild).
- `initialInvariant` (Invariant.lean): needs to prove `items_partition`
  for the initial bag assignment.
- `capacity_maintained` (Invariant.lean): unaffected -- the two-case proof
  structure is correct and `hkick_pair` is already proved.

**Difficulty:** MEDIUM-HARD. The fix is well-understood mathematically but
touches several files and requires reproving item conservation through
`rebag`.

**Estimate:** 2-3 weeks.

### S2: `concreteSplit_fromParent_filtered` (SplitStranger.lean)

**Statement:** Among items sent from parent to child (`fromParent`), the
j-stranger count at the parent level is at most `eps` times the full parent
bag's j-stranger count.

**Confidence: 90%.** The statement is almost certainly correct.

**Key insight (from Rust validation):** LHS = 0 in ALL tested cases (max
ratio 0.0000). This means for the concrete split, ALL parent-level
strangers are captured by the fringe. The bound `eps * strangerCount` is
very loose -- the true bound is 0.

**Why LHS = 0:** j-strangers (j >= 1) at level `l` have `perm` values
outside their native bag's interval at level `l`. This means their `perm`
value is extreme relative to the bag. Since `rankInBag` orders items by
`perm` value, j-strangers get extreme `rankInBag` values (near 0 or near
b-1). The fringe captures the extreme-ranked positions (rank < f or
rank >= f+2h), so all j-strangers end up in `toParent`, never in
`toLeftChild`/`toRightChild`.

**Proof strategy:**
1. Use `isJStranger_perm_bound` to get: j-stranger => `perm` value outside
   native interval at level `l`
2. Use `rankInBag_lt_count_below` / `rankInBag_ge_count_below` to convert:
   extreme `perm` value => extreme `rankInBag`
3. Show: extreme `rankInBag` => captured by fringe (rank < f or rank >= f+2h)
4. Conclude: j-strangers in `fromParent` = 0

The argument is multi-step but each step is well-defined. The main risk is
step 2 (connecting perm-value bounds to rank bounds) which requires counting
how many bag items have `perm` below/above a threshold.

**Files touched:** `SplitStranger.lean` (proof body at line ~253), possibly
`Split.lean` (new rank-perm lemmas).

**Independent of S1.** Does not need item conservation or leaf-level fixes.

**Estimate:** 2-4 weeks.

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
S1 (fix invariant + leaf split) ----+
S2 (fromParent_filtered) ----------+--> S4 (assembly + convergence->sorted)
S3 (cnative_bound) ----------------+
```

S1, S2, and S3 are **fully independent** of each other:
- S1 (even sizes) is invariant strengthening + concreteSplit leaf fix
- S2 (eps-filtering) is rank-based combinatorics using `rankInBag` + `perm` bounds
- S3 (sibling-native) is separator-error analysis using `nativeBagIdx` + `rankInBag`

### Recommended: 3 Parallel Instances

| Instance | Task | Files touched | Key references |
|----------|------|---------------|----------------|
| **I1** | S1: Fix invariant + leaf split + prove `bags_even_at_small_cap` | `Invariant.lean`, `Split.lean`, `SplitCard.lean`, `SplitProof.lean` | Seiferas Sections 2-5 |
| **I2** | S2: Prove `concreteSplit_fromParent_filtered` | `SplitStranger.lean`, possibly `Split.lean` | Seiferas Section 5, stranger definitions |
| **I3** | S3: Prove `concreteSplit_cnative_bound` | `SplitStranger.lean`, possibly `Split.lean` | Seiferas Section 5, separator guarantee |

**Conflict risks:**
- I2 and I3 both touch `SplitStranger.lean` but at non-overlapping sorry
  locations (line ~253 vs line ~270) -- trivial merge
- I1 changes `Invariant.lean` (add clause) and `Split.lean` (fix leaf case).
  I2/I3 may add helper lemmas to `Split.lean`. Coordinate by having I2/I3
  add helpers at the END of `Split.lean`, while I1's changes are to the
  `concreteSplit` definition near the top.
- I1 changes `SplitProof.lean` to prove the new `items_partition` clause.
  I2/I3 don't touch this file.

### Instance I1: Detailed Plan

**Goal:** Make `bags_even_at_small_cap` provable and prove it.

**Step 1:** Add `items_partition` clause to `SeifInvariant` in `Invariant.lean`.
Choose representation carefully:
- Option A: `Finset.univ = biUnion of all bags` (global partition)
- Option B: `forall level, sum over idx of (bags level idx).card = n`
  (per-level total)
- Option C: Per-subtree total tracking (Seiferas's Clause 2)

Option B is simplest and sufficient for even-size. Option C is more powerful
but harder. Recommend starting with Option B.

**Step 2:** Fix `concreteSplit` in `Split.lean`:
- At leaf levels, `toParent = regs` (all items)
- This ensures no items are lost

**Step 3:** Prove `items_partition` is maintained by `rebag(concreteSplit(...))`:
- The split must partition each bag: `toParent ∪ toLeftChild ∪ toRightChild = bag`
  and pairwise disjoint (already have `hsplit_sub` and can add `hsplit_cover`)
- Rebag reassembles from children's toParent + parent's fromParent
- Need: `sum of new bags at level l = sum of old bags at level l`

**Step 4:** Prove `initialInvariant` satisfies `items_partition`.

**Step 5:** Prove `bags_even_at_small_cap`:
- From `items_partition`: total items at level `l+1` = n
- From `uniform_size`: all bags at `l+1` have equal size, so each has n/2^(l+1)
- When cap(l) < A: ancestors empty, so subtree items = n/2^(l+1) = 2^(k-l-1)
- Since k-l-1 >= 1 (l < maxLevel), this is even

### Instance I2: Detailed Plan

**Goal:** Prove `concreteSplit_fromParent_filtered`.

**Strategy (prove LHS = 0):**

**Step 1:** Prove rank-perm ordering lemma: for items in a bag, if item `x`
has `perm x < perm y` then `rankInBag perm bag x <= rankInBag perm bag y`.
This should follow from `rankInBag` being defined as the count of items with
smaller `perm` value.

**Step 2:** Prove j-stranger -> extreme rank: if `isJStranger n perm x l i j`
(j >= 1), then either:
- `perm x < nativeIntervalLo n l i` => `rankInBag perm bag x < count_below`
  => rank is small (near 0)
- `perm x >= nativeIntervalHi n l i` => `rankInBag perm bag x >= count_above`
  => rank is large (near b)

**Step 3:** Prove extreme rank -> fringe: if rank < f or rank >= f+2h, then
item is in `toParent` (fringe), not in `toLeftChild`/`toRightChild`.

**Step 4:** Combine: j-strangers from parent bag are in `toParent`, so
j-strangers in `fromParent` (= toLeftChild or toRightChild) = 0.

**Step 5:** Conclude: `jStrangerCount ... fromParent ... <= eps * jStrangerCount`
since LHS = 0.

**Key definitions to understand:**
- `rankInBag` (Split.lean): `(regs.filter (fun j => perm j < perm i)).card`
- `isJStranger` (Defs.lean): `nativeBagIdx n perm r level idx != idx'`
  where `idx'` is the j-ancestor's index
- `fringeSize` (Split.lean): `floor(lam * b)`
- `fromParent` in rebag: items sent to child from parent's split

### Instance I3: Detailed Plan

**Goal:** Prove `concreteSplit_cnative_bound`.

**Strategy (bound halving error):**

**Step 1:** Understand `siblingNativeCount` definition in `Defs.lean`:
items that are 1-strangers at level `l+1` but native to level `l` (parent).
These are items assigned to the wrong child by the split.

**Step 2:** Prove: sibling-native items have `perm` values near the
`bagSize/2` boundary. Their `nativeBagIdx` at level `l+1` differs from
their rank-based child assignment (threshold at `f + h`).

**Step 3:** Count: the number of items near the boundary is bounded by
the separator's epsilon error. Specifically, items where rank-based
assignment disagrees with native assignment are bounded by `eps * b / 2`.

**Step 4:** Show the `cnativeCoeff` bound absorbs the halving error:
`eps * b / 2 <= cnativeCoeff * cap(parent)`.

**Shared infrastructure with I2:** Both need rank-perm ordering lemmas
from `Split.lean`. If I2 and I3 run in parallel, coordinate so that shared
helpers go in `Split.lean` (avoid conflicts in `SplitStranger.lean`).

## Other Sorries (Outside Bags Subsystem)

The full project has 14 sorries total. The Bags subsystem accounts for 4
(S1-S4 above). The remainder:

| Area | Count | Key theorems |
|------|-------|-------------|
| `Graph/Quotient.lean` | 1 | `spectralGap_quotient` (Cauchy interlacing) |
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
