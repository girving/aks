> **OBSOLETE:** References stale file names (TreeSort.lean, SplitStranger.lean) from before Bags/ restructuring. See `docs/bags.md` for current status.

# Seiferas Path: Remaining Work and Parallelism Plan

## Current Status (2026-02-25)

**Total sorries: 5** (all in `AKS/Bags/`). All sorries outside the Bags
subsystem have been resolved. The full pipeline from base expander through
zig-zag families, contracted expanders, halver families, separator families,
and top-level assembly is sorry-free. Only the bag-tree correctness proofs remain.

**Recent milestones:**
- `actualModel_invariant` image preservation PROVED (2026-02-25): via
  `exec_foldl_image_eq_partitioned` + `separatorStage_comparators_partitioned`
- `hcnative` sorry factored to `siblingNativeCount_mixed_le` (2026-02-25):
  well-specified sorry in new `SeparatorBridge.lean`
- `hfilter` cases 1-2 PROVED (2026-02-25): subset monotonicity + empty set
- `scatterEmbed_exec_inside/outside` PROVED (2026-02-25): scatter-embedded
  networks act on local views within wire range
- B6 wire maps FULLY RESOLVED (2026-02-24): `wireMapSeq`, `wireMapSeq_disjoint`,
  `wireMapSeq_covers`, `wireMapSeq_range` all proved via partition-based construction
- `actualModel_invariant` multiset preservation PROVED (2026-02-24)
- B3 (`benchmark_analytic_bound`) PROVED (2026-02-22) via 9th invariant clause
- B4a (`separatorStage_depth_le`) PROVED via `depth_flatMap_le`

### Sorry Summary

| # | File | Theorem | Risk | Estimate |
|---|------|---------|------|----------|
| AM1 | `TreeSort.lean:493` | `hfilter` case 3 (SepInitial bound) | MEDIUM | 2-3 weeks |
| AM2 | `SeparatorBridge.lean:216` | `siblingNativeCount_mixed_le` | MED-HIGH | 2-3 weeks |
| AM3 | `TreeSort.lean:528` | `hrebag_deviation` (mixed-perm) | MEDIUM | 2-3 weeks |
| B5 | `SplitStranger.lean:1553` | `native_imbalance_bound` | MEDIUM | 2-3 weeks |
| B4b | `TreeSort.lean:617` | `separatorSortingNetwork_sorts` | MED-HIGH | 1-2 weeks (after AM1-3+B5) |

### Dependency Structure

```
(B5) native_imbalance_bound ──────────────────────────┐
(AM2) siblingNativeCount_mixed_le ──┐                  │
(AM1) hfilter case 3 ──────────────┼──→ actualModel_invariant
(AM3) hrebag_deviation ────────────┘          │
                                              ↓
                                (B4b) separatorSortingNetwork_sorts
```

AM1–AM3 are the three mixed-perm obstacles in `actualModel_invariant`.
B5 is a standalone analytic bound. B4b is the final assembly.

**Risk rationale:**
- **AM1** (`hfilter` case 3): Non-empty `fromParent` with parent j-strangers.
  Needs: restrict `π_next` to parent bag → build local `Equiv.Perm (Fin m)` →
  apply `IsSeparator` (`SepInitial` with γ ≤ lam) → bound displaced strangers
  by `ε_sep · s_total ≤ eps · s_total`. Requires `hγ_le` and `hε_le` hypotheses.
  Empirically: ratio = 0.0000.
- **AM2** (`siblingNativeCount_mixed_le`): Mixed-perm sibling-native bound.
  The existing `concreteSplit_cnative_bound` handles matched perms (split and
  count by same perm). The mixed case (split by `id`, count by `π_next`)
  needs the separator property to bridge positions and values.
  Empirically: ratio ≤ 0.1442.
- **AM3** (`hrebag_deviation`): Deviation bound for rebag with mixed perms.
  Same 4-way partition structure as `concreteSplit_rebag_deviation` but with
  `id`-based split and `π_next`-based counting.
- **B5** (`native_imbalance_bound`): Combined 4-way bound on deviation after
  rebag. Three-source decomposition (kickL + kickR + fromParent) with
  sibling-native cancellation. Empirically validated (18× margin).
  See detailed strategy below.
- **B4b** (`separatorSortingNetwork_sorts`): Final assembly. Once AM1-3+B5
  are done, chains `actualModel_converges` → zero strangers → monotone.

### What's Proved

**Invariant infrastructure:**
- `invariant_maintained` — abstract invariant maintenance (0 sorry)
- `concreteSplit_maintains_invariant` — concrete assembly (delegates to sorry'd sub-lemmas)
- `kick_stranger_bound` — fringe strangers at parent level
- `parent_stranger_bound` — parent strangers for j ≥ 2
- `parent_1stranger_from_inv` — parent 1-strangers (abstract)
- `concreteSplit_hrebag_uniform` — uniform rebag sizes
- `concreteSplit_hrebag_disjoint` — disjoint rebag bags
- `concreteSplit_fromParent_filtered` — ε-filtering (LHS = 0, fully proved)
- `rebag_covers` — item conservation through rebag
- `concreteSplit_cnative_bound` — matched-perm sibling-native bound (chains A + B)
- `siblingNative_le_deviation` — Sub-lemma A (rank structure)
- `below_boundary_deviation` — Sub-lemma B (deviation bound via `inv.deviation_bound`)

**Actual model bridge (`actualModel_invariant`):**
- Image preservation — PROVED via `exec_foldl_image_eq_partitioned` +
  `separatorStage_comparators_partitioned` (SeparatorBridge.lean)
- `SeifInvariant.perm_rearrange` — invariant transfer across perm changes
- `hfilter` cases 1-2 — proved via subset monotonicity / empty set
- `hcnative` — factored to `siblingNativeCount_mixed_le` (SeparatorBridge.lean)

**Scatter embedding:**
- `scatterEmbed_exec_inside` — local view theorem for scatter embeddings
- `scatterEmbed_exec_outside` — positions outside range unchanged
- `scatterEmbed_exec_image_eq` — image preservation on wire positions

**Wire maps (B6 — FULLY RESOLVED):**
- `wireMapSeq` — computable wire map sequence from partition-based construction
- `wireMapSeq_disjoint` — disjoint wire map images
- `wireMapSeq_covers` — every register in some wire map image
- `wireMapSeq_range` — wire map range = bag set
- `ipsBagSize_eq_card` — IPS determinism (actual sizes match recurrence)

**Network structure:**
- `separatorStage_depth_le` — per-stage depth ≤ d_sep (via scatter embedding)
- `separatorSortingNetwork_depth_le` — total depth ≤ numStages * d_sep
- `separatorSortingNetwork_depth_bound` — O(log n) depth bound
- `separatorSortingNetwork_converges` — convergence: all bags have 0 strangers

## Architecture

```
Split.lean              -- concreteSplit definition, rankInBag, fringeSize, childSendSize
     |          |
SplitCard.lean   SplitStranger.lean  -- cardinality bounds / stranger bounds
     |          |
SplitProof.lean                     -- concreteSplit_maintains_invariant (assembly)
     |
Stage.lean                          -- separatorStage, wireMapSeq (IPS construction)
     |
SeparatorBridge.lean                -- mixed-perm bridge (siblingNativeCount_mixed_le)
     |
TreeSort.lean                       -- actualModel_invariant, separatorSortingNetwork_sorts
     |
Seiferas.lean                       -- seiferas_sorting_networks_exist
```

## Dependency Graph of Remaining Sorries

```
AM1 (hfilter case 3) ────────────┐
     TreeSort.lean                │
                                  │
AM2 (siblingNativeCount_mixed_le)┼──→ actualModel_invariant ──→ B4b (sorts)
     SeparatorBridge.lean         │                                TreeSort.lean
                                  │
AM3 (hrebag_deviation) ──────────┘
     TreeSort.lean

B5 (native_imbalance_bound) ──────────────────────────────────→ B4b (sorts)
     SplitStranger.lean (independent of AM1-3)
```

**Parallelism:** AM1, AM2, AM3, and B5 are all independent — all four can be
worked in parallel. B4b (final assembly) becomes tractable once all four are done.

## Proof Plan for `AKS/Bags/`

### B3: `benchmark_analytic_bound` — COMPLETED

**Status:** DONE (2026-02-22).

**What was proved:** `benchmark_analytic_bound` — the signed bound
`|(s_lo-s_hi)+(out_R-out_L)+b%2| ≤ 2·cnativeCoeff·cap(parent)`. Uses 9th
invariant clause `inv.deviation_bound` on the parent bag, then the identity
`2(C - ⌊b/2⌋) = signed sum`. All of `below_boundary_deviation` now proved.

**Trade-off:** Added clause 9 (`deviation_bound`) to `SeifInvariant`. This
creates the `hrebag_deviation` sorry (B5): maintaining deviation through rebag.
The signed-bound approach avoids the original multi-level geometric series
plan (which would have required deriving deviation from stranger bounds).
Empirical testing confirmed local derivation is impossible (native imbalance
can be 26× stranger count), so the inductive maintenance approach is correct.

### B2: Item Conservation + Leaf Fix — RESOLVED

**Status:** DONE. The `hrebag_small_cap_even` sorry and leaf kick bounds have
been resolved. `items_partition` and `root_even` clauses added to `SeifInvariant`.
Leaf handling fixed in `concreteSplit`.

### AM1–AM3: `actualModel_invariant` Bridge (Mixed-Perm Obstacles)

**Files:** `TreeSort.lean` (AM1, AM3), `SeparatorBridge.lean` (AM2)

**Status:** 3 sorries remain. Image preservation and multiset preservation proved.
`hfilter` cases 1-2 proved. `hcnative` factored to `siblingNativeCount_mixed_le`.

**Context:** `actualModel_invariant` bridges the abstract bag model (where `perm = id`
and split/count use the same perm) to the actual model (where `perm = π_next` from
separator execution and split uses `id`). This "mixed-perm" setting causes three
obstacles where existing matched-perm proofs cannot be directly applied.

**What's proved:**
- Image preservation: separator stage preserves value multiset per bag
  (`exec_foldl_image_eq_partitioned` + `separatorStage_comparators_partitioned`)
- `SeifInvariant.perm_rearrange`: transfers invariant from `π_t'` to `π_next`
- `hfilter` cases 1-2: subset monotonicity (parent has 0 strangers) and empty set
- `hcnative` wiring: `siblingNativeCount_mixed_le` call replaces sorry

**AM1 (`hfilter` case 3):** Non-empty `fromParent` with parent j-strangers.
Needs local perm extraction from `π_next` restricted to parent bag, then apply
`IsSeparator` with `SepInitial` using `γ ≤ lam` (from `hγ_le`) to bound displaced
strangers by `ε_sep · s_total ≤ eps · s_total`. Empirically: ratio = 0.0000.

**AM2 (`siblingNativeCount_mixed_le`):** The matched-perm `concreteSplit_cnative_bound`
chains `siblingNative_le_deviation` (sibNat ≤ |C - b/2|) with `below_boundary_deviation`
(|C - b/2| ≤ cnativeCoeff·cap). The mixed-perm case needs the separator property to
bridge id-based positions and π_next-based values. The key difficulty is that the
ε·m/2 approximation error from the separator can exceed cnativeCoeff·cap when
m > cap (which happens at early stages). The proof likely needs the IPS recurrence
to bound m/cap or a more sophisticated decomposition. Empirically: ratio ≤ 0.1442.

**AM3 (`hrebag_deviation`):** Same 4-way partition structure as
`concreteSplit_rebag_deviation` but with `id`-based split and `π_next`-based counting.
The existing proof infrastructure handles the partition decomposition; the mixed-perm
aspect requires showing the deviation bound transfers correctly.

### B4a: Stage Depth + Statement Fixes — COMPLETED

**Status:** DONE (2026-02-22).

**Files touched:** `Stage.lean`, `TreeSort.lean`, `Seiferas.lean`

**Completed:**
1. **`separatorStage_depth_le`** (B4a): PROVED. Bound is `(maxLevel n + 1) * d_sep`
   (sequential levels via `depth_flatMap_le`). The original claim of `d_sep` per stage
   was FALSE — levels have overlapping wire ranges. Achieving O(1) depth per stage
   requires wire-disjoint embedding (Seiferas Section 3).
2. **`hstages` fix**: Replaced `hstages : True` with real convergence bound
   `hconv : converged n A ν numStages` + parameter constraints `hparams`.
3. **`n = 2^k` guard**: Added `hn : ∃ k, n = 2 ^ k` hypothesis.
4. **Cascading bound updates**: Size/depth bounds now O(n log n)/O(log n) throughout
   pipeline (via parametric `WireMap` fix in B6).

### B5: `concreteSplit_rebag_deviation` (deviation maintenance through rebag)

**Files touched:** `SplitStranger.lean`, `SplitCard.lean`, `SplitProof.lean` (line 82)

**Status:** Factored into three layers. Single sorry remains at
`rebag_native_imbalance_bound` (line 1444 of `SplitStranger.lean`).

**Current proof structure (three layers):**
1. `concreteSplit_rebag_deviation` — outer proof (PROVED): 4-way partition by perm
   value, exact identity `2(C-⌊b/2⌋) = (s_lo-s_hi) + (n_L-n_R) + b%2`, delegates
   to `rebag_analytic_bound` for the combined bound
2. `rebag_analytic_bound` — combined 4-way bound (PROVED, 0 own sorry): triangle
   inequality decomposition into stranger bound + native imbalance bound.
   Edge cases (level=0, level>k) handled via `rebag_empty_level0`/`rebag_empty_beyond_k`.
3. `rebag_native_imbalance_bound` — native imbalance bound (1 sorry): proves
   `|n_L - n_R| + b%2 ≤ (2·cnativeCoeff - lam) · cap(t+1, level)`

**Proved infrastructure (all in `SplitStranger.lean`):**
- `rebag_stranger_bound` (line 1369): 1-stranger count on rebag bag ≤ lam·cap(t+1)
  (proved via `stranger_bound_maintained_eq1` + `kick_stranger_bound` + `concreteSplit_parent_1stranger`)
- `slo_shi_eq_strangerCount_self` (line 1333): s_lo + s_hi = jStrangerCount at (level, idx)
- `rebag_empty_level0` / `rebag_empty_beyond_k`: degenerate cases (B = ∅)
- `kick_stranger_bound` (line 71): toParent strangers at parent level ≤ lam·ε^j·cap(t, child_level)
- `siblingNative_le_deviation` (line 1022): sibling-native count of fromParent ≤ |C - ⌊b/2⌋| of parent
- `concreteSplit_cnative_bound` (line 1210): chains the above → siblingNativeCount ≤ cnativeCoeff·cap(parent)
- `below_boundary_deviation` (line 802): deviation bound on parent bag (proved via `inv.deviation_bound`)
- `benchmark_analytic_bound` (line 669): 4-way bound on existing bags (proved via `inv.deviation_bound`)

**What remains:** Prove `rebag_native_imbalance_bound`.

#### Proof strategy for `rebag_analytic_bound`

**Recommended approach: Three-source decomposition with 2C-b identity.**

The rebag bag B = kickL ∪ kickR ∪ fp (three disjoint sources from
`rebag_sources_disjoint`). Filter distributes over disjoint union
(`Finset.filter_union` + `Finset.card_union_of_disjoint`), giving:
```
2C - b = (2·C_kL - b_kL) + (2·C_kR - b_kR) + (2·C_fp - b_fp)
```
where C_src = items in source with perm < boundary, b_src = source card.
Then `signed_sum = 2C - b + b%2`, so:
```
|signed_sum| ≤ |2·C_kL - b_kL| + |2·C_kR - b_kR| + |2·C_fp - b_fp| + 1
```
by triangle inequality (`Int.natAbs_add_le`).

**Sub-bound 1: Kick terms.** For kickL from child (level+1, 2·idx):
- boundary = (2·idx+1)·bagSize(level+1) = upper edge of left child's native interval
- So ALL child-native items in kickL have perm < boundary → contribute to C_kL
- Items in kickL with perm ≥ boundary are: sibling-native items (perm in right
  child's range) + far-strangers at parent level (perm outside [lo, hi))
- Therefore: `b_kL - C_kL = sibling_native_right(kL) + far_strangers_above(kL)`

For kickR from child (level+1, 2·idx+1):
- boundary = lower edge of right child's native interval
- So ALL child-native items in kickR have perm ≥ boundary → DON'T contribute to C_kR
- Items in kickR with perm < boundary are: sibling-native items + far-strangers below
- Therefore: `C_kR = sibling_native_left(kR) + far_strangers_below(kR)`

Combined kick deviation with uniform kicks (b_kL = b_kR):
```
(2·C_kL - b_kL) + (2·C_kR - b_kR)
  = (b_kL - 2·(sib_R_kL + far_above_kL)) + (2·(sib_L_kR + far_below_kR) - b_kR)
  = 2·(sib_L_kR - sib_R_kL) + 2·(far_below_kR - far_above_kL)    [when b_kL = b_kR]
```

**Key cancellation:** In the "typical" case (fringe size f < C_below_bdy of child < b_child - f),
the sibling-native items in each kick are EXACTLY f (fringe size):
- sib_R_kL = f (left child's HIGH-fringe items are all in sibling range)
- sib_L_kR = f (right child's LOW-fringe items are all in sibling range)
So `sib_L_kR - sib_R_kL = 0` (perfect cancellation).

The residual `far_below_kR - far_above_kL` involves only 2+-strangers at the
parent level, bounded by `kick_stranger_bound` at j=1 applied at parent level:
```
|far_below_kR - far_above_kL| ≤ far_below_kR + far_above_kL
  ≤ jStrangerCount(kickR, level, idx, 1) + jStrangerCount(kickL, level, idx, 1)
  ≤ 2·lam·ε·cap(t, level+1)
  = 2·lam·ε·(A/ν)·cap(t+1, level)
  ≈ 2·0.01·0.01·15.4·cap ≈ 0.003·cap
```

**Sub-bound 2: fromParent term.** Items from parent split (rank range [f, f+h) or
[f+h, f+2h) of parent bag). The deviation `|2·C_fp - b_fp|` is bounded by the
parent's deviation plus stranger perturbation:
- `siblingNative_le_deviation` gives: sibling-native count of fp ≤ |C_parent - b_parent/2|
- `below_boundary_deviation` gives: |C_parent - b_parent/2| ≤ cnativeCoeff·cap(t, level-1)
- Cross-level scaling: cap(t, level-1) = cap(t+1, level)/(Aν) ≈ 0.154·cap(t+1, level)

The fp deviation decomposes as:
```
2·C_fp - b_fp = 2·(native_left_fp - native_right_fp) + 2·(str_below_fp - str_above_fp)
```
where the native imbalance is bounded by the sibling-native count (≈ parent deviation),
and the stranger imbalance is bounded by the 1-stranger count of fp.

Combined: `|2·C_fp - b_fp| ≤ 2·cnativeCoeff·cap(t,level-1) + lam·cap(t,level-1)`
  `≈ (2·0.027 + 0.01)·0.154·cap(t+1) ≈ 0.010·cap(t+1)`

**Total budget check:**
- Kick terms: ≤ ~0.006·cap(t+1) [when sibling-native cancels]
- fp term: ≤ ~0.010·cap(t+1)
- b%2 term: ≤ 1
- Sum: ~0.016·cap(t+1) + 1 ≤ 2·cnativeCoeff·cap(t+1) ≈ 0.054·cap(t+1) ✓

**Empirical validation:** `rust/test-deviation-maintenance.rs` shows
max deviation ratio ≈ 0.056 (18× safety margin). `rust/test-rebag-deviation-decomp.rs`
shows fromParent dev / cap ≤ 0.0036, kick dev / cap ≤ 0.0036.

#### Implementation plan for `rebag_native_imbalance_bound`

**Step 1: Factor into sorry'd sub-lemmas. — DONE (2026-02-23)**
Factored via triangle inequality (stranger + native imbalance), not three-source:
- `rebag_analytic_bound` PROVED: assembly via `|A+B| ≤ |A| + |B|`
  - Stranger bound: `s_lo + s_hi ≤ lam·cap` via `rebag_stranger_bound` ✓
  - Edge cases: `rebag_empty_level0`, `rebag_empty_beyond_k` ✓
- `rebag_native_imbalance_bound` (1 sorry): `|n_L - n_R| + b%2 ≤ (2·cnativeCoeff - lam)·cap`

The three-source decomposition (kickL + kickR + fromParent) is now the strategy
for proving `rebag_native_imbalance_bound`. The sub-lemmas needed:
- `kick_deviation_bound`: `|2·C_kL - b_kL + 2·C_kR - b_kR| ≤ K₁·cap(t+1,level)`
  using sibling-native cancellation + `kick_stranger_bound`
- `fp_deviation_bound`: `|2·C_fp - b_fp| ≤ K₂·cap(t+1,level)`
  using `siblingNative_le_deviation` + `below_boundary_deviation`

**Step 2: Prove kick_deviation_bound.**
Core technique: show `b_kL - C_kL = sib_R(kL) + str_above(kL)` and
`C_kR = sib_L(kR) + str_below(kR)`, then use `sib_L(kR) = sib_R(kL)` (by
symmetry of the construction at uniform-sized children) + triangle inequality
on the far-stranger terms.

The sibling-native cancellation requires formalizing:
- In the "typical" case: all low-fringe items of the left child are child-native
  (below boundary), all high-fringe items are sibling-native (above boundary)
  → sib_R(kL) = f. Similarly sib_L(kR) = f.
- The "typical" condition (f < C_child < b_child - f) follows from the child's
  deviation bound: |C_child - b_child/2| ≤ cnativeCoeff·cap(child) and
  f = ⌊lam·cap(child)⌋ with lam < cnativeCoeff (by parameter constraints).

**Step 3: Prove fp_deviation_bound.**
Use `siblingNative_le_deviation` (already proved) to bound the native imbalance,
and `kick_stranger_bound` (via level shift) for the stranger perturbation.

**Lean tools needed (all verified available):**
- `Finset.filter_union`: filter distributes over union
- `Finset.card_union_of_disjoint`: card distributes over disjoint union
- `Disjoint.mono (filter_subset p A) (filter_subset p B)`: filter preserves disjointness
- `Int.natAbs_add_le`: triangle inequality for integer absolute values
- `Nat.mul_add_div`: `⌊(2k+m)/2⌋ = k + ⌊m/2⌋`

#### Lessons learned

1. **The triangle inequality approach works, but requires sibling-native cancellation.**
   Individual kick stranger counts (LS, RS) are each ~0.15·cap — 6× too large for a
   naive `|LS - RS| ≤ LS + RS` bound. The cancellation `sib_L(kR) = sib_R(kL)` is
   essential and follows from the uniform-size property of the construction.

2. **The 2C - b decomposition is cleaner than the signed_sum decomposition.**
   Working with `2·C_src - b_src` for each source avoids the b%2 correction until
   the very end and composes linearly.

3. **Cross-level capacity scaling matters.** cap(t, level-1) / cap(t+1, level) = 1/(Aν) ≈ 0.154.
   The fp bound involves parent-level quantities that scale down by this factor.
   cap(t, level+1) / cap(t+1, level) = A/ν ≈ 15.4. The kick stranger bounds at the
   child level scale UP by this factor, which is why they seem large individually.

4. **Seiferas's benchmark distribution approach is a global tree argument.**
   It does NOT decompose into kick/fp. The formalization's local decomposition
   approach is viable but requires more lemmas than the paper suggests. If sub-bounds
   prove hard, consider the benchmark approach (requires tree induction + geometric
   series but matches the paper directly).

5. **The deviation bound is NOT monotone across rebag.** fromParent deviation can be
   13× the parent's deviation. The bound works because both are small fractions of
   cap(t+1), not because deviation decreases.

**Risk:** MEDIUM. Three-source decomposition is well-understood; sibling-native
cancellation is the main technical hurdle but follows from uniform sizes.

**Estimate:** 2-3 weeks (mostly in formalizing the three sub-bounds).

### B6: Wire Map Construction (IPS) — FULLY RESOLVED

**Status:** DONE (2026-02-24). All wire map sorries eliminated.

Partition-based construction: `wireMapSeq` uses `Finset.orderEmbOfFin` on actual
bags at each stage. `wireMapSeq_disjoint` from `bags_disjoint`, `wireMapSeq_covers`
from `items_partition`, `wireMapSeq_range` from `range_orderEmbOfFin`. The IPS
determinism theorem `ipsBagSize_eq_card` proves actual bag sizes match the
`ipsBagSize` recurrence, enabling the type cast.

`hwm_mem` hypothesis (wire positions ∈ bags) supplied by `wireMapSeq_mem` at
call sites in `Seiferas.lean`.

### B4b: Assembly (`separatorSortingNetwork_sorts`)

Once AM1-3+B5 are complete, `separatorSortingNetwork_sorts` (B4b) becomes the
final assembly step. It needs:
- `actualModel_invariant` (needs AM1-3 to be sorry-free)
- `actualModel_converges` (chains `actualModel_invariant` + `separatorSortingNetwork_converges`)
- Zero strangers → items native → partition preserved → monotone

**Proof sketch:**
1. `zero_one_principle` (proved) reduces to Boolean inputs
2. Decompose `v = g ∘ σ` where `g` monotone, `σ` a permutation
3. `exec_comp_mono` (proved): `net.exec (g ∘ σ) = g ∘ (net.exec σ)`
4. `actualModel_converges` gives zero strangers at all levels
5. Zero 1-strangers + `n = 2^k` → items native → output is monotone

**Estimate:** 1-2 weeks after AM1-3+B5.

### Remaining Sorries Summary

| Sorry | Files | Risk | Estimate | Parallel? |
|-------|-------|------|----------|-----------|
| AM1 (`hfilter` case 3) | `TreeSort` | MEDIUM | 2-3 weeks | Yes |
| AM2 (`siblingNativeCount_mixed_le`) | `SeparatorBridge` | MED-HIGH | 2-3 weeks | Yes |
| AM3 (`hrebag_deviation`) | `TreeSort` | MEDIUM | 2-3 weeks | Yes |
| B5 (`native_imbalance_bound`) | `SplitStranger` | MEDIUM | 2-3 weeks | Yes |
| B4b (sorts) | `TreeSort` (after AM1-3+B5) | MED-HIGH | 1-2 weeks | After AM1-3+B5 |

## B4 Deep Analysis (from Rust validation) — ALL FIXED

Rust tests revealed three statement/architecture bugs, **all now resolved**:
1. **`hstages : True`** → replaced with `hconv : converged n A ν numStages`
2. **Missing `n = 2^k`** → added `hn : ∃ k, n = 2 ^ k` hypothesis
3. **Stage structure mismatch** → `separatorStage` iterates all active levels

## Former Sorries (Outside Bags) — ALL RESOLVED

| Area | Former sorry | How resolved |
|------|-------------|-------------|
| `Graph/Contract.lean` | `spectralGap_contractDivisible_le` | Equal-fiber contraction preserves spectral gap |
| `Halver/FromExpander.lean` | `graph_exists_halver_depth_le` | König's edge coloring |
| `ZigZag/Expanders.lean` | `explicit_expanders_exist_zigzag` | Via contraction (Quotient.lean deleted) |
| `Seiferas.lean` | `wireMapSeq_exists` (×1), correctness (×2) | Sorry-free assembly; sorries moved to Bags |

**Total sorry: 5** (all in `AKS/Bags/`). The full pipeline from base expander
certificate through top-level theorem is sorry-free except for the five Bags
correctness proofs (3 in `actualModel_invariant`, 1 in `SplitStranger`, 1 final assembly).

## Key Seiferas Paper References

- **Section 2** (p.2): Item conservation ("always occupy one of n-1 bags"), n = 2^K
- **Section 3** (p.3): Leaf handling, odd excess to parent, "inductively predictable subsequences"
- **Section 4** (p.3): Clause (2) — subtree uniformity (stronger than our `uniform_size`)
- **Section 5** (p.4): Even-size when cap < A; the b < A capacity case
- **Section 5** (p.4-5): Stranger bound maintenance (ε-filtering, cnative)
- **Section 5** (p.5): Benchmark distribution comparison (for `below_boundary_deviation`)
- **Section 7** (p.8): Network depth per iteration = constant × halver depth
