# Seiferas Path: Plan for Resolving Remaining Sorries

## Status

The Seiferas path (expanders → halvers → separators → bag-tree sorting) has **2 remaining
sorries** in the Bags/Seiferas subsystem:

1. **`separatorSortingNetwork_sorts`** (TreeSort.lean:87) — the main correctness theorem
2. **`halverToSeparatorFamily'.isSep`** (Seiferas.lean:120) — separator family needs `2^t ∣ n`

Both block `seiferas_sorting_networks_exist`.

## Architecture Overview

```
SeparatorFamily.net : (n : ℕ) → ComparatorNetwork n
  ↓
separatorStage n sep stageIdx : ComparatorNetwork n     -- currently: comparators := []
  ↓
separatorSortingNetwork n sep numStages : ComparatorNetwork n
  ↓
separatorSortingNetwork_sorts : Monotone (net.exec v)   -- sorry
```

The core problem: `separatorStage` is a placeholder (`comparators := []`). To prove
`separatorSortingNetwork_sorts`, we need:
- A real `separatorStage` that applies the separator to each active bag
- A proof that each stage maintains `SeifInvariant`
- A proof that convergence (all bags ≤ 1 item) implies sorted output

## Part B Progress (Rust Exploration + Lean Formalization)

### Completed: Rust Validation (`rust/test-split-hypotheses.rs`)

All split hypotheses validated with Seiferas parameters (A=10, ν=0.65, λ=ε=1/99):

| Hypothesis | Max ratio | Status |
|---|---|---|
| `hkick_stranger` (lam·ε^j·cap) | 0.0000 | trivially holds |
| `hparent_1stranger` (parentStrangerCoeff·cap) | 0.1786 | 82% margin |
| `hcnative_bound` (cnativeCoeff·cap(parent)) | 0.1793 | 82% margin |
| `hkick_pair` (4λA·cap, no +2) | 0.9995 | holds |
| even-item property | 100% | always holds |
| parent-empty when cap < A | 100% | always holds |

### Completed: Two-Case Capacity Proof in Lean

**Key finding (Seiferas Section 5):** The original `capacity_maintained` theorem
required `hcap_ge : A ≤ n·ν^t`, which fails at early stages. The fix is a
two-case proof:
- **Case 1 (cap ≥ A):** Standard: `4λAb + 2 + b/(2A) ≤ νb` (uses C3)
- **Case 2 (cap < A):** Parent empty, children have even items, no +2:
  `4λAb ≤ νb` (uses C3 with slack)

**Changes to `Invariant.lean`:**
- Removed `hcap_ge` from both `capacity_maintained` and `invariant_maintained`
- Added `hkick_pair` parameter: paired kick bound when `cap < A`
- Derived `hfrom_parent_empty` internally: when `cap(l) < A`,
  `cap(l-1) = cap(l)/A < 1`, so parent bag has card 0, hence empty

## Work Packages

### Part A: Low-Risk (known-correct statements, clear proof paths)

#### WP-A1: Fix `halverToSeparatorFamily'.isSep` with power-of-2 restriction

**File:** `AKS/Seiferas.lean` (line 114–121)

**Problem:** `SeparatorFamily` requires `IsSeparator` for *all* `n`, but
`halverToSeparator_isSeparator` requires `2^t ∣ n`. For non-power-of-2 sizes,
the separator property doesn't hold.

**Solution:** Restrict the sorting network to power-of-2 sizes. This is standard:
pad any input to the next power of 2, sort, extract. The top-level theorem already
allows any `n ≥ 2` via the `C * n * log n` bound (padding at most doubles `n`).

**Approach:** Change `halverToSeparatorFamily'` to produce a
`SeparatorFamily` that works only at sizes divisible by `2^t`. Then modify
`seiferas_implies_sorting_network` to:
1. For input size `n`, round up to `n' = 2^⌈log₂ n⌉`
2. Build the sorting network at size `n'`
3. Embed the `n`-element input into `n'` wires (pad with ⊤)
4. Extract the first `n` outputs

The `halverToSeparator_isSeparator` theorem is already proved with the
`2^t ∣ n` hypothesis, so the only work is plumbing the divisibility through.

Alternatively (simpler): add a `(hdiv : 2^t ∣ n)` hypothesis to the top-level
theorem. Since the AKS construction naturally works with powers of 2, this is
mathematically clean. The O(n log n) bound absorbs the padding.

**Risk:** LOW. Pure plumbing — `halverToSeparator_isSeparator` is fully proved.

**Estimate:** ~50 lines changed across Seiferas.lean.

#### WP-A2: Implement `separatorStage` (real construction)

**File:** `AKS/Bags/Stage.lean`

**Problem:** `separatorStage` currently has `comparators := []`. It needs to
apply the separator to each active bag at stage `t`.

**Construction:** For each active bag `(level, idx)` at stage `t`:
- The bag covers a contiguous range of registers (by the partition invariant)
- Apply `sep.net bagSize` embedded via `shiftEmbed` at the bag's offset

The key insight (Seiferas Section 7): active bags have **disjoint register sets**
(from `SeifInvariant.bags_disjoint`), so all separators run in parallel.

**Approach:** Use `halverAtLevel` from `Nearsort/Construction.lean` as a model.
For each active level (where `(t + level) % 2 = 0`), iterate over bag indices
`0..<2^level`, compute offset = `idx * bagSize n level`, embed `sep.net bagSize`
at that offset. Concatenate across levels.

**Key infrastructure that already exists:**
- `shiftEmbed` (Sort/Defs.lean): embeds m-wire network at offset in n-wire network
- `halverAtLevel` (Nearsort/Construction.lean): model for iterating over sub-intervals
- `SeparatorFamily.net` returns `ComparatorNetwork n` for any `n`

**Complication:** `SeparatorFamily.net` takes an arbitrary `n`, but we need
it applied to `bagSize n level` (size of each bag at that level), then embedded
into the full `n`-wire network. This requires `bagSize n level ≤ n` and
alignment conditions.

For power-of-2 `n` with `level ≤ log₂ n`: `bagSize n level = n / 2^level` and
bags start at offsets `idx * (n / 2^level)`, each of size `n / 2^level`.

**Risk:** LOW-MEDIUM. The construction is clear; the main work is proving
the alignment conditions (`offset + bagSize ≤ n` for each bag) and that the
resulting depth is ≤ `d_sep` (from disjointness of active bags).

**Estimate:** ~100 lines.

#### WP-A3: Prove convergence → sorted

**File:** `AKS/Bags/TreeSort.lean`

**Problem:** `separatorSortingNetwork_sorts` needs: after enough stages,
all bags have ≤ 1 item → output is sorted.

**Approach:** After convergence, every bag has ≤ 1 item. The partition property
(items in bag `(level, idx)` have ranks in `[idx * bagSize, (idx+1) * bagSize)`)
plus each bag having ≤ 1 item means items are sorted.

More precisely: the 0-1 principle reduces to Boolean inputs. For Boolean `v`:
- Each bag has ≤ 1 item after convergence
- Items are partitioned correctly by the bag structure
- Since each bag's native interval covers `bagSize` positions, and there are
  `2^level` bags at each level, the partition at the leaf level has bags of
  size 1 → items are in sorted order

This requires connecting "zero strangers at convergence" to "sorted output."
The 0-stranger condition means every item is in its native bag, which for
single-item bags means every item is at its sorted position.

**Actually:** The proof uses the 0-1 principle (already in `TreeSort.lean`):
`zero_one_principle net (separatorSortingNetwork_sorts ...)`. So we need to
prove: for 0-1 inputs, after enough stages, the output is monotone.

The argument:
1. Start with `SeifInvariant` at t=0 (proved: `initialInvariant`)
2. Each stage maintains the invariant (proved: `invariant_maintained`, modulo
   the `split` hypotheses which come from the real separator)
3. After convergence, all bags have ≤ 1 item (proved: `separatorSortingNetwork_converges`)
4. Zero strangers (from stranger bound with capacity < 2) → items in native bags
5. Items in native single-item bags → sorted

Steps 1-3 are essentially done. Step 4-5 needs: the `perm` tracked by the
invariant corresponds to the actual execution of the comparator network.

**Risk:** MEDIUM. The main gap is connecting `SeifInvariant`'s abstract `perm`
and `bags` to the concrete execution of `separatorStage`. This requires proving
that executing `separatorStage` on a vector produces the same result as the
abstract rebagging operation.

**Estimate:** ~150 lines for the connection + ~50 lines for the final assembly.

### Part B: High-Risk (uncertain statements, need Rust exploration)

**STATUS: Rust exploration COMPLETE. All hypotheses validated. Key Lean change done.**

The `invariant_maintained` theorem no longer requires `hcap_ge`. The two-case
capacity proof (Seiferas Section 5) handles both cap ≥ A and cap < A cases.

#### WP-B1: Concrete `SplitResult` from separator execution

**Rust validation complete.** Split into position-based fringe (top λ and bottom λ
positions) + middle-left + middle-right. All cardinality and stranger bounds hold
with large margin.

**Remaining Lean work:** Define the concrete split operation and prove it satisfies
the hypotheses of `invariant_maintained`. This is engineering work (connecting
comparator network execution to the abstract split), not mathematical risk.

#### WP-B2: Stranger bounds on kicked items (`hkick_stranger`)

**Rust validation: trivially holds** (max ratio 0.0000). Kicked items are fringe
items, which are from the extremes of the separator output. These items are native
to the parent's ancestry (they're in the wrong child but right parent), so they
have 0 j-strangers at the parent level for all j ≥ 1.

**Remaining Lean work:** Formalize that fringe items (top/bottom λ positions of
separator output) have the same stranger status as the original bag items. Since
fringe items are a subset of the original bag, and the stranger count at the parent
level is bounded by ε times the bag capacity (from the invariant), this follows from
subset monotonicity + the existing `jStrangerCount_mono`.

#### WP-B3: Sibling-native bound (`hcnative_bound`)

**Rust validation complete.** Maximum empirical ratio: 0.179 (82% margin from bound).
Three sub-sources decompose cleanly:
- c1 (ε/2): halver misroutes — 18.3% of bound
- c2 (geometric series): stranger displacement — 77.1% of bound
- c3 (1/(8A²-2)): ancestor items — 4.5% of bound

**Remaining Lean work:** Prove the three-source decomposition. Each source is a
standard combinatorial argument about fringe selection + stranger counting.

#### WP-B4: Connecting abstract invariant to concrete execution

**Depends on:** WP-A2 (real separatorStage), WP-B1 (concrete split)

The bridge between abstract `SeifInvariant` and concrete network execution.
Given a vector `v` and the current invariant, executing `separatorStage` produces
output consistent with `rebag split` where `split` satisfies all hypotheses of
`invariant_maintained`.

**Risk:** MEDIUM (reduced from HIGH). The Rust validation confirms all individual
hypotheses hold. The remaining work is Lean formalization connecting:
1. Comparator network execution semantics
2. Position-based fringe selection = abstract toParent/toChild partition
3. Separator error guarantee → stranger bound on fringe items

## Dependency Graph

```
WP-A1 (fix isSep)          -- independent, do first
WP-A2 (implement stage)    -- independent, do first
   ↓
WP-B1 (concrete split)     -- needs WP-A2 (real separatorStage)
   ↓
WP-B2 (kick stranger)      -- needs WP-B1 (split definition)
WP-B3 (sibling-native)     -- needs WP-B1 (split definition)
   ↓
WP-B4 (abstract↔concrete)  -- needs WP-B1, WP-B2, WP-B3
   ↓
WP-A3 (convergence→sorted) -- needs WP-B4 (the full connection)
```

## Parallelization Strategy

**Instance 1 (low-risk):** WP-A1 + WP-A2
- Fix `halverToSeparatorFamily'.isSep` with power-of-2 approach
- Implement real `separatorStage` using `shiftEmbed` + `halverAtLevel` model

**Instance 2 (high-risk exploration):** WP-B1 + WP-B2 + WP-B3
- ~~Write Rust programs to validate the concrete split definition~~ **DONE**
- ~~Test stranger bounds with realistic separator implementations~~ **DONE**
- ~~Pin down exact partition rules and verify all hypotheses~~ **DONE**
- Remaining: formalize the validated results in Lean

## Parameter Reference (Seiferas Section 5)

For reference, the Seiferas parameters (approximate):
- A ≈ 10 (capacity growth per level)
- ν ≈ 0.65 (capacity decay per stage)
- λ ≈ 1/99 (fringe fraction)
- ε ≈ 1/99 (separator error)
- γ = 1/2 (separator split fraction, since we use 1-level halving)
- Convergence: ~7 · log₂(n) stages

Constraints (all proved to be satisfiable with these parameters):
- C3: ν ≥ 4λA + 5/(2A)
- C4 (j>1): 2Aε + 1/A ≤ ν
- C4 (j=1): 2λεA + parentStrangerCoeff ≤ λν

## Key Invariant Change (from Part B exploration)

The `capacity_maintained` and `invariant_maintained` theorems were updated:

**Removed:** `hcap_ge : A ≤ n·ν^t` — this failed at stages t ≥ 11 for n = 1024
(cap(0) drops below A before convergence), making the invariant impossible to maintain.

**Added:** `hkick_pair` — when `bagCapacity(l) < A`, the paired kick from both
children has no +2 additive term (because children have even item counts due to
divisibility of n = 2^k across uniform bag sizes).

**Derived internally:** `hfrom_parent_empty` — when `bagCapacity(l) < A`,
`bagCapacity(l-1) = bagCapacity(l)/A < 1`, so the parent bag has 0 items, hence
`fromParent` is empty. This eliminates the parent contribution in Case 2.
