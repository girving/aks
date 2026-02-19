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

#### WP-B1: Concrete `SplitResult` from separator execution

**Problem:** `invariant_maintained` requires a `split : ℕ → ℕ → SplitResult n`
satisfying many hypotheses (subset, cardinality, stranger bounds). We need to
prove that the *actual* separator execution produces a split satisfying these.

**What the separator does:** When applied to a bag at `(level, idx)`:
- The separator is a `(γ, ε)`-separator with `γ = 1/2^t` for some `t`
- It approximately γ-separates the items: the bottom `⌊γ · size⌋` outputs
  have rank ≤ γ · n + ε · size (approximately)
- For γ = 1/2: items are approximately halved

**The split:** After applying the separator to bag B at `(level, idx)`:
- **toParent** (fringe): items in the top `λ` and bottom `λ` fractions of the
  bag's output. These are the "fringes" that get kicked up.
- **toLeftChild**: items in the middle-left portion (ranks below median)
- **toRightChild**: items in the middle-right portion (ranks above median)

The exact fringe fraction `λ` is a parameter. Seiferas uses `λ ≈ 1/99`.

**What needs Rust exploration:**
- Verify the exact partition rule (which positions go to parent vs children)
- Verify that `hkick` (fringe ≤ `2λ · cap + 1`) holds
- Verify that `hsend_left/right` (each child gets ≤ `cap/2`) holds
- Verify that `hkick_stranger` (stranger bound on kicked items) holds

**Risk:** MEDIUM-HIGH. The partition rule affects all downstream proofs.
Getting it wrong would require restructuring `SplitResult` and `rebag`.

#### WP-B2: Stranger bounds on kicked items (`hkick_stranger`)

**Problem:** `invariant_maintained` requires that j-strangers among items kicked
from bag `(l, i)` to parent `(l-1, i/2)` satisfy:
```
jStrangerCount n perm (split l i).toParent (l-1) (i/2) j ≤ lam * ε^j * bagCapacity(l)
```

**Analysis:** Items kicked to parent are the fringe items. A j-stranger among
the fringe at the parent level `(l-1, i/2)` must have `nativeBagIdx(l-1-j+1, rank) ≠ (i/2)/2^(j-1)`.

The key insight: most kicked items are native to the parent's ancestry
(they're just in the wrong child). The ε factor comes from the separator's
error rate — only ε-fraction of items are misplaced across the separation
boundary, and those are the ones that could be strangers at the parent level.

**What needs Rust exploration:**
- Is the `lam * ε^j` bound tight? Or should it be `lam * ε^(j-1)` at parent level?
- How does the fringe selection interact with stranger counting?
- Does the bound hold for both children simultaneously?

**Risk:** MEDIUM. The bound follows from combining the separator's ε-error
guarantee with the fringe selection rule, but the exact interaction is subtle.

#### WP-B3: Sibling-native bound (`hcnative_bound`)

**Problem:** `parent_1stranger_bound` (now proved) requires as hypothesis:
```
siblingNativeCount n perm (fromParent split level idx) level idx ≤
  cnativeCoeff A lam ε * bagCapacity(level - 1)
```
where `cnativeCoeff = ε/2 + 2λεA²/(1-(2εA)²) + 1/(8A²-2)`.

**Already validated by Rust** (`/tmp/test-parent-bound.rs`):
- Maximum empirical ratio: 0.183 (with 81.7% margin from bound)
- Holds across all separator types (perfect, ε-halver, adversarial)
- Three sub-sources decompose cleanly:
  - c1 (ε/2): halver misroutes — 18.3% of bound
  - c2 (geometric series): stranger displacement — 77.1% of bound
  - c3 (1/(8A²-2)): ancestor items — 4.5% of bound

**What needs Rust exploration:**
- Verify the bound holds with the *actual* Seiferas parameters (A, ε, λ)
- Test edge cases at small n and early stages (t=0, t=1)
- Verify the geometric series argument for c2 is correct

**Risk:** MEDIUM. The bound is empirically solid. The proof decomposes into
3 independent sub-lemmas, each of which is a standard argument.

#### WP-B4: Connecting abstract invariant to concrete execution

**Problem:** The invariant tracks abstract `perm` and `bags`, but the sorting
network operates on concrete vectors. We need a bridge: executing
`separatorStage` on vector `v` produces results consistent with some
`SplitResult` satisfying all the hypotheses of `invariant_maintained`.

**What this means concretely:**
- Given the current permutation `perm` and bag assignment `bags`
- Execute `separatorStage` (the real network from WP-A2)
- Define the resulting `split` from the execution
- Prove the split satisfies all hypotheses of `invariant_maintained`

This is the hardest conceptual piece: connecting the comparator network's
execution semantics to the abstract rebagging model.

**What needs Rust exploration:**
- Implement the full pipeline in Rust: build separator stage, execute on
  random inputs, extract the induced split, verify all invariant hypotheses
- Test with various separator implementations (ideal, ε-halver, adversarial)

**Risk:** HIGH. This is the core "soundness" connection between the abstract
proof and the concrete construction. The individual pieces (WP-A2, WP-A3,
WP-B1) all feed into this.

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
- Write Rust programs to validate the concrete split definition
- Test stranger bounds with realistic separator implementations
- Pin down exact partition rules and verify all hypotheses

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
