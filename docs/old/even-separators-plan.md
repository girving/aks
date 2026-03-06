> **OBSOLETE:** Work completed. General γ separators are now supported.

# Plan: Prove `separatorNet_isSeparator` for general γ (DONE)

## Goal

Remove `hγ_half : γ = 1/2` from `separatorNet_isSeparator` and `separators` in
`AKS/Separator/SepProof.lean`. The theorem should work for any `0 < γ ≤ 1/2`.

```lean
theorem separatorNet_isSeparator (γ ε : ℚ) (hγ : 0 < γ) (hε : 0 < ε) (m : ℕ) :
    IsSeparator (separatorNet γ ε hγ hε m) ↑γ ↑ε

def separators (γ ε : ℚ) (hγ : 0 < γ) (hε : 0 < ε) : SeparatorFamily γ ε
```

## Why γ = 1/2 is insufficient

`Seiferas.lean` currently uses `γ = 1/2`, but the comment says this is temporary
and will need `seiferasLam = 1/100` once `AKS/Bags/` is rewritten. The `separators`
API must not bake in `γ = 1/2`.

## Construction recap (`General.lean`)

`separatorNet γ ε hγ hε m` builds a network on `n = 2m` wires:

1. **Initial halver** on all `n` wires (ε₀-halver, `ε₀ = ε / sepTotalLayers γ`)
2. **Prefix-doubling levels** k = K-1, K-2, ..., 0 (K = `numSepLevels γ + 1`):
   - Prefix halver on `[0, 2^(k+1)·m₀)` (length `2·halfLen`, `halfLen = 2^k·m₀`)
   - Suffix halver on `[n - 2^(k+1)·m₀, n)` (same length)
   where `m₀ = max(1, ⌊γ·n⌋₊)`.

Levels where `2^(k+1)·m₀ > n` produce empty comparators (guarded by `if`).

## Existing infrastructure

| Lemma | File | What it does |
|---|---|---|
| `exec_append` | `Sort/Defs.lean:147` | `exec(A++B) = exec(B) ∘ exec(A)` |
| `shiftEmbed_exec_outside` | `Sort/Defs.lean:168` | Positions outside `[offset, offset+m)` untouched |
| `shiftEmbed_exec_inside` | `Sort/Defs.lean:216` | Positions inside see the local halver |
| `exec_displaced_le` | `Sort/Displaced.lean:99` | Comparator networks only decrease displaced count (initial direction) |
| `exec_displaced_final_le` | `Sort/Displaced.lean:167` | Same for final direction |
| `halver_injective_initial_halved` | `Separator/FromHalver.lean:363` | Halver bound for injective inputs (initial) |
| `halver_injective_final_halved` | `Separator/FromHalver.lean:496` | Same for final direction |
| `injective_count_lt_le` | `Separator/FromHalver.lean:449` | Injective map: `|{val < k}| ≤ k` |
| `halver_isSeparator_half` | `Separator/FromHalver.lean:126` | ε-halver → (1/2, ε)-separator |
| `numSepLevels_coverage` | `Separator/General.lean:45` | `2^(K) · γ ≥ 1` so `2^K · m₀ ≥ m` |
| `sepInitial_trivial` | `Separator/General.lean:123` | `⌊γn⌋₊ = 0` → `SepInitial` trivially |
| `sepFinal_trivial` | `Separator/General.lean:143` | Same for `SepFinal` |
| `IsEpsilonHalver_append` | `Halver/Mono.lean` | Appending comparators preserves halver property |

## Proof strategy

### Case split on `⌊γn⌋₊`

- **`⌊γn⌋₊ = 0`**: `SepInitial` and `SepFinal` hold trivially (`sepInitial_trivial`,
  `sepFinal_trivial`). No levels matter.

- **`⌊γn⌋₊ ≥ 1`**: Need the inductive argument below.

### SepInitial direction — inductive invariant

After executing the initial halver + prefix halvers for levels K-1, ..., k, define:

```
displaced(k, threshold) := |{pos : pos.val ≥ 2^k · m₀ ∧ (w' pos).val < threshold}|
```

where `w'` is the wire state after those layers, and `threshold = ⌊γ'·n⌋₊`.

**Claim:** `displaced(k, threshold) ≤ (K + 1 - k) · ε₀ · threshold` for all `k`.

**Base case (k = K):**
- `2^K · m₀ ≥ m` by `numSepLevels_coverage` (since `m₀ ≥ ⌊γn⌋₊` and `2^K · γ ≥ 1`).
- So `{pos ≥ 2^K·m₀} ⊆ {pos ≥ m}`.
- The initial halver gives `|{pos ≥ m : val < threshold}| ≤ ε₀ · threshold`
  via `halver_injective_initial_halved` (with the restriction to `[0, n)` being injective).
- Actually simpler: the initial halver is an ε₀-halver on all `n = 2m` wires.
  After executing it, the output satisfies `EpsilonInitialHalved` with error ε₀.
  The `EpsilonInitialHalved` definition says `|{pos ≥ m : rank(val) < k}| ≤ ε₀ · k`.
  Since `threshold ≤ m` (because `γ' ≤ γ ≤ 1/2` gives `⌊γ'n⌋₊ ≤ m`... wait, γ can
  be > 1/2 in principle, but `γ ≤ 1/2` for our use case. Actually `γ > 1/2` makes
  the theorem false for small n per prior analysis.)

  For now: since `2^K · m₀ ≥ m`, the set `{pos ≥ 2^K·m₀}` is a subset of `{pos ≥ m}`,
  so displaced(K) ≤ displaced_at_m ≤ ε₀ · threshold. ✓

  More precisely: use `exec_displaced_le` to pass through intermediate layers
  (the prefix levels don't increase displaced counts), and use the halver property
  for the initial layer.

**Inductive step (k+1 → k):**
The prefix halver at level k operates on `[0, 2^(k+1)·m₀)` with midpoint `2^k·m₀`.

Split `{pos ≥ 2^k·m₀ : val < threshold}` into:
- **Far:** `{pos ≥ 2^(k+1)·m₀ : val < threshold}` — outside prefix range, unchanged by
  this level's prefix halver (`shiftEmbed_exec_outside`). By induction hypothesis,
  `≤ (K-k) · ε₀ · threshold`.
- **Near:** `{pos ∈ [2^k·m₀, 2^(k+1)·m₀) : val < threshold}` — inside prefix halver range.
  The prefix halver is an ε₀-halver on `2·halfLen` wires, applied to the restriction
  of the current wire state to `[0, 2^(k+1)·m₀)`. By `halver_injective_initial_halved`
  (the restriction is injective since it's a subsequence of a permutation), the count
  of positions in the upper half `[halfLen, 2·halfLen)` with value < threshold is
  `≤ ε₀ · a` where `a = |{val < threshold in [0, 2·halfLen)}|`.
  Since the restriction is injective, `a ≤ threshold` by `injective_count_lt_le`.
  So near count `≤ ε₀ · threshold`.

Total: `(K-k) · ε₀ · threshold + ε₀ · threshold = (K+1-k) · ε₀ · threshold`. ✓

**Final bound (k = 0):**
`displaced(0) = |{pos ≥ m₀ : val < threshold}|`.
Since `m₀ = max(1, ⌊γn⌋₊) ≥ ⌊γn⌋₊`, we have `{pos ≥ ⌊γn⌋₊} ⊇ {pos ≥ m₀}`,
wait — that's the wrong direction. We need `{pos ≥ ⌊γn⌋₊}` but we control `{pos ≥ m₀}`.
Since `m₀ ≥ ⌊γn⌋₊`, the set `{pos ≥ ⌊γn⌋₊}` is *larger* than `{pos ≥ m₀}`.

We need a bound on `{pos ≥ ⌊γn⌋₊ : val < threshold}`, and we have a bound on
`{pos ≥ m₀ : val < threshold}` where `m₀ ≥ ⌊γn⌋₊`. The extra positions in
`[⌊γn⌋₊, m₀)` could have bad values.

**Fix:** When `⌊γn⌋₊ ≥ 1`, we have `m₀ = max(1, ⌊γn⌋₊) = ⌊γn⌋₊` (since `⌊γn⌋₊ ≥ 1`).
So `m₀ = ⌊γn⌋₊` and there's no gap. The `max(1, ...)` only matters when `⌊γn⌋₊ = 0`,
which is the trivial case.

So in the non-trivial case: `m₀ = ⌊γn⌋₊` and the induction gives
`|{pos ≥ ⌊γn⌋₊ : val < threshold}| ≤ (K+1) · ε₀ · threshold`.
Since `K + 1 = numSepLevels γ + 2 = sepTotalLayers γ` and `ε₀ = ε / sepTotalLayers γ`:
`(K+1) · ε₀ = ε`. So displaced ≤ ε · threshold ≤ ε · γ' · n. ✓

### SepFinal direction

Symmetric using suffix halvers and `exec_displaced_final_le` /
`halver_injective_final_halved`. The suffix halver at level k operates on
`[n - 2^(k+1)·m₀, n)` with midpoint at `n - 2^k·m₀`.

The inductive invariant is:
```
displaced_final(k, threshold) := |{pos < n - 2^k·m₀ : val ≥ threshold}|
    ≤ (K+1-k) · ε₀ · (n - threshold)
```

where now `threshold = n - ⌊γ'·n⌋₊` (dual direction).

### ℚ/ℝ bridging

`separatorNet` uses ℚ parameters; `IsSeparator` uses ℝ. The existing
`floor_rat_real_mul_nat` bridges `⌊(γ : ℝ) * n⌋₊ = ⌊(γ : ℚ) * n⌋₊`.
The `convert ... using 1` + `norm_num` trick from the γ = 1/2 proof handles
the final cast.

## Implementation plan

### Step 0: Understand the network decomposition

The network `separatorNet γ ε hγ hε m` has comparators:
```
(family.net m).comparators ++                          -- initial halver
(List.range K).reverse.flatMap (sepLevelComparators n family.net m₀ ·)  -- levels K-1..0
```

Each `sepLevelComparators n halverNet m₀ k` is:
```
prefix_halver(k) ++ suffix_halver(k)
```

After executing through level `k`, the wire state is the result of:
```
exec(suffix(k), exec(prefix(k), exec(levels K-1..k+1, exec(initial, v))))
```

Use `exec_append` to decompose.

### Step 1: Coverage lemma (~10 lines)

```lean
lemma sepBaseChunk_eq_floor (γ : ℚ) (n : ℕ) (hγ : 0 < γ) (hfloor : 0 < ⌊γ * ↑n⌋₊) :
    sepBaseChunk γ n = ⌊γ * ↑n⌋₊
```

Since `⌊γn⌋₊ ≥ 1`, `max(1, ⌊γn⌋₊) = ⌊γn⌋₊`.

```lean
lemma coverage_nat (γ : ℚ) (m : ℕ) (hγ : 0 < γ) :
    m ≤ 2 ^ (numSepLevels γ + 1) * sepBaseChunk γ (2 * m)
```

Uses `numSepLevels_coverage`.

### Step 2: Far-positions preservation lemma (~15 lines)

```lean
lemma displaced_outside_le (net : ComparatorNetwork n) (offset : ℕ)
    (h : offset + m ≤ n) (v : Fin n → Fin n) (B threshold : ℕ) (hB : offset + m ≤ B) :
    -- positions ≥ B are unchanged by shiftEmbed
    |{pos ≥ B : (shiftEmbed.exec v pos).val < threshold}| =
    |{pos ≥ B : (v pos).val < threshold}|
```

Follows from `shiftEmbed_exec_outside` — every position `≥ B ≥ offset + m` is outside
the range, so the output equals the input at those positions. The filter sets are equal.

### Step 3: Near-positions halver bound (~25 lines)

```lean
lemma prefix_halver_near_bound (net : ComparatorNetwork (2 * halfLen))
    (hnet : IsEpsilonHalver net ε₀) (n offset : ℕ) (h : offset + 2 * halfLen ≤ n)
    (v : Fin n → Fin n) (hv : Function.Injective v) (threshold : ℕ) :
    let v' := (net.shiftEmbed n offset h).exec v
    (|{pos ∈ [offset + halfLen, offset + 2*halfLen) : v'(pos).val < threshold}| : ℝ)
    ≤ ε₀ * threshold
```

Proof sketch:
1. Restrict `v` to `[offset, offset + 2*halfLen)` — call it `u : Fin (2*halfLen) → Fin n`.
2. `u` is injective (subsequence of injective `v`).
3. By `shiftEmbed_exec_inside`, the output on `[offset, offset + 2*halfLen)` equals
   `net.exec u`.
4. Apply `halver_injective_initial_halved` to get bound `≤ ε₀ · a` where
   `a = |{i : (u i).val < threshold}|`.
5. By `injective_count_lt_le`, `a ≤ threshold`.

### Step 4: Inductive displaced bound (~40 lines)

This is the core. Define the wire state after executing through level k:

```lean
-- State after initial halver + levels K-1, ..., k
def stateAfterLevel (v : Fin n → Fin n) (k : ℕ) : Fin n → Fin n := ...
```

Or just work with `exec_append` to decompose the full network.

Actually, it's cleaner to prove the bound directly by strong induction on k
(from K down to 0), splitting the full network into "everything through level k+1"
and "level k's prefix".

The inductive statement:
```lean
lemma separatorNet_displaced_induction (k : ℕ) (hk : k ≤ K) :
    let w' := <state after initial + levels K-1..k>
    ∀ threshold, threshold ≤ m →
    (|{pos ≥ 2^k · m₀ : (w' pos).val < threshold}| : ℝ) ≤ (K + 1 - k) * ε₀ * threshold
```

Base: k = K. By coverage, `2^K · m₀ ≥ m`. The state is just `exec(initial_halver, v)`.
The halver gives `|{pos ≥ m : val < threshold}| ≤ ε₀ · threshold` (via
`EpsilonInitialHalved`). Since `{pos ≥ 2^K·m₀} ⊆ {pos ≥ m}`, the count is ≤ ε₀·threshold = (1)·ε₀·threshold. ✓

Step: k → k-1. The state after level k-1 = exec(suffix(k-1), exec(prefix(k-1), w'_k)).
For SepInitial we only need the prefix halver (suffix doesn't affect positions < n - something,
which are the positions we care about for SepInitial when positions are in the lower half).

Wait — actually the suffix halver CAN affect positions in `[2^(k-1)·m₀, 2^k·m₀)` if
`n - 2^k·m₀ < 2^k·m₀`, i.e., if the suffix range overlaps with the prefix range.

**Key insight:** Use `exec_displaced_le` to handle the suffix halver. Since comparator
networks only *decrease* displaced counts (small values at high positions), the suffix
halver can only help (or not affect) the SepInitial bound. So:

```
displaced_after_suffix(k-1) ≤ displaced_after_prefix(k-1)
```

by `exec_displaced_le` applied to the suffix halver.

So we only need to bound the displaced count after the prefix halver, and the suffix
halver is free.

Similarly for SepFinal: the prefix halver is free (can only decrease large values at
low positions), and we only need to bound the displaced count after the suffix halver.

This simplifies the proof considerably.

### Step 5: Assembly (~15 lines)

```lean
theorem separatorNet_isSeparator (γ ε : ℚ) (hγ : 0 < γ) (hε : 0 < ε) (m : ℕ) :
    IsSeparator (separatorNet γ ε hγ hε m) ↑γ ↑ε := by
  intro v
  constructor
  · -- SepInitial
    by_cases hfloor : ⌊(γ : ℝ) * ↑(2 * m)⌋₊ = 0
    · exact sepInitial_trivial ...
    · -- Use induction at k = 0 with m₀ = ⌊γn⌋₊
      ...
  · -- SepFinal: symmetric
    ...
```

### Step 6: Clean up `separators` (~5 lines)

```lean
def separators (γ ε : ℚ) (hγ : 0 < γ) (hε : 0 < ε) : SeparatorFamily γ ε where
  depth := separatorDepth γ ε hγ hε
  net m := separatorNet γ ε hγ hε m
  isSeparator m := separatorNet_isSeparator γ ε hγ hε m
  depth_le m := separatorNet_depth_le γ ε hγ hε m
```

No `hγ_half` parameter.

## Files to modify

1. **`AKS/Separator/SepProof.lean`** — rewrite proof for general γ (~150 lines)
2. **`AKS/Seiferas.lean`** — remove `hγ_half` from `separators` call (if present)

## Key risks

- **Near-bound argument:** Connecting `shiftEmbed_exec_inside` with
  `halver_injective_initial_halved` requires careful index arithmetic
  (offset + halfLen ↔ position m in the local halver). MEDIUM risk.

- **Induction bookkeeping:** Decomposing the flatMap into individual levels
  and tracking the wire state. May need a helper to peel off one level.
  MEDIUM risk.

- **ℚ/ℝ casts in coverage:** `numSepLevels_coverage` is over ℚ, but positions
  are ℕ. Need `⌊γ * n⌋₊ ≤ m₀` and `2^K * m₀ ≥ m`. LOW risk (mostly `omega`).

## Estimated size

~150 lines in `SepProof.lean` (replacing current ~100 lines).
