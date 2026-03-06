> **OBSOLETE:** Superseded by docs/bags.md. Analysis was for an earlier formulation of the stranger bound.

# Removing Clause 8: Benchmark Comparison Analysis

## Overview

The `SeifInvariant` (in `AKS/Bags/Invariant.lean`) had 10 fields (now 9). Clause 8
(`deviation_bound`) bounds `|C - ⌊b/2⌋| ≤ cnativeCoeff × bagCapacity` for each
active bag. This clause is **not in the paper's 4-clause invariant** (Seiferas 2009,
page 3) — it was added during formalization to factor out the "sibling-native" bound
needed for maintaining clause 4 (1-stranger bound).

The problem: maintaining clause 8 across stages requires
`three_source_native_bound` (SplitStranger.lean:1553), which is **sorry'd** and
**provably unsolvable** with the current decomposition (the separate absolute values
are ~14× too loose; see separator-plan.md §644–663).

This document records the detailed analysis of the paper's actual proof mechanism
for maintaining clause 4 without clause 8, based on careful reading of Seiferas
Section 5 (pages 4–7) and empirical validation via `rust/test-benchmark-comparison.rs`.

## Paper's 4-Clause Invariant (Seiferas, page 3)

1. **Alternating**: Alternating levels are entirely empty
2. **Uniform size**: On each active level, each bag has `bagSize` items
3. **Capacity**: Items in each bag ≤ current capacity `b`
4. **Strangers**: j-strangers ≤ `λε^(j-1) × b` (current capacity)

No deviation bound. The paper maintains these 4 clauses by induction on stages.

## Paper's Section 5: Maintaining Clause 4 (j=1 Case)

This is the core argument. The j > 1 case is straightforward (page 4 bottom);
the j = 1 case requires the **benchmark comparison** (page 5).

### Setup

- B is a currently empty bag at level l, with current capacity b
- D = B's parent at level l−1 (currently active, about to be split)
- C = B's sibling (also at level l, currently empty)
- d = number of items in D (d ≤ b/A since cap(D) = b/A)

After the separator is applied to D, items are distributed: middle items go down
to B and C, fringe items go up to D's parent.

### Three Sources of 1-Strangers at B

After the iteration, B receives items from D. Some of these items are 1-strangers
(native to C, D, or some adjacent bag). The paper decomposes 1-strangers by source:

**Source 1: Current 2-strangers at D's children** (at most `2λεbA`)
- B and C's children (at level l+1) currently contain items. Among them,
  2-strangers are at tree distance ≥ 2 from their native bag. After redistribution,
  some become 1-strangers at B.
- Bounded by Clause 4 with j=2 at the children's level.

**Source 2: Unfiltered 1-strangers in D** (at most `ελb/A`)
- D has at most `λ × cap(D) = λb/A` 1-strangers. The separator filters fringe
  items (including some strangers), but with error rate ε, some 1-strangers
  remain in the middle portion and end up in B.
- Bounded by Clause 4 with j=1 at D's level, times ε (separator error).

**Source 3: C-native items in D sent to B** (the hard case)
- Items in D that are native to C (perm ∈ C's range) but get placed in B by
  the separator. The count of these is at most:

  (C-native items in D in excess of d/2) + (halving errors ≤ εb/(2A))

The **halving errors** are items the approximate separator places in the wrong
half: bounded by `εb/(2A)` (separator property).

The **C-native excess** = (actual C-native items in D) − d/2 is the hard part,
bounded via the benchmark comparison.

### The Benchmark Comparison

The paper defines a hypothetical **benchmark distribution** with the same item
counts per bag but a more symmetric internal arrangement:
- For each bag C' at B's level: only C'-native items below C'
- For each bag C' at B's level: d'/2 C'-native items in parent D'

In the benchmark, C-native items in D in excess of d/2 = 0.

**Where can the excess come from (actual vs benchmark)?**

Two sources:

#### (a) C-native items at levels above D

In the actual distribution, some items at ancestor levels have perm in C's range.
These items exist in the benchmark too but may be redistributed. The paper counts
total items at levels above D:

Active ancestor levels above D: l−3, l−5, l−7, ... (same parity as D = l−1).
At ancestor level l−(2k+1) for k ≥ 1:
- 2^(l−2k−1) bags at that level
- Each bag has items ≤ capacity: cap(l−2k−1) = b/A^(2k+1) (paper's Clause 3)
- Total items at this level ≤ 2^(l−2k−1) × b/A^(2k+1)

The paper then claims: "Since the number native to each such C' is the same,
the number native to C is at most 1/2^i times as much" (where 2^i = 2^l bags
at C's level). This is an **equidistribution** argument: items at each ancestor
level are equally distributed among all 2^l C'-intervals.

C-native items above D ≤ (2^(l−3) × b/A³)/2^l + (2^(l−5) × b/A⁵)/2^l + ...
                        = b/(2A)³ + b/(2A)⁵ + b/(2A)⁷ + ...
                        = b/((2A)³ × (1 − 1/(2A)²))
                        = **b/(8A³ − 2A)**

For A=10: b/7980. Very small.

**Key point 1:** This bound requires **items ≤ capacity** (not just items ≤ bagSize).
Our current Lean Clause 3 uses `bagSize = n/2^level` (structural, stage-independent),
while the paper uses capacity = n·ν^t·A^level (decays with stage). We need to add
items ≤ bagCapacity to the invariant (provable from `capacity_maintained`).

**Key point 2:** This bound requires **equidistribution** — that items at each
ancestor level are equally distributed among C'-intervals. This follows from the
construction's symmetry (same separator applied to all bags at each level) but is
NOT captured by the current invariant. We need to either:
- Add an equidistribution clause to the invariant, OR
- Use a weaker bound: items in C's ancestor bag ≤ cap(ℓ), giving
  above ≤ b/(A³−A) = b/990 (for A=10). This still satisfies the constraint
  (LHS = 0.005693 < 0.0065 = RHS, slack 1.14) but is 8× weaker.

**Key point 3:** Ancestor items are all native at their level — there are
0 strangers at ancestor levels with perm in D's range (confirmed empirically).
The bound works because C's range is a tiny fraction (1/2^l) of the ancestor's range.

#### (b) Net reduction of C-native items in C's subtree

In the actual distribution, C's subtree may contain items NOT native to C
(items with perm outside C's range). These displace C-native items out of
C's subtree — some of those displaced items end up in D.

The count of non-C-native items in C's subtree is bounded by Clause 4:

Active levels in C's subtree: l+1, l+3, l+5, ... (same parity as D, opposite to C).
At level l+(2k+1) for k = 0, 1, 2, ...:
- 2^(2k+1) bags in C's subtree at this level
- Each bag has index idx ∈ [c·2^(2k+1), (c+1)·2^(2k+1))
- Items NOT native to C have `nativeBagIdx(n, l, rank) ≠ c`
- In `isJStranger` terms: j−1 = (l+2k+1) − l = 2k+1, so **j = 2k+2**
  (verified: `idx/2^(j−1) = idx/2^(2k+1) = c` for bags in C's subtree)
- Clause 4 bound per bag: λ · ε^(j−1) · cap = λ · ε^(2k+1) · bA^(2k+1)
- Total at this level: 2^(2k+1) × λ · ε^(2k+1) · bA^(2k+1) = λ · (2εA)^(2k+1) · b

Concrete levels:
- Level l+1 (k=0): j=2 strangers. 2 × λε × bA = **2λεbA**
- Level l+3 (k=1): j=4 strangers. 8 × λε³ × bA³ = **8λε³bA³** = λ(2εA)³b
- Level l+5 (k=2): j=6 strangers. 32 × λε⁵ × bA⁵ = **32λε⁵bA⁵** = λ(2εA)⁵b

Sum over k ≥ 0: λb · Σ_{k≥0} (2εA)^(2k+1)
  = λb · 2εA · (1 + (2εA)² + (2εA)⁴ + ...)
  = **2λεbA/(1 − (2εA)²)**

For A=10, ε=0.01: 2λ × 0.1 × b / 0.96 ≈ 0.208λb.

**Key point: this bound uses Clause 4 at C's subtree levels with j = 2k+2.**
The stranger level increases with depth in C's subtree: 2-strangers at l+1,
4-strangers at l+3, 6-strangers at l+5, etc. Each level's contribution is
λ·(2εA)^(2k+1)·b, summing to a convergent geometric series since 2εA = 0.2 < 1.

**Provability of the subtree bound:** The subtree bound is NOT claiming that
non-C-native items are always zero (that's just an artifact of small test sizes —
see "Subtree Strangers Are Not Provably Zero" below). It claims they are bounded
by the clause 4 stranger budget, which is an inductive hypothesis. The proof
structure is:

1. For each bag in C's subtree at level l+(2k+1), "not native to C" corresponds
   precisely to `isJStranger` with j=2k+2 (definitional, from how `isJStranger`
   checks `nativeBagIdx(n, l, rank) ≠ idx/2^(2k+1)`).
2. The inductive hypothesis (clause 4 at stage t) bounds j-strangers per bag
   by `λ·ε^(j-1)·cap`. This holds for ALL j ≥ 1 and ALL levels.
3. Summing over bags at each level and levels over k gives the geometric series.

Step 1 is the key insight: the definitional connection between "non-C-native" and
`isJStranger` at the right j. Step 2 is just invoking the inductive hypothesis.
Step 3 is arithmetic.

### Subtree Strangers Are Not Provably Zero

Our Rust tests show zero non-C-native items at subtree levels for all test sizes
(n ≤ 4096). This does NOT mean the subtree bound is vacuously true. Here's why:

**Why tests show zero:** With λ=ε=1/100, the stranger budget per bag is
`0.01 × 0.01^(j-1) × cap`. For j=2 at level l+1, that's `0.0001 × cap`. With
small bags (cap often < 100 in our tests), the budget is < 0.01, so even one
stranger would be notable. The construction works well enough at small sizes
that no items migrate far enough to become j≥2 strangers in the subtree.

**Why nonzero strangers are possible in principle:** Consider C at level l with
index c, and a bag at (l+1, 2c) in C's subtree. An item with
`nativeBagIdx(n, l, rank) ≠ c` is a 2-stranger at this bag. Such items arise
when the separator at a previous stage misclassifies items with error rate ε,
placing them in the wrong child. Over multiple stages, items can drift into bags
where they are high-order strangers. With ε=0.01, this happens with probability
~ε per stage per item, so at n=2^20 with many stages we'd expect to see them.

**Why this doesn't matter for the proof:** The proof doesn't assume stranger
counts are zero. It assumes stranger counts satisfy clause 4's bound
`λ·ε^(j-1)·cap`, which is the inductive hypothesis. The bound is correct whether
the actual count is 0 or 0.9×λ·ε^(j-1)·cap. The geometric series
`2λεbA/(1-(2εA)²)` sums the worst-case budgets, not the actual counts.

**Larger tests would show nonzero subtree strangers.** At n=2^20, bags have
cap ≈ 2^20/2^l which is large enough that `λε·cap ≫ 1`, making it probable
that some items become 2-strangers at subtree levels. The proof handles this
by design — it uses the budget, not the actual count.

### Combined Source 3 Bound

C-native excess ≤ (subtree displacement) + (above items)
                = 2λεbA/(1−(2εA)²) + b/(8A³−2A)

Source 3 total ≤ C-native excess + halving errors
              = 2λεbA/(1−(2εA)²) + b/(8A³−2A) + εb/(2A)

### Total 1-Stranger Bound

Total 1-strangers at B ≤ source1 + source2 + source3
= 2λεbA + ελb/A + εb/(2A) + 2λεbA/(1−(2εA)²) + b/(A³−A)

(Using the **weakened** above bound b/(A³−A) instead of paper's b/(8A³−2A).)

This must be ≤ λνb (the 1-stranger budget at the next stage, capacity νb).

Dividing by b:

**2λεA + ελ/A + ε/(2A) + 2λεA/(1−(2εA)²) + 1/(A³−A) ≤ λν**

For A=10, λ=ε=1/100, ν=13/20:
LHS = 0.002 + 0.0001 + 0.0005 + 0.002083 + 0.001010 = 0.005693
RHS = 0.0065

**0.005693 < 0.0065** ✓ (slack factor 1.14)

(Paper's tighter bound with equidistribution: LHS = 0.004718, slack 1.38.)

### What the Paper Does NOT Use

- **No deviation bound** (clause 8). The benchmark comparison replaces it.
- **No recursive argument through ancestor deviations.** The ancestor contribution
  uses total item counts (Clause 2/3), not ancestor deviations.
- **No per-level stranger counts at ancestor levels.** Ancestor items are all native;
  the bound comes from the 1/2^i fraction argument.

## Weakened vs Paper's Above Bound: `b/(A³−A)` vs `b/(8A³−2A)`

### Why we use the weakened bound

The paper's bound `b/(8A³−2A)` requires:
1. Items ≤ capacity (we need this regardless)
2. **Equidistribution**: items at each ancestor level are equally distributed
   among C'-intervals at B's level

Equidistribution is a construction symmetry — the same separator is applied to
all bags at each level, so item distributions are symmetric. But this is NOT
captured by the current invariant, and formalizing it would require either:
- Adding an equidistribution clause to `SeifInvariant` (invasive)
- Proving it as a separate property of the construction (significant work)

The weakened bound `b/(A³−A)` avoids equidistribution entirely by bounding items
at ancestor level ℓ by the full capacity `cap(ℓ)` of C's ancestor bag, rather
than `cap(ℓ)/2^l` (the equidistributed share). This is valid because all items
in C's ancestor bag — regardless of which C'-interval they belong to — could in
the worst case all have perm in C's range.

### Constraint verification

With the weakened bound, `SatisfiesC4_eq1` becomes:
```
2λεA + ελ/A + ε/(2A) + 2λεA/(1-(2εA)²) + 1/(A³-A) ≤ λν
```

For Seiferas parameters (A=10, λ=ε=1/100, ν=13/20):
- LHS = 0.005693
- RHS = 0.0065
- Slack factor: 1.14

Verified in Lean with `norm_num`:
```lean
example : (2 : ℚ) * (1/100) * (1/100) * 10 + (1/100) * (1/100) / 10 + (1/100) / (2 * 10)
  + 2 * (1/100) * (1/100) * 10 / (1 - (2 * (1/100) * 10) ^ 2)
  + 1 / ((10 : ℚ)^3 - 10)
  ≤ (1/100) * (13/20) := by norm_num
```

### Fallback to paper's tighter bound

If the weakened bound turns out insufficient (unlikely, since it provably satisfies
the constraint), or if we want to match the paper exactly, the fix is **localized**:

1. Change `1/(A³-A)` back to `1/(8A³-2A)` in `SatisfiesC4_eq1` (one line)
2. `parentStrangerCoeff` changes correspondingly (one line)
3. `seiferas_preview_satisfiesConstraints` still passes (strictly easier)
4. The above bound proof must be strengthened to use equidistribution
5. **Everything downstream of `SatisfiesC4_eq1` is unchanged** — the constraint
   flows through `stranger_eq1_arithmetic` and `c4_eq1_decomposed` algebraically

How we'll know the weakened bound isn't working: if we can't prove the above
bound ≤ `b/(A³-A)` per ancestor level, we'd get stuck on `hparent_1stranger`.
This is the same place we'd get stuck with the tighter bound, just with a harder
target. The weakened bound strictly dominates — if it fails, the paper's bound
fails too (it needs everything we need plus equidistribution).

The `hparent_1stranger` hypothesis in `stranger_bound_maintained_eq1` should carry
a comment noting this fallback path:
```
-- NOTE: hparent_1stranger uses the weakened above bound 1/(A³-A) instead of the
-- paper's 1/(8A³-2A). If tightening is ever needed: (1) change SatisfiesC4_eq1,
-- (2) change parentStrangerCoeff, (3) prove equidistribution for above bound.
-- Everything downstream of SatisfiesC4_eq1 is algebraic and needs no change.
```

## Empirical Validation (`rust/test-benchmark-comparison.rs`)

The Rust test validates the paper's proof strategy by simulating the bag tree with
adversarial separators (Seiferas parameters A=10, ν=0.65, λ=ε=0.01) for n=2^3
through 2^12.

### Results Summary

| Metric | Result | Status |
|--------|--------|--------|
| Full bound: \|signed_sum\| ≤ 2·cnc·cap | max ratio **0.056** | PASS |
| Per-level asym ≤ strangers (when both > 0) | ratio **1.0** | PASS |
| Clause 4: stranger_count / (λ·cap) | max **0.023** | PASS |
| s_lo + s_hi ≤ λ·cap | max **0.023** | PASS |
| Ancestor native asym / \|ancestor dev\| | **107×** | Expected — see below |
| Ancestor asym / (cnc·cap·interval_frac) | **60×** | Expected — see below |
| Above-D strangers | **always 0** | Confirms paper |
| Subtree: non-C-native items at subtree levels | **always 0** | Artifact of small tests (see above) |
| Above: items in C's anc bag / paper's expected | max **0.08** | Well within bounds |
| Above: items in C's anc bag / weakened expected | max **0.10** | Weakened bound works |
| Equidistribution ratio (actual/expected) | max **4.0** | Violated, but bound still holds |

### Key Findings

**Finding 1: Zero strangers at ancestor levels.** Items at ancestor bags with perm
in D's range are ALL native at their level (0 strangers). This confirms that the
paper's "above" bound uses total item counts, not stranger counts. The 1/2^i fraction
argument is the correct mechanism.

**Finding 2: Ancestor deviation does not control contribution (107×).** The ancestor's
own deviation (|C_A − b_A/2|) does NOT bound the asymmetry it creates in D's range.
An ancestor with deviation 1 can create asymmetry 107 in D's interval, because:
- The ancestor's L/R split is at a DIFFERENT boundary than D's B/C boundary
- Items distribute within ancestor's range based on the full separation history,
  not just the ancestor's own deviation

This falsifies naive proof strategies like "telescope deviations through the tree"
or "bound each ancestor's contribution by cnc·cap·interval_fraction."

**Finding 3: The paper's approach avoids this entirely.** The paper doesn't try to
bound the ancestor contribution via deviations or stranger counts at ancestor levels.
Instead:
- The "above" source contributes b/(8A³−2A), using only the total items at ancestor
  levels divided by the number of bags at C's level
- The "subtree" source contributes 2λεbA/(1−(2εA)²), using stranger counts at
  C's SUBTREE levels (not ancestor levels)

**Finding 4: Subtree formula trivially satisfied in tests.** Non-C-native items in
C's subtree bags are always 0 in the simulation. This is an artifact of small test
sizes (n ≤ 4096) with λ=ε=1/100 — the stranger budget per bag is < 0.01 items, so
even one stranger is improbable. The subtree bound `2λεbA/(1−(2εA)²)` sums
worst-case budgets from clause 4, not actual counts, so it's valid regardless. See
"Subtree Strangers Are Not Provably Zero" above for detailed analysis.

**Finding 5: Above bound holds with weakened approach.** Items with perm in C's
interval at ancestor levels are bounded by the capacity of C's ancestor bag (no
equidistribution needed). The ratio `items_in_ancestor_bag / (b/A^shift)` peaks at
0.10 (10× slack). The paper's equidistribution assumption (items equally distributed
among C'-intervals) is violated by up to 4×, but the overall bound is still safe
because capacity at ancestor levels is so small relative to b.

**Finding 6: Weakened above bound is sufficient.** Using the crude bound
`above ≤ Σ cap(ℓ) = b/(A³−A)` (no equidistribution) gives:
- LHS = 2λεA + ελ/A + ε/(2A) + 2λεA/(1−(2εA)²) + 1/(A³−A) = 0.005693
- RHS = λν = 0.0065
- **0.005693 < 0.0065** ✓ (slack factor 1.14)
This is tighter than the paper's bound (slack 1.38) but still valid. The weakened
approach avoids the equidistribution formalization entirely.

**Finding 7: Full bound holds with 18× margin.** Despite individual diagnostic ratios
being large (107×, 60×), the overall bound holds with ratio 0.056 (18× slack). This
confirms the bound is true and the proof strategy is viable — just not via the naive
decomposition.

## Relationship to Current Lean Code

### Current dependency chain (with clause 8)

```
deviation_bound(t) ──→ benchmark_analytic_bound ──→ concreteSplit_cnative_bound
                   └──→ parent_1stranger_bound ──→ stranger_bound(t+1)  [PROVED]

stranger_bound(t)  ──→ rebag_stranger_bound                            [PROVED]

deviation_bound(t+1) ←── three_source_native_bound                     [SORRY]
    uses: stranger_bound(t), deviation_bound(t), items_partition
```

The circular dependency: clause 8 at time t+1 depends on clause 8 at time t
(via `three_source_native_bound`), which is sorry'd because the decomposition
into separate absolute values |kick_imb| + |fp_imb| + fp%2 is 14× too loose.

### Paper's dependency chain (without clause 8)

```
stranger_bound(t, all levels) + uniform_size + capacity_bound
    │
    ├──→ source 1 bound (2-strangers at children)
    ├──→ source 2 bound (1-strangers in D, filtered)
    └──→ source 3 bound (benchmark comparison)
         ├──→ subtree: strangers in C's subtree ← Clause 4
         └──→ above: total items / 2^i ← Clause 2/3
    │
    └──→ stranger_bound(t+1)
```

No clause 8 anywhere. The stranger bound at t+1 depends only on:
- Stranger bounds at t (all levels) — Clause 4
- Structural properties (uniform size, capacity) — Clauses 2, 3
- Separator properties (halving error ≤ ε)

## Existing Proved Infrastructure That Can Be Reused

| Theorem | File:Line | Role | Reusable? |
|---------|-----------|------|-----------|
| `rebag_stranger_bound` | SplitStranger:1375 | s_lo+s_hi ≤ λ·cap(t+1) | YES |
| `siblingNative_le_deviation` | SplitStranger:1028 | siblingNative ≤ \|C−b/2\| | YES (identity) |
| `deviation_identity` | SplitStranger:499 | 2(C−b/2) = (s_lo−s_hi)+(n_L−n_R)+b%2 | YES |
| `filter_partition_card` | SplitStranger:635 | Perm bijectivity | YES |
| `filter_comp_perm_card` | SplitStranger:536 | \|filter(P∘perm)\| = \|filter(P)\| | YES |
| `rankInBag_ge_count_below` | Split:103 | Items above threshold have high rank | YES |
| `fringeSize_le_mul` | SplitCard:346 | fringeSize ≤ λ·cap | YES |
| `kick_toParent_card_uniform` | SplitStranger:1469 | \|kL\| = \|kR\| | YES |
| `concreteSplit_cnative_bound` | SplitStranger:1216 | siblingNative ≤ cnc·cap(l−1) | PARTIALLY — currently chains through deviation_bound |
| `benchmark_analytic_bound` | SplitStranger:675 | Signed sum ≤ 2·cnc·cap | REPLACE — currently uses clause 8 |
| `below_boundary_deviation` | SplitStranger:808 | Wraps benchmark_analytic_bound | REPLACE |

### Code to Delete (depends on sorry)

| Theorem | File:Line | Status |
|---------|-----------|--------|
| `three_source_native_bound` | SplitStranger:1529–1553 | SORRY — delete |
| `rebag_native_imbalance_bound` | SplitStranger:1568 | Depends on sorry — delete |
| `rebag_analytic_bound` | SplitStranger:1652 | Depends on sorry — delete |
| `concreteSplit_rebag_deviation` | SplitStranger:1772 | Depends on sorry — delete |
| `deviation_bound` field | Invariant:137–147 | Remove from SeifInvariant |

## Phase 2 Plan: Lean Proof Structure

### Step 1: Prove the benchmark comparison bound (NEW)

Create `AKS/Bags/Clause4.lean` with a new proof of the 1-stranger bound for
source 3, using the paper's benchmark comparison argument.

The key theorem to prove:

```lean
theorem source3_bound (inv : SeifInvariant n A ν lam ε t perm bags) ... :
    (C_native_excess_in_D : ℚ) ≤
    2 * lam * ε * b * A / (1 - (2 * ε * A)^2) + b / (A^3 - A)
```

Note: uses the **weakened** above bound b/(A³−A) instead of the paper's
b/(8A³−2A). This avoids needing equidistribution (see Finding 6).

This decomposes into two sub-bounds:

**Subtree bound** (uses Clause 4): Count items in C's subtree bags that are
not native to C. At each active level l+(2k+1) in C's subtree, these are
**(2k+2)-strangers** (j = 2k+2, since the ancestor check at level l gives
`nativeBagIdx(n, l, rank) ≠ idx/2^(2k+1) = c`). Clause 4 gives per-bag bound
λ·ε^(2k+1)·cap(l+2k+1). Total: 2^(2k+1) bags × bound = λ·(2εA)^(2k+1)·b.
Sum with geometric decay gives **2λεbA/(1−(2εA)²)**.

The subtree bound is a straightforward application of the inductive hypothesis
(clause 4 at stage t). The key step is the definitional connection:
"non-C-native at level l+(2k+1)" = "(2k+2)-strangers" via `isJStranger`.
See "Provability of the subtree bound" in Section 5 above.

**Above bound** (uses items ≤ capacity): Items at ancestor levels with perm in
C's interval. At ancestor level ℓ, C's ancestor bag has ≤ cap(ℓ) = b/A^(l−ℓ)
items. In the worst case, ALL of them have perm in C's interval. Sum over
ancestor levels ℓ = l−3, l−5, ...:
  above ≤ Σ b/A^(l−ℓ) = b/A³ + b/A⁵ + ... = **b/(A³−A)**

This is weaker than the paper's b/(8A³−2A) but avoids the equidistribution
argument (confirmed empirically: equidistribution violated by 4× but bound
still holds with 1.14× slack).

**Prerequisite:** Need items ≤ bagCapacity as an invariant property. Can derive
from `capacity_maintained` by induction.

### Step 1b: Update `SatisfiesC4_eq1`

The current `SatisfiesC4_eq1` uses the paper's `1/(8A³−2A)` (with equidistribution).
Change to `1/(A³−A)` for the weakened approach:

```lean
def SatisfiesC4_eq1 (A ν lam ε : ℚ) : Prop :=
  2 * lam * ε * A + ε * lam / A + ε / (2 * A)
  + 2 * lam * ε * A / (1 - (2 * ε * A) ^ 2)
  + 1 / (A ^ 3 - A)          -- was: 1 / (8 * A ^ 3 - 2 * A)
  ≤ lam * ν
```

Verified: `seiferas_preview_satisfiesConstraints` still holds with `norm_num`.

### Step 2: Wire into stranger bound maintenance

Replace `concreteSplit_cnative_bound`'s proof chain. Currently:
```
siblingNative_le_deviation → below_boundary_deviation → benchmark_analytic_bound
                                                        └── uses inv.deviation_bound
```

New chain:
```
source3_bound → (combines with sources 1, 2, halving errors)
             → total_1stranger_bound ≤ λνb
             → stranger_bound(t+1)
```

### Step 3: Remove clause 8 from SeifInvariant

1. Delete `deviation_bound` field from `SeifInvariant` (Invariant.lean:137–147)
2. Delete `cnativeCoeff` definition (no longer needed for invariant)
3. Update `initialInvariant` — remove clause 8 proof (lines 284–343)
4. Update `invariant_maintained` — remove `hrebag_deviation` parameter (lines 839–845)
5. Delete sorry'd pipeline: `three_source_native_bound`, `rebag_native_imbalance_bound`,
   `rebag_analytic_bound`, `concreteSplit_rebag_deviation` (~280 lines)
6. Update `concreteSplit_maintains_invariant` (SplitProof.lean:73) — remove
   `hrebag_deviation` argument
7. Update `perm_rearrange` (TreeSort.lean:305–309) — remove `deviation_bound` field
8. Sorry at TreeSort.lean:528 (`hrebag_deviation`) is **eliminated**

### Sorries Affected

| Sorry | File:Line | Effect |
|-------|-----------|--------|
| `three_source_native_bound` | SplitStranger:1553 | ELIMINATED (deleted) |
| `hrebag_deviation` (in TreeSort) | TreeSort:528 | ELIMINATED (field removed) |
| `hfilter` case 3 | TreeSort:493 | UNCHANGED |
| `hcnative` mixed perms | TreeSort:502 | UNCHANGED |
| `separatorSortingNetwork_sorts` | TreeSort:616 | UNCHANGED |

Net effect: **2 sorries eliminated**, 3 remain.

## Risk Assessment

| Component | Risk | Rationale |
|-----------|------|-----------|
| Subtree stranger bound | MEDIUM | Standard Clause 4 at each subtree level with j=2k+2; geometric series. Definitional connection between "non-C-native" and `isJStranger` is straightforward. Nonzero stranger counts at subtree levels are handled by the clause 4 budget (see "Subtree Strangers Are Not Provably Zero"). |
| Above items bound (paper's version) | HIGH | Needs items ≤ capacity AND equidistribution. Equidistribution is a construction symmetry not in the current invariant. |
| Above items bound (weakened) | MEDIUM | Uses only items ≤ capacity from C's ancestor bag. No equidistribution needed. Constraint still holds (slack 1.14) but tight. |
| Items ≤ capacity in invariant | LOW–MEDIUM | Can derive from `capacity_maintained` by induction. Mechanical but needs plumbing. |
| Wiring into stranger maintenance | LOW | Structural; existing infrastructure handles most of it |
| Removing clause 8 | LOW | Mechanical deletion once the new proof compiles |
| Overall | MEDIUM–HIGH | The above bound is the main risk. Recommend starting with the weakened version (no equidistribution) and upgrading later if needed. |

## Open Questions

1. ~~**Exact stranger levels in subtree.**~~ **RESOLVED.** Items not native to C
   at level l+(2k+1) in C's subtree are **(2k+2)-strangers** (not (2k+1)).
   Derivation: `isJStranger` at level l+(2k+1) with `j−1 = 2k+1` gives `j = 2k+2`.
   The condition checks `nativeBagIdx(n, l, rank) ≠ idx/2^(2k+1) = c`. ✓

2. ~~**Active vs inactive levels.**~~ **RESOLVED.** D is at level l−1 (active,
   `(t+l−1)%2=0`). C's subtree active levels: l+1, l+3, l+5, ... (same parity
   as D). Ancestor active levels above D: l−3, l−5, l−7, ... ✓

3. **Capacity convention.** Lean uses `bagCapacity n A ν t level = n × ν^t × A^level`
   where deeper levels have HIGHER capacity (matching the paper). But the paper's "b"
   is the capacity at B's level (= cap(l)), while D's capacity = b/A = cap(l−1). Need
   to be careful about which level's capacity appears in each bound.

4. **`cnativeCoeff` after removal.** The `cnativeCoeff` formula was introduced for
   clause 8. After removal, the three-source bound's terms should be expressed
   directly in the stranger bound maintenance proof, not through `cnativeCoeff`.
   However, `concreteSplit_cnative_bound` currently uses `cnativeCoeff` in its
   statement — this statement may need to change.

5. **Items ≤ bagCapacity needed in invariant.** The above bound requires items ≤
   capacity (not just items ≤ bagSize). Our Clause 3 uses `bagSize = n/2^level`,
   but the paper's Clause 3 uses capacity = n·ν^t·A^level. We need to either:
   - Add `items_le_capacity : (bags level idx).card ≤ bagCapacity ...` as a field
   - Derive it from `capacity_maintained` by induction on stages
   The second approach avoids enlarging the invariant.

6. **Equidistribution for the above bound.** The paper claims "the number native
   to each C' is the same" at each ancestor level. This is a symmetry property
   of the construction (same separator applied to all bags at each level). It's
   NOT captured by the current invariant. Options:
   - (a) Add equidistribution clause to invariant (cleanest, matches paper)
   - (b) Use weaker bound: above ≤ b/(A³−A) = b/990 without symmetry.
     Still satisfies constraint (LHS = 0.005693 < 0.0065 = RHS, slack 1.14).
   - (c) Prove equidistribution as a separate theorem about the construction
   **Decision: option (b)** for now, with clear fallback path to (a)/(c). See
   "Weakened vs Paper's Above Bound" section above.

## Phase 2 Implementation Status

**Completed:** Clause 8 (`deviation_bound`) removed from `SeifInvariant`.

### Changes made (all compile, 0 errors across 60 files):

- **`Invariant.lean`**: Removed `deviation_bound` field from `SeifInvariant` (10→9 fields).
  Removed `hrebag_deviation` parameter from `invariant_maintained`. Removed clause 8
  proof from `initialInvariant` and unused `h2εA`/`hperm` params. Updated coefficient
  definitions: `cnativeCoeff` (`1/(8A²-2)` → `1/(A²-1)`), `parentStrangerCoeff`
  (`1/(8A³-2A)` → `1/(A³-A)`), `SatisfiesC4_eq1` (updated master constraint).
- **`SplitStranger.lean`**: `benchmark_analytic_bound` proof sorry'd at the input
  hypothesis `hdev` (was `inv.deviation_bound`, removed). Rest of proof body preserved.
- **`SplitProof.lean`**: Removed `hrebag_deviation` argument to `invariant_maintained`.
- **`TreeSort.lean`**: Removed `deviation_bound` transfer in `perm_rearrange`, removed
  `hrebag_deviation` sorry block in `actualModel_invariant`, fixed `initialInvariant` calls.
- **`Stage.lean`**: Fixed `initialInvariant` call (removed `h2εA`/`hperm` args).
- **`SeparatorBridge.lean`**: Updated docstring (no code changes needed).

### Naming convention decision

**No c4 parallel naming.** The old 8-clause lemmas were modified in-place rather than
creating parallel `*_c4` versions. Rationale: the `deviation_bound` field removal is a
clean deletion — old proofs that referenced it are sorry'd at a single well-defined point
(`hdev` in `benchmark_analytic_bound`), preserving the rest of their proof structure. The
old proof body is intact and can be restored by providing the `hdev` input from a different
source. Creating parallel versions would be massive duplication for no benefit since the
old invariant structure (with clause 8) is a dead end — clause 8 was provably unmaintainable.

## Algebraic Feasibility Analysis for `hdev`

### The `hdev` sorry

The single remaining sorry in the 1-stranger maintenance chain is at
`SplitStranger.lean:699-703`:

```lean
have hdev : (Int.natAbs (↑(bags (level - 1) (idx / 2) |>.filter
    (fun i ↦ (perm i).val < (idx / 2) * bagSize (2 ^ k) (level - 1) +
      bagSize (2 ^ k) ((level - 1) + 1))).card -
    ↑((bags (level - 1) (idx / 2)).card / 2)) : ℚ) ≤
  cnativeCoeff A lam ε * bagCapacity (2 ^ k) A ν t (level - 1) := by sorry
```

This bounds: `|C - ⌊b/2⌋| ≤ cnativeCoeff * cap(level-1)` where `C` = items in
parent bag D with `perm < boundary`, `b = |D|`.

### Full-capacity case (b = bagSize)

At full capacity (`b = bagSize(level-1) = n/2^(level-1)`), the bijectivity of perm
gives `out_L + out_R = s_lo + s_hi` (items outside B with perm in the parent's
native range exactly equals the stranger count). This yields:

- `|out_R - out_L| ≤ out_L + out_R = s_lo + s_hi`
- `|s_lo - s_hi| ≤ s_lo + s_hi`
- `|C - b/2| = |(s_lo - s_hi + n_L - n_R)/2| ≤ s_lo + s_hi ≤ λ * cap(level-1)`

So the bound holds if `λ ≤ cnativeCoeff`. For Seiferas parameters (λ = ε = 1/100):
`λ = 0.01 < cnativeCoeff ≈ 0.036` ✓ with 3.6× slack.

### `SatisfiesConstraints` does NOT imply `λ ≤ cnativeCoeff`

Counterexample: `λ = 0.014`, `ε = 0.001`, `A = 10`, `ν = 0.81`.

- `SatisfiesC3`: `4*0.014*10 + 5/20 = 0.81 ≤ 0.81` ✓
- `SatisfiesC4_gt1`: `2*10*0.001 + 1/10 = 0.12 ≤ 0.81` ✓
- `SatisfiesC4_eq1`: `0.001622 ≤ 0.014*0.81 = 0.01134` ✓
- `cnativeCoeff = 0.001/2 + 2*0.014*0.001*100/(1-0.0004) + 1/99 ≈ 0.01340`
- **`λ = 0.014 > 0.01340 = cnativeCoeff`** ✗

The bound `|C - b/2| ≤ λ*cap` at full capacity is tight (achievable when all
strangers are on one side: `s_lo = λ*cap`, `s_hi = 0`, `out_L = 0`,
`out_R = s_lo + s_hi`). So the full-capacity triangle inequality alone doesn't
suffice for all valid parameters.

### Sub-capacity case (b < bagSize) — the harder problem

When multiple tree levels are active simultaneously, bags can be sub-capacity
(`b < bagSize`). This happens because `uniform_size + items_partition` only force
full capacity when a single level is active; with two or more active levels,
total items `n` are split between them.

At sub-capacity, `out_L + out_R = bagSize(level-1) - b + s_lo + s_hi`, which can
be much larger than `s_lo + s_hi`. The imbalance `|out_R - out_L| = |n_L - n_R|`
is no longer controlled by the stranger bound alone.

**Worst case:** When `b ≤ bagSize(level)/2` and `s_lo = s_hi = 0`, all `b` native
items can have perm values in one half of the parent's range (say `[lo, boundary)`).
Then `n_L = b`, `n_R = 0`, `C = b`, and `|C - b/2| = b/2`.

With `items_le_cap` (b ≤ cap), this gives `|C - b/2| ≤ cap/2`. But
`cnativeCoeff * cap ≈ 0.036 * cap`, so `cap/2 ≫ cnativeCoeff * cap`. **The
bound fails for sub-capacity bags unless the imbalance is otherwise constrained.**

This scenario is not pathological — it's consistent with the abstract invariant
(0 strangers at any level, valid partition, uniform size).

### The three-source analysis must bound out_R − out_L

The items contributing to `out_L` and `out_R` (items outside the parent bag B
with perm in the parent's native range) come from three sources:

1. **Subtree** (levels l+1, l+3, ...): Items in B's subtree bags whose perm values
   are in [lo, hi). Native items at these levels are naturally balanced between
   left and right halves (their native ranges subdivide [lo, hi) symmetrically).
   The imbalance comes from strangers at these levels — bounded by the subtree
   stranger sum `2λεA²/(1-(2εA)²) * cap(l-1)`.

2. **Above** (levels l-3, l-5, ...): Items at ancestor levels with perm in [lo, hi).
   These items could be entirely on one side. Bounded by total items at ancestors:
   `cap(l-1)/(A²-1)`.

3. **Sibling subtrees** (same level, different index): Items in sibling bags at
   level l-1 with perm in [lo, hi). These are 1-strangers of their host bag.
   However, bounding how many of each sibling's strangers have perm specifically
   in [lo, hi) requires a global argument — the per-sibling stranger bound doesn't
   suffice because [lo, hi) is just one of many possible target ranges.

**Key insight:** The paper's benchmark comparison avoids decomposing `out_R - out_L`
by source. Instead, it bounds the **C-native excess** (`actual C-native in D −
d/2`) as a single quantity via the subtree + above argument. The excess counts
items displaced from C's subtree into D, which is bounded by the subtree stranger
sum plus the above items sum. This works because:
- Items displaced FROM C's subtree (strangers there) end up SOMEWHERE — possibly
  in D, contributing to C-native excess.
- Items AT above levels with perm in C's range are additional C-native items in D
  (by displacement).
- The total displacement ≤ subtree strangers + above items = `cnativeCoeff * cap(l-1)`.

### `bagCapacity` increases with level

The formalization uses `bagCapacity n A ν t level = n * ν^t * A^level` with `A > 1`,
so capacity INCREASES at deeper levels. This matches the paper's convention where
the capacity bound is loose at deep levels (many items allowed per bag) and tight
at shallow levels.

This is correct but counterintuitive: `bagSize = n/2^level` DECREASES with level,
while `bagCapacity = n * ν^t * A^level` INCREASES with level (for small t).
The stranger bound `λ * ε^(j-1) * bagCapacity` is a BUDGET that the actual stranger
count must satisfy; it's not a tight estimate.

At high t, `ν^t → 0` makes `bagCapacity` small at all levels. The convergence of
the sorting network relies on this decay.

### Recommended proof approach for `hdev`

**Option A: Add `lam ≤ ε` to `SatisfiesConstraints`.**
The paper uses `λ = ε`. With `λ ≤ ε`, the full-capacity bound gives
`|C - b/2| ≤ λ*cap ≤ ε*cap`. Then `ε ≤ cnativeCoeff` when `λ ≤ ε` because
`cnativeCoeff ≥ ε/2 + 2λεA²/(1-(2εA)²) + 1/(A²-1)`, and the subtree and above
terms provide sufficient margin for all valid parameters.

Verified: for ALL valid A > 1 with C4_gt1 constraint `2Aε + 1/A < 1`,
the ratio `cnativeCoeff/ε > 1` when `λ = ε` (checked numerically for
A ∈ {1.1, 1.5, 2, 3, 10} at max ε from C4_gt1).

But this only handles full capacity. The sub-capacity case requires the
three-source analysis to bound the imbalance, which is independent of λ vs ε.

**Option B: Prove the benchmark comparison directly.**
This is the paper's actual approach. Instead of bounding `|C - b/2|` via the
triangle inequality on `(s_lo - s_hi) + (n_L - n_R)`, bound the C-native excess
directly via the subtree + above displacement argument. This handles both
full-capacity and sub-capacity cases because the displacement bound doesn't
depend on `b`.

**Option C: Add a deviation-like field back to the invariant.**
If the bound can't be proved from the abstract invariant, re-introduce
`deviation_bound` as a field but with a DIFFERENT maintenance proof that avoids
the previously-failed `three_source_native_bound`. This is circular-sounding but
the circularity might be breakable with a different proof structure.

**Recommendation:** Option B (paper's approach). The previous analysis showed that
the three-source bound is mathematically correct and empirically validated. The
formalization challenge is expressing the benchmark comparison argument in Lean,
not the mathematics itself.
