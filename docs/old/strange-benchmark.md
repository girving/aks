> **OBSOLETE:** Superseded by docs/bags.md. Benchmark comparison analysis from earlier formulation.

# Benchmark Comparison for `h_deficit` (Strange.lean)

## Goal

Prove the sorry at `h_deficit` in `parent_stranger_eq1_le`:

```
max (0 : ℚ) (↑half_D - ↑b_native) ≤
    (2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2)
     + 1 / (8 * p.A ^ 3 - 2 * p.A)) * cap
```

This bounds the excess of C-native items over the "fair share" half_D
in D's register at stage t, following Seiferas (2009) Section 5.

## Setup

- B at level ℓ (`b.l`), currently empty (alternating levels)
- D = B.parent at level ℓ−1, has `parent_regs` items
- C = B.sibling at level ℓ, currently empty
- `half_D = parent_regs.card / 2`, `n_local = 2 * half_D`
- `b_native` = count of B-native items among n_local inner items of D
- `cap = capacity p k t b.l`

## Partition identity

Among D's n_local inner items, each is exactly one of:
- B-native (value in B's interval)
- C-native (value in C's interval)
- D-stranger (value outside D's interval)

So `b_native + c_native + s_D = n_local = 2 * half_D`, giving:

```
half_D - b_native = (c_native - half_D) + s_D
```

## Benchmark distribution (Seiferas Section 5)

The benchmark has the same bagCard at every level as the actual distribution, but:
- For each bag C' at level ℓ: all items in C's subtree are C'-native
- D has exactly half_D items native to each child (B and C)

In the benchmark: c_native = half_D (zero excess), s_D = 0 (no strangers in D).

## Where does the excess come from?

To go from benchmark to actual, items are rearranged (same bag sizes, different
value assignments). The excess `half_D - b_native` has two sources:

### Source (i): C-native items from levels above D

In the benchmark, some C-native items sit in ancestor registers above D.
In the actual distribution, more or fewer may be there. The contribution
to c_native in D from levels above is bounded by:

```
Σ_{l < ℓ-1} bagCard(l) / 2^(ℓ - l)
```

The dominant term l = ℓ−1 gives bagCard(ℓ−1)/2 = half_D, which cancels.
The remaining terms (l < ℓ−1) use `bagCard_le_capacity` and alternating
levels (`bagCard_odd_eq_zero`): only odd distances j = ℓ−l contribute, giving:

```
Σ_{j=3,5,7,...} cap / (2A)^j = cap / (8A³ − 2A)
```

### Source (ii): Non-C-native items in C's subtree

In the benchmark, C's subtree has only C-native items. In reality, some
items in C's subtree are not C-native. Each such item displaced a C-native
item, which may have ended up in D's register.

**Key fact**: For a descendant b' of C at distance d, an item in b' that is
not C-native has value outside C's interval. C = b'.ancestor(d), so
"not C-native" = `b'.Strange (d+1)` (not native to ancestor at distance d).

By the IH (Clause 4): `b'.strangers(d+1) ≤ γ · ε^d · cap(ℓ+d)`.

**Why ε^d, not ε^(d-1)**: The naive attempt uses `Strange d` (giving ε^(d-1)),
which produces a bound ~100× too large (0.2·cap vs budget 0.002·cap).
The fix: C is ancestor at distance d from b', so "not C-native" requires
`Strange (d+1)`, not `Strange d`. The `Strange j` definition checks
`ancestor (j-1)`, so `Strange (d+1)` checks `ancestor d` = C. This shifts
the exponent from ε^(d-1) to ε^((d+1)-1) = ε^d, matching the paper.

With `cap(ℓ+d) = cap · A^d` and alternating levels (only odd d contribute):

```
Σ_{d=1,3,5,...} 2^d · γ · ε^d · cap · A^d
= γ · cap · Σ_{d=1,3,...} (2εA)^d
= 2γεA · cap / (1 − (2εA)²)
```

## Conservation argument

By bijectivity of perm_t, total C-native items = C.size = 2^(k−ℓ).
From `bagCard_total`: Σ_l 2^l · bagCard(l) = 2^k.

Items in C's subtree: at level l' = ℓ+d, there are 2^d descendant bags of C,
each with bagCard(l') items. Total: Σ_{d≥0} 2^d · bagCard(ℓ+d).

Define:
- `total_sub` = items in C's subtree = Σ_{d≥0} 2^d · bagCard(ℓ+d)
- `non_C_sub` = non-C-native items in C's subtree (= source ii)

Then:
```
C.size − total_sub = Σ_{l < ℓ} bagCard(l) / 2^(ℓ−l)
```
(derived from bagCard_total by splitting the sum at level ℓ).

And:
```
c_native_in_D ≤ C.size − (total_sub − non_C_sub)
             = (C.size − total_sub) + non_C_sub
             = Σ_{l < ℓ} bagCard(l)/2^(ℓ−l) + non_C_sub
```

The l = ℓ−1 term gives half_D (assuming bagCard(ℓ−1) is even; see parity below).
So: `c_native − half_D ≤ source(i) + source(ii)`.

The s_D term: D-strangers in D's register have values outside D's interval.
These are a subset of the items "not in the benchmark" — they contribute to
the deficit but are already counted in the conservation: s_D items in D
displace D-native items, some of which end up in C's subtree as non-C-native
items (already counted in source ii) or in B's subtree (reducing c_native
by symmetry).

## Parity issue

`half_D = bagCard(ℓ−1) / 2` (integer division). If bagCard(ℓ−1) is odd,
half_D = (bagCard(ℓ−1) − 1) / 2, and the conservation gives
bagCard(ℓ−1)/2 ≥ half_D with equality when even.

`bagCard_root_even` proves the root is even. Need to verify that
bagCard(ℓ−1) is even when ℓ−1 is an active level. This may follow from
the rebag recurrence: children contribute 2×splitParentCard (always even),
and parent contributes splitChildCard. If the parent's bagCard is even,
splitChildCard preserves this. Investigate `bagCard_even` lemma.

If bagCard is always even at active levels, the parity issue vanishes.
Otherwise, the +1/2 error from odd bagCard needs to be absorbed into
the coefficient budget (tight but may work since the budget has ~40% slack).

## Current proof status (updated)

The original single sorry at `hc_excess` has been factored into two independent sub-goals:

### Sorry 1: `h_subtree_bound` (source ii)

```lean
(non_C_sub_nat : ℚ) ≤ 2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2) * cap
```

where `non_C_sub_nat = (subregs pl sibling).filter(¬sibling.Native · perm_t).card`.

**Proof strategy**: Tree induction on `subregs` structure.
- At each descendant `b'` at distance `d`, non-sibling-native items = `b'.strangers(d+1)`
- IH gives `strangers(d+1) ≤ γ · ε^d · cap · A^d`
- At even `d`: `bagCard = 0` (by `bagCard_odd_eq_zero`), so 0 strangers
- Sum over odd `d`: `γ · cap · Σ (2εA)^d = 2γεA/(1-(2εA)²) · cap`
- `odd_geom_sum_le` (proved) handles the geometric series arithmetic

**Blocker**: `subregs_card_split` and `regs_disjoint_subregs` are in `Depth.lean`
which cannot be imported (circular: `Sorts.lean` imports `Strange.lean`).
Either move those lemmas to `Network.lean` or `Sizes.lean`, or reprove inline.

### Sorry 2: `h_conservation` (conservation + source i)

```lean
(↑c_card : ℚ) ≤ ↑half_D + ↑non_C_sub_nat + 1 / (8 * p.A ^ 3 - 2 * p.A) * cap
```

**Proof strategy**:
1. Bijectivity: `sibling.size` items are C-native total
2. C-native in subtree ≥ `sub_card - non_C_sub_nat`
3. `bagCard_total` gives: `sibling.size - sub_card = Σ_{l<ℓ} bagCard(l)/2^(ℓ-l)`
4. The `l = ℓ-1` term gives `bagCard(ℓ-1)/2 ≥ half_D`
5. Remaining terms ≤ `cap/(8A³-2A)` via `bagCard_le_capacity` + `bagCard_odd_eq_zero`
6. Combine: `c_card ≤ half_D + non_C_sub_nat + cap/(8A³-2A)`

**Available infrastructure** (all importable from `Sizes.lean`):
- `bagCard_total`, `bagCard_le_capacity`, `bagCard_odd_eq_zero`
- `Placement.complete`, `Placement.disjoint` (from `Defs.lean`)

### Assembly (proved)

```lean
linarith [Nat.cast_nonneg (α := ℚ) non_C_sub_nat]
```

combines `h_subtree_bound` and `h_conservation` to get `hc_excess`.

## Key lemmas needed

- `bagCard_subtree_sum`: Σ_{d=0}^{k−ℓ} 2^d · bagCard(ℓ+d) = (2^k − Σ_{l<ℓ} 2^l · bagCard(l)) / 2^ℓ
  (or equivalently: C.size − total_sub = Σ_{l<ℓ} bagCard(l)/2^(ℓ−l))
- `non_C_native_eq_stranger`: for b' descendant of C at distance d,
  non-C-native in b' ↔ b'.Strange (d+1) (uses interval containment)
- `odd_geom_sum_le` (PROVED in Strange.lean): Σ_{i<n} r^(2i+1) ≤ r/(1-r²)
- `source_above_bound`: Σ_{l<ℓ−1, active} bagCard(l)/2^(ℓ−l) ≤ cap/(8A³−2A)
- Possibly `bagCard_even` for the parity issue

## Existing infrastructure

- `bagCard_total` (Sizes.lean): conservation Σ 2^l · bagCard(l) = 2^k
- `bagCard_le_capacity` (Sizes.lean): bagCard ≤ capacity
- `bagCard_odd_eq_zero` (Sizes.lean): alternating levels empty
- `bagCard_root_even` (Sizes.lean): root bagCard is even
- `ih`: IH on strangers at stage t
- `hs_D_bound`: parent.strangers(1) ≤ γ · cap/A (already proved in context)
- `Bag.parent_native_iff` (Defs.lean): D-native ↔ B-native ∨ C-native
- `odd_geom_sum_le` (Strange.lean): geometric series for odd indices
