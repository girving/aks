# Bag-Tree Sorting (`AKS/Bags/`, `AKS/Separator/`)

Seiferas (2009) separator-based sorting network correctness proof.
Replaces the original AKS ε-nearsort + tree-distance wrongness argument
with a cleaner bag-tree abstraction using (γ,ε)-separators and a single
potential function (stranger count).

**Primary source:** Seiferas, "A Further Simplified AKS Sorting Network" (2009),
`docs/seiferas.pdf`. See also Paterson (1990), `docs/paterson.pdf`.

## Overview

The construction builds an O(log n)-depth sorting network for n = 2^k wires.
Wires are organized into a **binary bag tree** of depth k. At each **stage**,
separators split each bag's contents and redistribute to parent/children.
After O(k) stages, all items are native to their bags, and small bitonic
sorts at the leaves finish the job.

Correctness is proved via the **stranger bound**: at every stage t, the number
of j-strangers (items misplaced by j levels) in each bag decays geometrically:
`strangers ≤ γ · ε^(j-1) · capacity`. After enough stages, capacity shrinks
below 1, forcing zero strangers and hence a sorted output.

## File Structure

### Core definitions

| File | Purpose |
|------|---------|
| `Bags/Defs.lean` | `Bag k`, `Placement k`, `Native`, `Strange`, `strangers` |
| `Bags/Network.lean` | `BagSplit`, `split`, `separate`, `stage`, `stages`, `seiferasNetwork` |
| `Bags/Params.lean` | `Params` structure (γ, ε, ν, A constraints), `seiferasParams` concrete values |

### Size and depth analysis

| File | Purpose |
|------|---------|
| `Bags/Sizes.lean` | `bagCard` recurrence, `bagCard_eq_card`, `bagCard_le_capacity` (all proved) |
| `Bags/SplitCard.lean` | Pure arithmetic for parent/child size after split (all proved) |
| `Bags/Depth.lean` | `seiferasNetwork` has O(log n) depth (all proved) |

### Stranger bound (correctness)

| File | Purpose |
|------|---------|
| `Bags/Strange.lean` | Main `stranger_bound` theorem, induction on stage number |
| `Bags/Filter.lean` | Comparator filter preservation, `kick_stranger_le` |
| `Bags/SepBridge.lean` | Separator → stranger bridge, `parent_stranger_j2_le` (sorry) |
| `Bags/Source3.lean` | j=1 stranger bound `parent_stranger_eq1_le` (sorry) |
| `Bags/Subtree.lean` | Spillover and subtree non-native bounds |

### Final assembly

| File | Purpose |
|------|---------|
| `Bags/Sorts.lean` | `seiferasNetwork` sorts: stranger bound → zero strangers → sorted |
| `Separator/Defs.lean` | `SepInitial`, `SepFinal`, `IsApproxSep`, `IsSeparator` |
| `Separator/Family.lean` | `SeparatorFamily γ ε` structure |
| `Separator/FromHalver.lean` | `halverToSeparator` (halver → separator induction) |
| `Seiferas.lean` | Top-level `network n`, `network_sorts`, `network_depth_le` |

## Key Concepts

### Bags and nativeness

A `Bag k` is a node in a binary tree of depth k. Each bag has a **native
interval** `[b.lo, b.hi)` of sorted ranks. A register `r` is **native** to
bag `b` under permutation `perm` if `(perm r).val` falls in `b`'s interval.

The construction uses a **register-first convention**: bags own registers (wire
positions), not values. A permutation `perm : Fin (2^k) → Fin (2^k)` maps
registers to their sorted ranks.

### Strangeness

Register `r` is **j-strange** to bag `b` if it is not native to `b`'s
(j-1)-th ancestor. Equivalently, it's misplaced by at least j levels in
the tree. Key properties:
- 0-strangers = all items (vacuously)
- (j+1)-strange → j-strange (monotonicity)
- j-strangers at parent = (j+1)-strangers at child (`strangers_parent_eq`)
- 1-strangers decompose into: parent-strangers OR sibling-natives (`one_strange_decomp`)

### Stages and splitting

Each stage applies separators to all non-empty bags, then splits:
- `split` divides a bag's registers into `toParent` (fringe), `toLeft`, `toRight`
- `stageRegs` reassembles: children send fringe to parent, parent sends halves down
- Parity convention: `(t + level) % 2 ≠ 0` → bag is empty

### Capacity

The capacity formula `cap(t, l) = 2^k · ν^t · A^l` bounds bag sizes
geometrically. Parameters satisfy constraints in `Params`:
- `γ · A^2 > 1` (capacity grows enough per level)
- `ν ≥ 4 · γ · A + 5 / (2 · A)` (stage decay rate)
- `0 < γ ≤ 1/2`, `0 < ε`, `ν < 1`, `A > 1`

Concrete values: `seiferasParams` sets γ = ε = 1/99, A = 10, ν = 0.65.

## Proof Status

### Fully proved (0 sorry)

- All of `Bags/Defs.lean`, `Network.lean`, `Sizes.lean`, `SplitCard.lean`,
  `Params.lean`, `Depth.lean`, `Filter.lean`, `Subtree.lean`
- `Separator/Defs.lean`, `Family.lean`, `FromHalver.lean`
- `stranger_bound` (main theorem in `Strange.lean`, by induction)
- `seiferasNetwork` depth bound
- `Seiferas.lean` top-level assembly

### Remaining sorries (2 theorems)

Both are in the **separator-quality bridge** — connecting separator properties
to stranger counting:

| Theorem | File | Risk | Description |
|---------|------|------|-------------|
| `parent_stranger_j2_le` | `SepBridge.lean` | MEDIUM | j ≥ 2: separator ε-filtering bounds parent strangers |
| `parent_stranger_eq1_le` | `Source3.lean` | MED-HIGH | j = 1: separator + equidistribution for 1-strangers |

Both pass empirical validation (0 violations across all tested parameters).
The j ≥ 2 case follows from separator filtering: applying `IsSeparator`
restricts the fraction of misplaced items. The j = 1 case is harder because
1-strangers are "almost native" — they're native to the parent but assigned
to the wrong child, requiring a sibling-native decomposition argument.

## Data Flow

```
MGG Expander (8-regular on (Z/nZ)²)
    ↓  Halver/FromExpander.lean
ε-Halver Family (all sizes, proved)
    ↓  Separator/FromHalver.lean
(γ, ε)-Separator Family (iterated halving, proved)
    ↓  Bags/Network.lean
Bag-tree stages (separate + split at each bag)
    ↓  Bags/Sizes.lean + Strange.lean
Stranger bound (j-strangers ≤ γ · ε^(j-1) · capacity)
    ↓  Bags/Sorts.lean
Zero strangers after enough stages → sorted subtrees
    ↓  Seiferas.lean
O(log n)-depth sorting network for all n
```

## Rust Validation

Empirical tests in `rust/` mirror the Lean definitions:
- `test-bags.rs` — Full bag-tree simulation with adversarial separators
- `test-invariant-maintenance.rs` — All 10 invariant clauses through stages
- `test-split-hypotheses.rs` — All 11 split hypotheses
- `test-stranger-bound.rs` — Induction step of stranger bound
- `test-sorting-network-e2e.rs` — End-to-end sorting correctness
- `test-spillover*.rs` — Spillover/deficit bounds
- `test-benchmark-comparison.rs` — Seiferas benchmark comparison
