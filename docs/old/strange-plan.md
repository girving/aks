> **OBSOLETE:** Superseded by docs/bags.md. h_deficit proof strategy from earlier formulation.

# h_deficit Proof Strategy

## Context

In `AKS/Bags/Strange.lean`, the `parent_stranger_eq1_le` theorem bounds 1-strangers
in bag B after one stage. The proof decomposes source3 (items native to parent D but
native to sibling C, incorrectly sent to B) into:

```
source3 ≤ ε·(d/2) + max(0, d/2 - b_native)     [h_decomp, proved]
```

where `d = parent_regs.card`, `half_D = d/2`, and `b_native` counts B-native items
among the separator's domain.

The `h_deficit` sorry bounds the "B-native deficit":

```
max(0, half_D - b_native) ≤ (2γεA/(1-(2εA)²) + 1/(8A³-2A)) · cap
```

## Seiferas's Argument (Section 5, pp. 5-6)

Compare actual distribution with a **benchmark distribution** where each bag C' at
B's level has exactly C'-native items below C', and d/2 C'-native items in D' (parent
of C'). Excess C-native items in D beyond d/2 can only come from:

### Source (i): C-native items on levels above D

At level i above C (i.e., at C's ancestor at distance i), there are `2^i` bags at C's
level. The total items at that level is at most `b/A^(2i+1)` (capacity at distance 2i+1
from B). Each such C' contributes `1/2^i` of its items as C-native, giving:

```
b/(2A)³ + b/(2A)⁵ + b/(2A)⁷ + ...
= b/((2A)³(1 - 1/(2A)²))
= b/(8A³ - 2A)
```

### Source (ii): Strangers in C's subtree displacing C-native items

By Clause (4) of the invariant (the induction hypothesis), each bag C' in C's subtree
at distance j from C has at most `γ·ε^(j-1)·capacity(C')` j-strangers. These strangers
displace C-native items upward. Summing over the subtree:

```
2λεbA + 8λε³bA³ + 32λε⁵bA⁵ + ...
= 2λεbA(1 + (2εA)² + (2εA)⁴ + ...)
< 2λεbA/(1 - (2εA)²)
```

where `λ = γ` in our notation and `b = cap`.

### Combined bound

```
half_D - b_native ≤ 2γεA·cap/(1-(2εA)²) + cap/(8A³-2A)
```

which is exactly the `h_deficit` statement.

## Proof Plan

### Step 1: Subtree stranger displacement (source ii)

For each level `j` below C in C's subtree, the IH gives:
- At level `b.l + j`, there are `2^j` bags that are descendants of C
- Each has ≤ `γ·ε^j·capacity(p,k,t,b.l+j)` 1-strangers (by IH at j+1 level)
- `capacity(p,k,t,b.l+j) = cap · A^j`
- Total strangers in C's subtree at distance j: `2^j · γ·ε^j · cap·A^j = γ·cap·(2εA)^j`
- Summing: `γ·cap·Σ_{j=1}^{k-b.l} (2εA)^j < γ·cap·2εA/(1-(2εA)²)·...`

Wait — we need to be more careful. Each stranger in C's subtree displaces one C-native
item from its expected position. The displacement is measured relative to the benchmark.

Actually, the key insight is simpler: `b_native` counts items in D that are B-native.
The deficit `half_D - b_native` equals the count of non-B-native items in the first
half of D. These are either:
- (a) Strangers to D (already handled by source 2)
- (b) C-native items that ended up in D

The C-native items in D beyond d/2 come from sources (i) and (ii) above.

### Step 2: Equidistribution from above (source i)

Items native to C at levels above D: at each ancestor of D at distance i,
there are items distributed to D. The share native to C is bounded by `cap/A^(2i+1)`.
Geometric series gives `cap/(8A³-2A)`.

### Implementation approach

Factor into two lemmas:
1. `subtree_stranger_displacement`: bounds source (ii) using IH
2. `above_equidistribution`: bounds source (i) using capacity arithmetic

Both are pure arithmetic given the IH and capacity structure.

**Risk assessment**: MEDIUM. The geometric series arguments are standard but
connecting them to the concrete `b_native` count requires careful bookkeeping.
The key gap is formalizing "benchmark distribution" — we may need to avoid it
entirely and work with direct counting arguments.

## Parameter Constraints

The accumulated constraints from Seiferas (2009) Section 5, p.6:

| Constraint | Name | Origin |
|---|---|---|
| `A > 1` | `hA` | Already in `Params` |
| `0 < ν < 1` | `hν_pos`, `hν_lt` | Already in `Params` |
| `0 < ε < 1` | `hε_pos`, `hε_lt` | Already in `Params` |
| `0 < γ ≤ 1/2` | `hγ_pos`, `hγ_half` | Already in `Params` |
| `(2εA)² < 1` | `h2εA` | Convergence of geometric series |
| `ν ≥ 4γA + 5/(2A)` | `hC3` | Clause 3 capacity bound |
| `2Aε + 1/A ≤ ν` | `hC4_gt1` | j≥2 stranger decay |
| `2γεA + εγ/A + ε/(2A) + 2γεA/(1-(2εA)²) + 1/(8A³-2A) ≤ γν` | `hC4_eq1` | j=1 master constraint |

These are now fields in `Params` (Network.lean), avoiding threading through every theorem.

### Concrete satisfying values (Seiferas p.6)

`A = 10, γ = 1/100, ε = 1/100, ν = 13/20`

Verification:
- `(2·(1/100)·10)² = (1/5)² = 1/25 < 1` ✓
- `4·(1/100)·10 + 5/(2·10) = 2/5 + 1/4 = 13/20 ≤ 13/20` ✓
- `2·10·(1/100) + 1/10 = 1/5 + 1/10 = 3/10 ≤ 13/20` ✓
- Master: `2·(1/100)·(1/100)·10 + (1/100)·(1/100)/10 + (1/100)/(20) + 2·(1/100)·(1/100)·10/(1-1/25) + 1/(8000-20)`
  = `1/500 + 1/100000 + 1/2000 + (1/500)·(25/24) + 1/7980`
  = `0.002 + 0.00001 + 0.0005 + 0.002083... + 0.000125...`
  ≈ `0.004718` ≤ `(1/100)·(13/20)` = `0.0065` ✓

Satisfiability proved formally via `seiferasParams` in `Network.lean` (all fields `decide +kernel`).

## Proved Infrastructure

### Phase 2: Parameter constraints as Params fields (done)
The four constraints (`h2εA`, `hC3`, `hC4_gt1`, `hC4_eq1`) are now fields of `Params`.
All callers updated: `Sizes.lean`, `Strange.lean`, `Sorts.lean`.

### Phase 3: Satisfiability (done)
`seiferasParams : Params` with `γ=1/100, ε=1/100, ν=13/20, A=10`, all proofs by `decide +kernel`.

### h_deficit partial progress (Phase 4)

Proved:
- `max_le` split: the `max(0, ...)` reduces to two goals: `0 ≤ RHS` (by positivity)
  and the core bound `half_D - b_native ≤ RHS`
- `hs_D_bound`: D's 1-stranger count ≤ `γ·cap/A` (by IH on parent with capacity arithmetic)
- `Bag.parent_native_iff` (Defs.lean): `parent.Native ↔ b.Native ∨ sibling.Native`
  (children partition parent's interval; needed for the partition identity)

### Remaining sorry

The core bound `half_D - b_native ≤ (2γεA/(1-(2εA)²) + 1/(8A³-2A)) · cap` in
`parent_stranger_eq1_le` at line ~2268 of Strange.lean. This requires:

1. **Partition identity**: `b_native + c_native + s_embed = n_local` where `c_native`
   counts sibling-native items and `s_embed` counts D-strangers among the separator's
   domain. Uses `Bag.parent_native_iff` (proved).

2. **s_embed bound**: `s_embed ≤ s_D ≤ γ·cap/A` (injection from n_local items into
   parent_regs, using `hs_D_bound`).

3. **C-native excess bound** (the hard part):
   `c_native - half_D ≤ (source i) + (source ii) - s_embed`
   Requires the global tree counting argument from Seiferas Section 5.

**Risk**: HIGH. Steps 1-2 are straightforward Lean proofs. Step 3 requires new
infrastructure for reasoning across the entire bag tree (summing over descendants
of C, summing over ancestors of D). This is a months-level task.
