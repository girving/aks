> **OBSOLETE:** Superseded by docs/bags.md. Alternative stranger bound approaches from earlier formulation.

# Alternative Approaches for the Stranger Bound (Clause 4)

## Context

The 4th invariant clause of Seiferas (2009) — the stranger bound — is sorry'd
in `AKS/Bags/Strange.lean`. The j≥2 case is straightforward; the j=1 case
requires bounding the number of sibling-native (C-native) items that end up in
bag B after a separator stage.

Seiferas proves the j=1 case via a **benchmark distribution**: a hypothetical
reference distribution with the same bag sizes but symmetric native placement.
The deviation from benchmark is bounded by two sources: strangers in C's
subtree (geometric series from IH) and items at ancestor levels (capacity
bounds). A previous formalization attempt added a "deviation bound" clause
(clause 8) to the invariant but failed because the maintenance proof was
provably too loose (14× gap — see `clause4.md`).

This document records three alternatives that avoid the benchmark distribution
construct.

## Alternative 1: Direct Conservation Counting (Recommended)

**Same math as Seiferas, different framing.** Instead of constructing a
benchmark distribution object, use a direct counting argument based on
conservation of native items.

### Core argument

1. **Conservation**: Total C-native items in the system = `C.size = 2^(k−ℓ)`
   (by bijectivity of perm). This is a global invariant, not per-bag.

2. **Subtree accounting**: Among items in C's subtree (levels ℓ, ℓ+1, ...),
   at least `total_sub − non_C_sub` are C-native, where `non_C_sub` counts
   non-C-native items. By the IH, non-C-native items at a descendant bag b'
   at distance d from C are `(d+1)`-strangers in b'. Clause 4 bounds these:
   `b'.strangers(d+1) ≤ γ·ε^d·cap(b'.l)`. Summing over C's subtree with
   alternating levels gives:
   ```
   non_C_sub ≤ 2γεA·cap / (1 − (2εA)²)
   ```

3. **Items above C**: C-native items outside C's subtree are at ancestor
   levels. At each ancestor level ℓ', C's ancestor bag has ≤ `cap(ℓ')` items.
   In the worst case, ALL are C-native. Summing over ancestor levels
   (with alternating emptiness, distances 3, 5, 7, ...):
   ```
   above ≤ cap/A³ + cap/A⁵ + ... = cap/(A³ − A)
   ```
   This is the **weakened bound** (no equidistribution needed). The paper's
   tighter bound `cap/(8A³ − 2A)` requires equidistribution — a construction
   symmetry not captured by the current invariant. The weakened bound still
   satisfies the master constraint with 1.14× slack.

4. **Assembly**: From conservation,
   ```
   c_native_in_D ≤ C.size − (total_sub − non_C_sub)
   ```
   The ℓ−1 term in the ancestor sum gives the "fair share" `≈ half_D`.
   The remaining terms give `source(i) + source(ii)`:
   ```
   c_native_in_D − half_D ≤ above + non_C_sub
   ```

### Key sub-lemmas needed

| Lemma | Risk | Description |
|-------|------|-------------|
| `conservation_identity` | LOW | `Σ_b (C-native items in b) = C.size`, from perm bijectivity |
| `subtree_stranger_bound` | MEDIUM | Sum over C's subtree: non-C-native = (d+1)-strangers, geometric series |
| `above_capacity_bound` | LOW–MEDIUM | Sum over ancestor levels: items ≤ capacity, geometric series |
| `assembly` | LOW | Combine conservation + subtree + above bounds |

### Pros
- Closest to the paper's mathematics
- Reuses existing infrastructure (`bagCard_total`, `bagCard_le_capacity`, `bagCard_odd_eq_zero`)
- No additional invariant clauses needed
- Well-analyzed in existing docs (`strange-benchmark.md`, `strange-plan.md`)

### Cons
- Still requires a tree-wide counting argument (summing over descendants/ancestors)
- Months-level effort but tractable

### Parameter constraint

The weakened master constraint (field `hC4_eq1` of `Params`):
```
2γεA + εγ/A + ε/(2A) + 2γεA/(1−(2εA)²) + 1/(8A³−2A) ≤ γν
```

With the weakened above bound `1/(A³−A)` replacing `1/(8A³−2A)`:
```
LHS = 0.005693 < 0.0065 = RHS  (A=10, γ=ε=1/100, ν=13/20)
```

## Alternative 2: Aggregate Potential Function

Define a **global potential** aggregating stranger counts across all bags,
weighted so the j=1 case is amortized across the tree.

### Definition

```
Φ(t) = Σ_{b active} Σ_{j≥1} (1/ε)^(j−1) · strangers(j, b, t)
```

### Approach

Show `Φ(t+1) ≤ ν' · Φ(t)` for some `ν' < 1`. Per-bag bounds follow: since
each term is non-negative,
```
(1/ε)^(j−1) · strangers(j, b, t) ≤ Φ(t) ≤ (ν')^t · Φ(0)
```
giving `strangers(j, b, t) ≤ ε^(j−1) · Φ(0) · (ν')^t`.

### Key insight

The imbalance issue that plagues the per-bag j=1 argument is **amortized**:
excess C-native items in one bag correspond to deficits elsewhere. The global
potential captures the total displacement, which decreases because the separator
reduces disorder at every bag simultaneously.

### Pros
- Avoids per-bag j=1 reasoning entirely
- All j levels handled uniformly by the potential decrease
- Potentially simpler induction structure

### Cons
- Novel approach (not in any paper)
- Weight function design requires mathematical validation
- `Φ(0)` depends on initial state (needs separate analysis; at t=0 only root
  has items, so Φ(0) is computable but depends on the initial permutation)
- May not easily give tight per-bag bounds: Φ aggregates over bags with
  different capacities, so extracting per-bag bounds requires relating
  individual terms to the aggregate
- Capacity varies by level: the potential needs level-dependent weighting
  to account for this

### Risk: HIGH
Unexplored territory. The weight function must satisfy:
1. Potential decreases each stage (requires all sources to be accounted for)
2. Per-bag bounds are recoverable (requires careful relationship between
   aggregate and individual terms)
3. The decay rate ν' must be < 1 (requires the parameter constraints to
   provide enough slack)

Mathematical validation needed before any formalization effort.

## Alternative 3: Strengthened Invariant with "Native Balance" Clause

Add a 5th clause bounding the imbalance of child-native items in each parent:

```
∀ parent D with children B, C:
  |c_native_in_D − bagCard(D)/2| ≤ δ · capacity(D)
```

where δ is a small constant (the `cnativeCoeff` from existing code).

### How it helps

The j=1 stranger bound follows easily from the balance clause:
```
c_native_in_B_portion ≤ ε · bagCard(D) + δ · capacity(D)
```
The ε term is the separator error; the δ term is the pre-existing imbalance.

### Maintaining the balance clause

After a stage, parent D receives items from:
- Children's toParent (fringe items from D.left and D.right)
- Grandparent's toLeft/toRight (from D's parent E)

The new balance is controlled by:
1. Separator's approximate sorting reduces imbalance by factor ε
2. IH on stranger counts bounds influx of misplaced items
3. IH on balance clause bounds pre-existing imbalance at E

### Connection to previous attempt

The old clause 8 (`deviation_bound`) used this approach but the maintenance
proof (`three_source_native_bound`) decomposed `|out_R − out_L|` into three
absolute values that were individually too loose (14× gap). A successful
version needs a **different decomposition** — e.g., bounding the signed sum
directly rather than splitting into absolute values.

### Pros
- Clean separation: j=1 case becomes trivial once balance is established
- Explicit invariant makes the proof structure transparent

### Cons
- May reproduce the same failure as the old clause 8 if the maintenance
  proof faces the same looseness issue
- Requires careful decomposition of the balance maintenance (different
  strategy from the failed `three_source_native_bound`)
- Adds complexity to the invariant (5 clauses instead of 4)

### Risk: MEDIUM–HIGH
The maintenance proof is the bottleneck. If a different decomposition
(signed sum rather than absolute values) works, this approach is viable.
If not, it fails for the same reasons as the old clause 8.

## Comparison

| Criterion | Alt 1: Conservation | Alt 2: Potential | Alt 3: Balance Clause |
|-----------|--------------------|-----------------|-----------------------|
| Mathematical novelty | LOW (paper's math) | HIGH (novel) | LOW (variant of old attempt) |
| Risk | MEDIUM | HIGH | MEDIUM–HIGH |
| Infrastructure needed | Subtree sums, ancestor sums | Weight design, aggregate decay | Balance maintenance |
| Additional invariant | None | None (external) | Yes (5th clause) |
| Closest to paper | Yes | No | Partially |
| Previous work | Extensive analysis in docs | None | Failed attempt (clause 8) |

## Decision

**Alternative 1 (Direct Conservation Counting)** is the recommended path.
