> **OBSOLETE:** Irregular graph path was blocked by a false theorem. Replaced by pow2 equal-fiber contraction.

# Irregular Expander → Halver Pipeline

**STATUS: SUPERSEDED.** The irregular graph path was blocked by `graph_exists_halver_depth_le`
being mathematically false (see below). It has been replaced by the **power-of-2 equal-fiber
contraction** path (`seiferas_sorting_networks_exist_pow2` in `AKS/Seiferas.lean`), which
uses `RegularGraph.contractDivisible` to produce regular contracted graphs, avoiding the
degree ratio issue entirely. The dead code (`contracted_squareIter_spectralGap`,
`graph_halverFamily_exists`, `seiferas_sorting_networks_exist_graph`,
`graph_exists_halver_depth_le`, `graphExpanderHalverFamily`) has been deleted.

## Original Goal

Wire proved `explicit_expanders_graph` (gives `Graph n` at every positive size via contraction) into the Seiferas sorting network pipeline, eliminating the dependency on sorry'd `explicit_expanders_exist_zigzag`.

## Strategy

- Add alternate "Graph" versions alongside existing proved `RegularGraph` lemmas
- Don't modify existing proofs; once Graph chain is complete, delete old versions
- Square at `RegularGraph` level before contracting (no need for `Graph.square`)

### Pipeline

```
zigzagFamily → RegularGraph, gap ≤ c
  → squareIter' → RegularGraph, gap ≤ c^(2^k) < 1/4
  → .toGraph.contract → Graph n, gap ≤ c^(2^k), degree ratio ≤ 2
  → graphExpanderHalverFamily → HalverFamily ε d
  → halverToSeparatorFamily' → SeparatorFamily
  → separatorSortingNetwork → O(n log n) sorting network
```

## Status Summary

| WP | Description | Status | File |
|----|-------------|--------|------|
| A | Graph Tanner Bound | **DONE** | `AKS/Halver/Tanner.lean` |
| B | König Irregular | **DONE** | `AKS/Konig/Defs.lean` |
| C | Graph Halver | **BLOCKED** | `AKS/Halver/FromExpander.lean` |
| D | Seiferas Assembly | **DONE** | `AKS/Seiferas.lean` |
| E | Degree Bounds | **DONE** | `AKS/Graph/Contract.lean` |

**4 of 5 work packages completed. WP-C is BLOCKED (see below).**

---

## Completed Work Packages

### WP-A: Graph Tanner Bound — DONE

**File:** `AKS/Halver/Tanner.lean` (~405 lines added, 0 sorry)

Proved:
- `Graph.neighborSet`, `Graph.codeg`, `Graph.volIndicatorVec` — definitions
- `Graph.tanner_bound_vol` — volume-weighted Tanner bound
- `Graph.tanner_bound_card` — cardinality Tanner with degree ratio

The proof uses volume indicator vectors `φ_T(v) = √(deg v) · [v∈T]` in `EuclideanSpace ℝ (Fin n)`, Cauchy-Schwarz on codegrees, and orthogonal decomposition `Nφ = Pφ + (N-P)φ` with the spectral gap bound.

### WP-B: König for Irregular Bipartite — DONE

**File:** `AKS/Konig/Defs.lean` (0 sorry)

Proved:
- `RegBipartite.ofGraph` — pads irregular bipartite to Δ-regular
- Supporting infrastructure for König decomposition of irregular graphs

### WP-D: Seiferas Assembly — DONE

**File:** `AKS/Seiferas.lean` (0 new sorry), `AKS/Halver/Defs.lean` (0 sorry)

Proved:
- `contracted_squareIter_spectralGap` — spectral gap of contracted iterated-squared zigzag family member ≤ c^(2^l); chains `spectralGap_contract`, `spectralGap_toGraph`, `spectralGap_squareIter'`, `zigzagFamily_gap`
- `zigzagFamily_min_div_bound` — for smallest family level k with B^(k+1) ≥ m, the quotient N/m + 1 ≤ B + 1; provides uniform depth bound
- `graph_halverFamily_exists` — full assembly: picks smallest zigzag family member, squares l times, contracts, builds halver with ε = 4·c^(2^l) and uniform depth bound d·(B+1)
- `IsEpsilonHalver.mono` (in `Defs.lean`) — monotonicity: ε₁-halver is ε₂-halver when ε₁ ≤ ε₂
- `EpsilonInitialHalved.mono`, `EpsilonHalved.mono` — component monotonicity lemmas

The proof calls sorry'd `graph_exists_halver_depth_le` (WP-C), so `seiferas_sorting_networks_exist_graph` inherits that sorry. But the assembly itself is fully proved.

### WP-E: Contracted Expander Degree Bounds — DONE

**File:** `AKS/Graph/Contract.lean` (~121 lines, 0 sorry)

*Note: placed in `Graph/Contract.lean` (near `Graph.contract` definition), not in `ZigZag/Expanders.lean` as originally planned.*

Proved:
- `RegularGraph.contract_mod_deg` — contracted degree = d × fiber size
- `RegularGraph.contract_mod_deg_lb` — degree ≥ d · ⌊N/n⌋
- `RegularGraph.contract_mod_deg_ub` — degree ≤ d · (⌊N/n⌋ + 1)
- `RegularGraph.contract_mod_deg_ratio` — any vertex's degree ≤ 2× any other's

---

## BLOCKER: `graph_exists_halver_depth_le` Has Incorrect Statement

**Discovery date:** 2026-02-21

### The Problem

The theorem `graph_exists_halver_depth_le` claims that an irregular graph with spectral gap `beta` and degree ratio `r = d_max/d_min` gives an `r^2 * beta`-halver. **This is mathematically false.** The Tanner-based contradiction argument that works for regular graphs (r=1) breaks down for any r > 1.

### Algebraic Analysis

The regular halver proof uses the contradiction lemma `tanner_halver_contradiction`:
given `s > beta * k` and `s * m <= (k-s) * (s + beta^2 * (m-s))`, derive False. This works via the factored identity:
```
s*m - (k-s)*(s + beta^2*(m-s)) = (s - beta*(k-s))*(s + beta*(k-s)) + (m-k)*(s - beta^2*(k-s))
```
Both summands are positive when `s > beta * k` and `k <= m`.

For irregular graphs, `Graph.tanner_bound_card` gives:
```
|T| * m <= r^2 * |N(T)| * (|T| + beta^2 * (m - |T|))
```
Combined with `|N(T)| <= k - |T|`:
```
s * m <= r^2 * (k-s) * (s + beta^2 * (m-s))
```
For `s > r^2 * beta * k`, we need `s*m > r^2 * (k-s) * (s + beta^2*(m-s))`. But the r^2 factor on the RHS destroys the clean factorization. Specifically, at `s = 1`, `k ~ 1/(r^2*beta)`, the RHS is approximately `r^2 * (1/(r^2*beta)) * (1 + beta^2 * m) ~ m/beta * beta^2 = beta * m ~ 1`, matching the LHS `1 * m = m`... except the constants don't favor us.

### Numerical Evidence

Comprehensive Rust tests (`rust/test-halver-contradiction.rs`, `rust/test-halver-correct-eps.rs`, `rust/test-halver-small-r2.rs`) confirm:

1. **r^2 = 1 (regular):** `epsilon = beta` works for all beta, m, k, s. No counterexamples.
2. **r^2 = 4 (degree ratio 2):** `epsilon = r^2 * beta = 4*beta` fails. Concrete counterexample: r^2=4, beta=0.01, m=10, k=4, s=1: `s*m=10 <= r^2*(k-s)*(s+beta^2*(m-s))=12`.
3. **ANY r^2 > 1:** For sufficiently small beta, `epsilon = r^2 * beta` fails. The minimum q (=d_min/d) for contradiction is: beta=0.01: q=8366; beta=0.05: q=367; beta=0.10: q=83.
4. The achievable epsilon for r^2 = 4 is approximately `1 - 1/r^2 = 0.75`, NOT proportional to beta.
5. The `shrinkHalver` approach (from `AKS/Halver/Shrink.lean`) gives `epsilon' = beta * (N-m+1)` which grows linearly with m — too large.

### Why This Can't Be Fixed

The obstruction is fundamental, not a proof technique issue:
- The r^2 factor in the cardinality Tanner bound is TIGHT (it equals the volume Tanner after optimal conversion)
- Lifting to the regular graph's Tanner bound on pre-images gives the SAME r^2 = ((q+1)/q)^2
- For any r^2 > 1, at s=1 the Tanner bound is satisfiable for small beta, so no contradiction is possible

### Downstream Impact

`graph_halverFamily_exists` in `AKS/Seiferas.lean` calls `graph_exists_halver_depth_le` with `epsilon = 4 * c^(2^l)`. Since the theorem is false, this sorry propagates to `seiferas_sorting_networks_exist_graph`. The assembly code (WP-D) is fully proved, so only WP-C's sorry remains.

### Possible Fixes (require architectural changes)

1. **Prove `explicit_expanders_exist_zigzag`** (sorry'd in `ZigZag/Expanders.lean`): gives d-regular graphs at every size, so r^2 = 1 and Tanner works. Requires Cauchy interlacing theorem. HIGH effort.

2. **Redesign the pipeline to use `shrinkHalver`** at zigzag-family sizes only: for each m, build a regular halver on 2N wires (N = zigzag family size >= m), shrink to 2m wires with `epsilon' = beta * (N-m+1)`. The epsilon is NOT uniform (depends on N/m ratio). Would need a variable-epsilon `HalverFamily` structure or a different separator pipeline.

3. **Use a non-Tanner proof for the irregular halver.** No known approach exists — the Tanner/expander-mixing route is the standard technique.

4. **Pad m to a multiple of N** so contraction has equal fibers (making the contracted graph regular). Requires changing `HalverFamily` to only need halvers at specific sizes, or showing the separator pipeline can use non-uniform halver sizes.

---

## Remaining Work (BLOCKED)

### WP-C: `graph_exists_halver_depth_le` — BLOCKED

The theorem statement is mathematically false. See blocker section above.

---

## Files Modified (cumulative)

| File | WP | Status | Change |
|------|-----|--------|--------|
| `AKS/Halver/Tanner.lean` | A | **Done** | Graph neighborSet, codeg, volume/cardinality Tanner |
| `AKS/Graph/Walk.lean` | A | **Done** | Made `Graph.deg_src_pos` public |
| `AKS/Konig/Defs.lean` | B | **Done** | `RegBipartite.ofGraph` + König for irregular bipartite |
| `AKS/Graph/Contract.lean` | E | **Done** | Degree bound theorems for contracted expanders |
| `AKS/Halver/FromExpander.lean` | C | **BLOCKED** | `graphBipartiteComparators` done; `graph_exists_halver_depth_le` statement incorrect |
| `AKS/Halver/Defs.lean` | D | **Done** | `IsEpsilonHalver.mono` + component monotonicity |
| `AKS/Seiferas.lean` | D | **Done** | `contracted_squareIter_spectralGap`, `zigzagFamily_min_div_bound`, `graph_halverFamily_exists` |

## Verification

```bash
mcp__lean__check AKS/Halver/Tanner.lean       # WP-A (done)
mcp__lean__check AKS/Konig/Defs.lean           # WP-B (done)
mcp__lean__check AKS/Halver/Defs.lean          # WP-D monotonicity (done)
mcp__lean__check AKS/Graph/Contract.lean        # WP-E (done)
mcp__lean__check AKS/Halver/FromExpander.lean  # WP-C (sorry — BLOCKED)
mcp__lean__check AKS/Seiferas.lean              # WP-D assembly (done, calls sorry'd WP-C)
mcp__lean__check --all
scripts/sorries
```
