> **OBSOLETE:** Non-pow2 assembly path was deleted. Pow2 path uses regular contracted graphs.

# Quotient Halver: Direct Tanner Bound for Non-Integer n/k

When an expander graph of size `n` is quotiented down to a graph of size `k`
with `k ∤ n`, the contracted graph is irregular. This document records how to
get an ε-halver of size `2k` by applying Tanner's bound **directly to the
original graph** — bypassing the need to compute the contracted graph's
spectral gap.

## Setup

- `G` is a `d`-regular bipartite graph on `n + n` vertices with spectral gap `β`.
- Partition the left (resp. right) side into `k` fibers via `v ↦ v % k`.
- Let `q = ⌊n/k⌋`. Fiber sizes lie in `[q, q+1]`
  (`mod_fiber_card_lb` / `mod_fiber_card_ub` in `Graph/Contract.lean`).
- The contracted graph `G̅` on `2k` vertices has edge multiset derived from `G`.
  Degree of contracted wire `i`: `d · |fiber_i| ∈ [d·q, d·(q+1)]`
  (`contract_mod_deg_lb` / `contract_mod_deg_ub`).
- `G̅` is **not regular** when `k ∤ n`, so the regular Tanner bound does not
  apply to it directly.

## The Direct Argument

For any set `S ⊆ [k]` of wrong left wires with `|S| = ε·k`:

**Step 1 — Lift to the original graph.**
Define `S* = ∪_{i ∈ S} fiber_i ⊆ [n]`. Then:
```
|S| · q  ≤  |S*|  ≤  |S| · (q+1)
```

**Step 2 — Apply Tanner to `G` at `S*`.**
Using `G`'s known spectral gap `β` (via `tanner_bound`):
```
|N_G(S*)| · (|S*| + β² · (n − |S*|))  ≥  |S*| · n
```
equivalently:
```
|N_G(S*)|  ≥  |S*| · n / (|S*| + β² · (n − |S*|))
```

**Step 3 — Project down.**
Each contracted wire `j` in `N_{G̅}(S)` contributes at most `q+1` elements to
`N_G(S*)` (its entire fiber). Therefore:
```
|N_{G̅}(S)|  ≥  |N_G(S*)| / (q+1)
```
This is the **bridge lemma** (not yet stated in the codebase; see below).

**Step 4 — Derive expansion at the contracted level.**
Combining Steps 2–3 with `|S*| ≥ εk·q`:
```
|N_{G̅}(S)|  ≥  εkq · n / ((q+1) · (εk(q+1) + β²·(n − εkq)))
```
For `|N_{G̅}(S)| > εk` (expanding beyond the wrong wire count), the sufficient
condition simplifies to:
```
q / (q+1)  >  ε + β² · (1 − ε)
```
or equivalently:
```
ε  <  (q/(q+1) − β²) / (1 − β²)
```
For small `β` this is approximately `q/(q+1) · 1/(1+β²)`.

## ε Bound Comparison

| Condition | ε bound |
|---|---|
| `k ∣ n` (regular quotient) | `ε < 1/(1+β²)` |
| `k ∤ n`, `q = ⌊n/k⌋ = 1` | `ε < 1/(2(1+β²))` |
| `k ∤ n`, `q` large | `ε ≲ (1 − 1/q) · 1/(1+β²)` |

The penalty factor is `q/(q+1) = ⌊n/k⌋/⌈n/k⌉`, which is also the
`d_min/d_max` ratio proved in `contract_mod_deg_ratio`. It approaches 1 as
`q → ∞`, so for `n ≫ k` the halver quality is essentially the same as the
divisible case.

For the AKS construction, the zig-zag expander sizes grow much faster than
`k`, so `q` is large at every level and the penalty is negligible relative to
the asymptotic constants.

## Why This Avoids the Contracted Graph's Spectral Gap

The argument uses only:
1. The Tanner bound applied to **`G`** for the lifted sets `S*` (Step 2).
2. A purely combinatorial counting step (Step 3).

It never computes the spectral gap of `G̅`. This matters because the quotient
spectral gap is not obviously bounded by `β` — it can be worse — so going
through `G̅`'s spectral gap would require a separate (and nontrivial) transfer
theorem.

## What the Codebase Already Has

| Lemma | Location |
|---|---|
| `mod_fiber_card_lb`, `mod_fiber_card_ub` | `Graph/Contract.lean` |
| `contract_mod_deg`, `contract_mod_deg_lb`, `contract_mod_deg_ub` | `Graph/Contract.lean` |
| `contract_mod_deg_ratio` (ratio ≤ 2 when `q ≥ 1`) | `Graph/Contract.lean` |
| `tanner_bound` (regular case, fully proved) | `Halver/Tanner.lean` |
| `Graph.tanner_bound_card` (irregular, `(d_max/d_min)²` penalty) | `Halver/Tanner.lean` |

## Missing Piece: The Bridge Lemma

The only lemma not yet in the codebase is:

> **Bridge lemma.** For any `S ⊆ [k]` and `S* = ∪_{i∈S} fiber_i`:
> ```
> |N_{G̅}(S)| · (q+1)  ≥  |N_G(S*)|
> ```

*Proof sketch.* Define `π : [n] → [k]` by `π(v) = v % k`. Then `N_{G̅}(S) =
π(N_G(S*))`, and `|π(N_G(S*))| · max_j |fiber_j| ≥ |N_G(S*)|` since each
`j ∈ π(N_G(S*))` has `|fiber_j| ≤ q+1` preimages in `N_G(S*)`.

In Lean terms: injectivity on fibers gives a surjection from
`N_G(S*) → (N_{G̅}(S) × Fin (q+1))`, which by cardinality gives the bound.

## Proof Structure (When Formalizing)

```
tanner_bound G hd hn β hβ S*        -- Step 2: lower bound on |N_G(S*)|
bridge_lemma G k S (q+1)             -- Step 3: |N_{G̅}(S)| ≥ |N_G(S*)| / (q+1)
arithmetic (mod_fiber_card_lb ...)   -- Step 4: combine with fiber size bounds
→ expander_quotient_gives_halver G k hβ  -- conclusion
```

The result `expander_quotient_gives_halver` would state: for a `d`-regular
bipartite graph on `n + n` vertices with spectral gap `β`, the comparator
network induced by the mod-`k` quotient is an `ε`-halver of size `2k`, for
any `ε < (q/(q+1) − β²) / (1 − β²)` where `q = ⌊n/k⌋`.
