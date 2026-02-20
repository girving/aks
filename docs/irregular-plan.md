# Irregular Graph Refactor: Contraction Replaces Quotient

## Motivation

`spectralGap_quotient` (in `Graph/Quotient.lean`) is **false**. The current quotient
pads vertex classes with virtual self-loop vertices to maintain regularity. Self-loops
are fixed points of the walk operator, inflating `‖W - P‖` toward 1. Counterexample:
K_4 quotient to m=3 gives `spectralGap ≈ 0.816 > 1/3 = spectralGap(K_4)`.

The correct approach: define a general `Graph` type supporting irregular degree, and
a `contract` operation that maps edges `(a,b)` to `(s(a), s(b))` via a surjection `s`.
The contraction produces an irregular multigraph, but its spectral gap (suitably
defined via the normalized Laplacian `D^{-1/2} A D^{-1/2}`) is at most `spectralGap G`.
This follows from the Rayleigh quotient: the block-constant subspace used by the
contraction is a subspace of the original space, so the min-max characterization
gives `λ₂(contraction) ≤ λ₂(original)`.

## Design

### `Graph n` — Half-Edge Representation

```lean
structure Graph (n : ℕ) where
  numHalfEdges : ℕ
  src : Fin numHalfEdges → Fin n
  rot : Fin numHalfEdges → Fin numHalfEdges
  rot_involution : ∀ e, rot (rot e) = e
```

Each half-edge `e` has a source vertex `src e`. The rotation map `rot` pairs half-edges
into edges: if `rot e = e'`, then `(src e, src e')` is an edge. The involution ensures
each edge is counted exactly once from each side.

Key derived operations:
- `target e := src (rot e)` — the vertex at the other end
- `deg v := #{e | src e = v}` — the degree of vertex `v`
- `maxDeg := max over vertices of deg v`

### `Graph.contract` — Vertex Merging

Given `s : Fin n → Fin m` (surjection), the contraction is trivially:

```lean
def Graph.contract (G : Graph n) (s : Fin n → Fin m) : Graph m where
  numHalfEdges := G.numHalfEdges
  src e := s (G.src e)
  rot := G.rot
  rot_involution := G.rot_involution
```

Half-edges and pairing are unchanged; only vertex labels change. Self-loops arise
naturally when `s(src e) = s(target e)`.

### `RegularGraph.toGraph` — Embedding Regular Graphs

```lean
def RegularGraph.toGraph (G : RegularGraph n d) : Graph n where
  numHalfEdges := n * d
  src e := ⟨e.val / d, ...⟩
  rot e := ⟨(G.rot (⟨e.val / d, ...⟩, ⟨e.val % d, ...⟩)).1.val * d +
            (G.rot (⟨e.val / d, ...⟩, ⟨e.val % d, ...⟩)).2.val, ...⟩
  rot_involution := ...
```

Uses `Fin n × Fin d ↔ Fin (n * d)` encoding from `Misc/Fin.lean`.

### Spectral Bound for Contractions

**We do NOT define `Graph.spectralGap`.** Instead, we prove a direct theorem:

```lean
theorem spectralGap_contract_le (G : RegularGraph n d) (s : Fin n → Fin m)
    (hs : Function.Surjective s) : ...
```

The spectral bound works via the Rayleigh quotient argument (from the ChatGPT PDF):
1. Define `R = D^{-1/2} S` where `S` is the block indicator matrix and `D = S^T S = diag(|block_i|)`
2. Show `R R^T = I_m`, so `R^T` is an isometry from `ℝ^m` to the block-constant subspace
3. For any `f ⊥ 1_m`, the lift `R^T f` is block-constant and `⊥ 1_n`
4. Rayleigh quotient: `⟨f, R(W/d)R^T f⟩ / ⟨f, f⟩ ≤ λ₂(W/d) = spectralGap G`

The conclusion is stated in a form usable by Tanner's bound downstream.

## Downstream Changes

### Tanner's Bound (`Halver/Tanner.lean`)

Currently: `tanner_bound` takes `G : RegularGraph n d`.

New: generalize to work with contractions of regular graphs. Two approaches:

**Option A (minimal change):** Add a `tanner_bound_contract` that takes
`G : RegularGraph n d`, `s : Fin n → Fin m`, and proves Tanner for the
contracted graph using `spectralGap_contract_le`. The existing `tanner_bound`
stays unchanged for zig-zag infrastructure.

**Option B (more general):** Restate Tanner for any graph with a spectral gap
bound. This requires defining `neighborSet` and `codeg` for `Graph`.

Recommend **Option A** — it minimizes changes and the contraction is only used
in one place (the halver pipeline).

### Halver Construction (`Halver/ExpanderToHalver.lean`)

Currently: `expanderHalver` takes `G : RegularGraph m d` and builds bipartite
comparators via `G.neighbor v p`.

New: `expanderHalverContract` takes `G : RegularGraph n d`, `s : Fin n → Fin m`,
and builds comparators from the contracted graph. For each half-edge `e` with
`s(src e) = v`, compare wire `v` with wire `m + s(target e)`.

The halver is still bipartite, but different wires may have different numbers of
comparators (irregular degree). Edge monotonicity still holds (bipartite comparators
maintain top ≤ bottom regardless of order).

The depth bound uses König's edge coloring on the bipartite multigraph. Max degree
on each side ≤ `maxDeg(contraction)`. So depth ≤ `maxDeg`.

### `expanderHalverFamily` and `expanderToHalverFamily`

Currently: `expanderHalverFamily` needs `∀ m, m > 0 → RegularGraph m d`.

New: needs `∀ m, m > 0 → ∃ G : RegularGraph n d, ∃ s : Fin n → Fin m, ...`
where `n` is some zig-zag family size ≥ m. The degree of the contracted graph
varies with `m` (it's at most `d * ⌈n/m⌉`), so the `HalverFamily` depth bound
becomes `maxDeg` which is bounded by `d * ⌈n/m⌉ ≤ d * 2 = 2d` when we choose
`n ≤ 2m` (i.e., take the smallest zig-zag family member ≥ m).

### `explicit_expanders_exist_zigzag` and Size Reduction

Currently: `sorry`'d, claims `RegularGraph n (D * D)` at every size via
"induced subgraph + Cauchy interlacing" (which is hard to formalize).

New: replace with contraction. For each target size `m`:
1. Find `k` such that `zigzagFamily H₀ k` has `n_k ≥ m` vertices
2. Define `s : Fin n_k → Fin m` by `s(v) = v % m` (or `v * m / n_k`)
3. Contract: `(zigzagFamily H₀ k).2.toGraph.contract s`
4. Apply `spectralGap_contract_le` to get gap bound

The conclusion changes from `∃ G : RegularGraph n d, ...` to something like
`∃ (G : Graph m), G.maxDeg ≤ D_bound ∧ spectralGap_bound G ≤ c`.

### Top-Level Theorems

`zigzag_implies_aks_network` and `seiferas_implies_sorting_network` currently
assume `∃ d, ∀ n, n > 0 → ∃ G : RegularGraph n d, spectralGap G ≤ β`.

With the refactor, the assumption becomes: there exists a constant-degree
expander family (possibly irregular) with bounded spectral gap. The key
property consumed downstream is the halver family, not the graph itself.

**Simplest approach:** change `explicit_expanders_exist_zigzag` to directly
produce a `HalverFamily` (bypassing the irregular graph abstraction in the
theorem statement). Then the top-level theorems take a `HalverFamily` as input.

## Phase Breakdown

### Phase 1: Foundation (this commit)
- `AKS/Graph/Graph.lean`: `Graph` structure, `contract`, `RegularGraph.toGraph`
- `docs/irregular-plan.md`: this document

### Phase 2a: Spectral Bound (can parallelize with 2b)
- Prove `spectralGap_contract_le`: contraction preserves spectral gap
- Proof via Rayleigh quotient / block-constant lift
- File: `AKS/Graph/Contract.lean` or extend `Graph.lean`
- **Risk: MEDIUM** — the math is clean but connecting to `spectralGap` (CLM norm)
  requires bridging between matrix Rayleigh quotient and operator norm

### Phase 2b: Halver Generalization (can parallelize with 2a)
- `expanderHalverContract`: halver from contracted graph
- Tanner bound for contractions (via `spectralGap_contract_le`)
- König depth bound for irregular bipartite graphs
- File: extend `Halver/ExpanderToHalver.lean` or new `Halver/ContractHalver.lean`
- **Risk: MEDIUM** — edge monotonicity is identical, but Tanner needs reworking

### Phase 3: Assembly
- Wire `zigzagFamily` → contraction → halver family → top-level theorem
- Resolve `explicit_expanders_exist_zigzag` sorry (or replace with direct pipeline)
- Update `Seiferas.lean` and `Main.lean`
- **Risk: LOW** — assembly once components are proved

### Parallel Work Allocation

**Instance 1 (Phase 2a):** Spectral bound proof
- Define the lift operator `R^T` and projection `R`
- Prove `R R^T = I`, `R^T` isometric
- Prove Rayleigh quotient bound
- Connect to `spectralGap` definition

**Instance 2 (Phase 2b):** Halver generalization
- Define `expanderHalverContract`
- Prove edge monotonicity (reuse existing lemmas)
- Prove `tanner_bound_contract` (adapt `tanner_bound`)
- Prove König depth bound for max-degree

**Instance 3 (Phase 3, after 2a+2b):** Assembly
- Wire components together
- Resolve top-level sorry
- Update visualization

### Dependency Graph

```
Phase 1: Graph.lean (foundation)
    ↓
Phase 2a: Contract spectral bound ─────┐
Phase 2b: Halver generalization ────────┤
    ↓                                   ↓
Phase 3: Assembly (zigzagFamily → contract → halver → sorting)
```

## Degree Analysis

When contracting a `D²`-regular graph on `n` vertices to `m ≤ n` vertices:
- Each contracted vertex has degree ≤ `D² * ⌈n/m⌉`
- If we choose `n ≤ 2m` (smallest zig-zag family member ≥ m): degree ≤ `2 * D²`
- Halver depth ≤ max degree ≤ `2 * D²` (constant)
- For D = 12: max degree ≤ 288, halver depth ≤ 288

This is larger than the regular case (degree exactly `D² = 144`) but still constant.
The AKS theorem only needs O(1) depth halvers, so the constant doesn't matter for
the asymptotic result.

## What Gets Deleted

- `AKS/Graph/Quotient.lean` — the entire file (false theorem, superseded by contraction)
- The `import AKS.Graph.Quotient` line in `AKS.lean`

## What Stays Unchanged

- `AKS/Graph/Regular.lean` — core regular graph theory (zig-zag needs this)
- `AKS/Graph/Square.lean` — graph squaring
- `AKS/ZigZag/` — entire zig-zag infrastructure (operates on `RegularGraph`)
- `AKS/Halver/Tanner.lean` — existing Tanner bound (used by existing halver)
- `AKS/Halver/ExpanderToHalver.lean` — existing halver (works for `RegularGraph`)
