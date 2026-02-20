# Halver and Expander Infrastructure

Detailed architecture and proof tactics for the halver/expander subsystem: graph theory, spectral gap, Tanner's bound, expander mixing, and the expander → ε-halver bridge.

## Architecture

### `AKS/Graph/Regular.lean` — Core Regular Graph Theory (~335 lines)
Core definitions and spectral gap, independent of specific constructions:
1. **Regular graphs and adjacency matrices** — `RegularGraph` (rotation map representation), `adjMatrix`, symmetry proofs
2. **Walk and mean operators** — `walkCLM` (CLM-first), `meanCLM`, `walkFun`/`walkLM`/`meanFun`/`meanLM` (three-layer pattern)
3. **Spectral gap** — `spectralGap` := `‖walkCLM - meanCLM‖` (operator norm), `spectralGap_nonneg`, `spectralGap_le_one`

### `AKS/Graph/Square.lean` — Graph Squaring (~225 lines)
Graph squaring and the spectral gap squaring identity:
1. **Graph squaring** — `G.square`, `adjMatrix_square_eq_sq`
2. **CLM identities** — self-adjointness, idempotency, `WP = PW = P`
3. **Spectral gap squaring** — `spectralGap_square`: λ(G²) = λ(G)²

### `AKS/Graph/Complete.lean` — Complete Graph (~108 lines)
The complete graph as a concrete example:
1. **Complete graph** — `completeGraph` via `Fin.succAbove`/`Fin.predAbove`
2. **Spectral gap** — `spectralGap_complete`: λ(K_{n+1}) = 1/n

### `AKS/Halver/Mixing.lean` — Expander Mixing Lemma
Fully proved expander mixing lemma via indicator vectors + Cauchy-Schwarz + operator norm.

### `AKS/Halver.lean` — ε-Halver Theory
ε-halvers and the expander → halver bridge. Imports `Graph/Regular.lean` and `Mixing.lean`:
1. **Sorted version** — `countOnes`, `sortedVersion`, `sortedVersion_monotone`
2. **ε-halvers** — `rank`, `EpsilonInitialHalved`, `EpsilonHalved`, `IsEpsilonHalver` (permutation-based, AKS Section 3), `epsHalverMerge`
3. **Sortedness infrastructure** — `IsEpsilonSorted`, `Monotone.bool_pattern`
Note: The tree-based AKS correctness proof is in `TreeSorting.lean`, not here. The `expander_gives_halver` proof is in `Halver/ExpanderToHalver.lean`.

### `AKS/Halver/Tanner.lean` — Tanner's Vertex Expansion Bound (~270 lines)
Tanner's bound and supporting lemmas. Imports `Mixing.lean` and `Square.lean`:
1. **Neighborhood/codegree** — `neighborSet`, `codeg`, `codeg_eq_zero_of_not_mem`
2. **Codegree sum** — `codeg_sum`: Σ codeg(v) = d·|T| (via rotation bijection)
3. **Walk-codegree identity** — `walkCLM_indicatorVec`, `norm_sq_walkCLM_indicatorVec`
4. **Orthogonal decomposition** — `norm_sq_walk_indicatorVec_le`: ‖W·1_T‖² ≤ |T|·(|T| + β²(n-|T|))/n
5. **Tanner's bound** — `tanner_bound`: |N(T)|·(|T| + β²(n-|T|)) ≥ |T|·n (fully proved)

### `AKS/Halver/ExpanderToHalver.lean` — Expander → ε-Halver Bridge (~650 lines)
Proves `expander_gives_halver` via Tanner's bound. Imports `Halver.lean`, `Halver/Tanner.lean`, `TreeSorting.lean`:
1. **Bipartite construction** — `bipartiteComparators G` (compare position v with m + G.neighbor(v,p))
2. **Edge monotonicity** — generalized to `LinearOrder α`: `exec_bipartite_edge_mono`
3. **Permutation counting** — `exec_perm_card_lt`: exactly k positions have output val < k
4. **Tanner-based proof** — `bipartite_epsilon_initial_halved`, `bipartite_epsilon_final_halved`
5. **Main theorem** — `expander_gives_halver` (fully proved, 0 sorry)

## Proof Tactics

**`Equiv.sum_comp` for rotation-bijection sum swaps.** Reindex via `G.rotEquiv.sum_comp`, then `simp only [show ∀ p, (G.rotEquiv p : _) = G.rot p from fun _ ↦ rfl, G.rot_involution]`. The `show` bridges `Equiv` coercion with `rot`. Don't use inside `calc` — unification fails when the coercion differs.

**`spectralGap_le_one` proof pattern: contraction + WP = P.** (1) `‖W‖ ≤ 1` via `opNorm_le_bound` + Cauchy-Schwarz + `rotEquiv.sum_comp`; (2) `WP = P`; (3) `‖f - Pf‖ ≤ ‖f‖` via `field_simp`+`nlinarith`; (4) factor `(W-P)f = W(f - Pf)` and chain. Handle d=0 separately. Pitfall: `Nat.cast_ne_zero.mpr` has type-class issues; use `by positivity` instead.

**Indicator vector pattern for combinatorial-spectral bridges.** (1) Define `indicatorVec S` via `(WithLp.equiv 2 _).symm (fun v ↦ if v ∈ S then 1 else 0)` with `@[simp]` apply lemma; (2) `‖indicatorVec S‖ = √↑S.card` via `EuclideanSpace.norm_sq_eq` + `sum_boole`; (3) express edge count as `⟨1_S, A(1_T)⟩` using `ite_mul`/`sum_filter`/`sum_boole`; (4) apply `abs_real_inner_le_norm` + `le_opNorm`. Key: `simp_rw [ite_mul, one_mul, zero_mul]; rw [← Finset.sum_filter]; have : univ.filter (· ∈ S) = S := by ext; simp`.

**Rotation bijection for walk/neighbor sum equality.** Use `RegularGraph.sum_neighbor_eq G (fun v => f v)` to show `∑ v ∑ i, f(G.neighbor v i) = ∑ v ∑ i, f v` (from `G.rot` involution). Chain with `Finset.sum_const` + `Finset.card_fin` for the d₂ factor.

## Proof Status

`IsEpsilonHalver` uses a permutation-based definition (AKS Section 3): for every permutation input, segment-wise bounds on displaced elements via `rank`. `expander_gives_halver` is fully proved via Tanner's vertex expansion bound + edge monotonicity + permutation counting. `expander_mixing_lemma` is fully proved.
