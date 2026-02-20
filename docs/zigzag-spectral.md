# Zig-Zag Spectral Analysis

Detailed architecture, proof status, and tactics for the zig-zag product spectral bound.

## Architecture

### `AKS/ZigZag/Operators.lean` — Zig-Zag Product and Walk Operators (~230 lines)
Defines the zig-zag product and the three CLM operators for its spectral analysis:
1. **Zig-zag product** — `G₁.zigzag G₂`, the three-step walk (zig-step-zag)
2. **Cluster encoding** — `cluster`/`port`/`encode` helpers for `Fin (n₁ * d₁)` ↔ `Fin n₁ × Fin d₁`
3. **Within-cluster walk** — `withinClusterCLM` (`B = I ⊗ W_{G₂}`)
4. **Step permutation** — `stepPermCLM` (`Σ`: permutes via `G₁.rot`)
5. **Cluster mean** — `clusterMeanCLM` (`Q`: averages within each cluster)
6. **Walk factorization** — `zigzag_walkCLM_eq`: `W_Z = B · Σ · B`

### `AKS/ZigZag/Spectral.lean` — Zig-Zag Operator Properties (~130 lines)
Algebraic identities and spectral bounds for the zig-zag operators:
1. **Algebraic properties** — `Q² = Q`, `Q* = Q`, `B* = B`, `Σ² = 1`, `Σ* = Σ`, `BQ = QB = Q`
2. **Tilde contraction** — `‖B(I-Q)‖ ≤ spectralGap G₂`
3. **Hat block norm** — `‖QΣQ - P‖ ≤ spectralGap G₁`
4. **Global mean decomposition** — `P·Q = Q·P = P`

### `AKS/ZigZag/Expanders.lean` — Expander Families (~115 lines)
Assembles the spectral bound and builds the iterated construction:
1. **Spectral composition theorem** — `zigzag_spectral_bound` (assembles sublemmas)
2. **Iterated construction** — `zigzagFamily`: square → zig-zag → repeat
3. **Main result** — `explicit_expanders_exist_zigzag`

## Sublemma Status

The 16 sublemmas of `zigzag_spectral_bound`:
- *Done (11/16):* `clusterMeanCLM_idempotent` (Q² = Q), `stepPermCLM_sq_eq_one` (Σ² = 1), `withinCluster_comp_clusterMean` (BQ = Q), `clusterMean_comp_meanCLM` (QP = P), `clusterMean_comp_withinCluster` (QB = Q), `meanCLM_eq_clusterMean_comp` (PQ = P), `withinClusterCLM_norm_le_one` (‖B‖ ≤ 1), `rvwBound_mono_left`, `rvwBound_mono_right`, `hat_block_norm` (‖QΣQ - P‖ ≤ spectralGap G₁), `withinCluster_tilde_contraction` (‖B(I-Q)‖ ≤ spectralGap G₂, 1 sorry in d₂=0 degenerate case)
- *Medium (1-2 weeks):* `clusterMeanCLM_isSelfAdjoint` (sum reorganization), `withinClusterCLM_isSelfAdjoint` (rotation bijection), `stepPermCLM_isSelfAdjoint` (involution → self-adjoint, needs bijection reindexing lemma), `zigzag_walkCLM_eq`, assembly of `zigzag_spectral_bound`
- *Done:* `rvw_quadratic_ineq` (proved in `ZigZag/RVWInequality.lean` via a-quadratic case analysis)

## Proof Tactics

**Algebraic CLM identities via `ext + simp + field_simp`.** For operator equalities (Q² = Q, BQ = Q, QP = P): (1) `ext f vk`, (2) `simp only [operator_apply, ...]`, (3) `field_simp`. For complex cases, insert `rw [Finset.sum_div]` between simp and field_simp. See `ZigZag/Spectral.lean`.

**Sum bijection helpers for reorganizing double sums.** For `Fin n₁ × Fin d₁ ≃ Fin (n₁ * d₁)`: use `Finset.sum_bij'` helpers (see `sum_encode_eq_sum`, `sum_over_cluster` in `ZigZag/Operators.lean`). Apply via `conv_lhs => rw [bijection_lemma]` in calc-style proofs.

**Block-diagonal operator norms via calc + per-block bounds.** (1) `opNorm_le_bound` → show `‖Bf‖ ≤ ‖f‖`, (2) expand `‖·‖²` via `EuclideanSpace.norm_sq_eq`, (3) regroup by blocks via bijection helpers, (4) `Finset.sum_le_sum` per-block, (5) connect to per-block norm bound. Use `Real.sqrt_le_sqrt` once. See `withinClusterCLM_norm_le_one` in `ZigZag/Spectral.lean`.
