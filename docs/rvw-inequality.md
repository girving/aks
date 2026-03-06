# RVW Quadratic Inequality

Detailed architecture and proof strategy for the RVW scalar inequality and operator bound.

## Architecture

### `AKS/ZigZag/RVWInequality.lean` — Core RVW Scalar Inequality (~400 lines)
Pure polynomial inequality, no operator imports. Fully proved (0 sorry):
1. **`rvw_reduced_ineq`** — V1' inequality via a-quadratic case analysis
2. **`rvw_cleared_ineq`** — cleared form via concavity + boundary reparameterization
3. **`rvw_quadratic_ineq`** — division form via `p·X ≤ |p|·|X|`

### `AKS/ZigZag/RVWBound.lean` — Abstract RVW Operator Bound
Operator theory importing `RVWInequality.lean`:
1. **`rvwBound`** — the precise RVW bound function
2. **Monotonicity** — `rvwBound_mono_left`, `rvwBound_mono_right`
3. **Abstract bound** — `rvw_operator_norm_bound`: `‖W - P‖ ≤ rvwBound(λ₁, λ₂)` from operator axioms

## Proof Chain

`rvw_quadratic_ineq` is fully proved in `AKS/ZigZag/RVWInequality.lean`:
1. **`rvw_reduced_ineq`** — core V1' inequality in 4 variables (α, wh, zh, a). Proved by treating as a quadratic in `a` and case-splitting: disc ≤ 0 (no real roots), vertex ≥ 1 (f(1) ≥ 0 suffices), or vertex ≤ 0 (f(0) ≥ 0 suffices).
2. **`rvw_cleared_ineq`** — cleared polynomial form, via concavity reduction + boundary reparameterization.
3. **`rvw_quadratic_ineq`** — original form with spectral gap parameters, via `p·X ≤ |p|·|X|`.

## Lesson: when `nlinarith` is structurally infeasible, try algebraic case analysis

Direct `nlinarith` (diagonal Positivstellensatz) was proven infeasible for this inequality. SOS certificates exist but couldn't be extracted at sufficient precision. The successful approach was mathematical: reparameterize to expose a quadratic in one variable, then case-split on discriminant sign and vertex location. Each case reduces to elementary `nlinarith` with explicit ring identity hints.
