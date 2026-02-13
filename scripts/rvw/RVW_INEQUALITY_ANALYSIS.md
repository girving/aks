# RVW Inequality Analysis Summary

## Problem Statement

We need to prove:
```
X² · a² · b² ≤ (b² - c²) · |p| · |X| + a² · c²
```

where:
- `X = p + 2q + r`
- `a² + b² = 1` (equivalently: `b² = 1 - a²`)
- `a > 0, b > 0, c ≥ 0, c ≤ b`
- `|p| ≤ a²`
- `|r| ≤ c²`
- `q² ≤ (a² + p)(c² + r)` [CS+]
- `q² ≤ (a² - p)(c² - r)` [CS-]

Derived constraints:
- `q² ≤ a²c² + pr` [sum_CS] (from adding CS+ and CS-)
- `a²q² ≤ c²(a⁴ - p²)` [weighted_CS]

## Case Analysis

Focus on case: `p ≥ 0, X ≥ 0`

Rearranging the inequality:
```
a²b²X² - (b²-c²)pX - a²c² ≤ 0
```

## Key Findings

### 1. Numerical Verification

**Result:** The inequality holds numerically across 10,000+ random test cases satisfying all constraints.

- No violations found in case `p ≥ 0, X ≥ 0`
- Closest approaches to equality occur when:
  - `c` is very small (near 0)
  - `r ≈ 0`
  - CS constraints are nearly tight

### 2. Quadratic Form Structure

The inequality can be viewed as a quadratic in `X`:
```
f(X) = AX² + BX + C
where:
  A = a²b² > 0
  B = -(b²-c²)p
  C = -a²c²
```

Discriminant:
```
Δ = B² - 4AC = (b²-c²)²p² + 4a⁴b²c²
```

Since `A > 0`, the parabola opens upward. The quadratic is `≤ 0` between its roots:
```
X₋ = [(b²-c²)p - √Δ] / [2a²b²]
X₊ = [(b²-c²)p + √Δ] / [2a²b²]
```

**Key insight:** `X₋` can be negative! When `X₋ < 0` and we're in case `X ≥ 0`, the lower bound is automatically satisfied.

### 3. Bounds on X from CS Constraints

Maximum `X` (approximately):
- Set `r = c²` (maximizing r)
- From CS+: `q² ≤ (a² + p)(2c²)`
- So `q_max ≈ c√[2(a² + p)]`
- Thus `X_max ≈ p + 2c√[2(a² + p)] + c²`

Minimum `X` (in case `X ≥ 0`):
- Often `X_min ≈ p` when `q, r ≈ 0`
- Or `X_min ≈ p - 2c√[2(a² - p)] - c²` when `r = -c²`

**Numerical verification confirms:** For all valid `X` values under CS constraints, we have `X ∈ [X₋, X₊]`.

## Proof Strategies

### Strategy 1: Root Bounds (Geometric)

**Approach:** Prove that `X_min ≥ X₋` and `X_max ≤ X₊`.

**Status:** Numerically verified but algebraically complex.

**Challenges:**
- Involves square root inequalities
- Need to square both sides carefully
- Multiple cases based on which constraints are tight

### Strategy 2: Direct Substitution (Algebraic)

**Approach:** Substitute `X = p + 2q + r` directly into the quadratic and use CS constraints.

Expanding:
```
f(p + 2q + r) = a²b²(p² + 4q² + r² + 4pq + 4qr + 2pr)
                - (b²-c²)p(p + 2q + r) - a²c²
```

The coefficient of `4q²` is `4a²b²`, which matches the coefficient in constraint multiplication:
- Use `4a²b² · (a²c² + pr - q²) ≥ 0` from sum_CS

**Status:** Attempted with SOS decomposition.

**Challenges:**
- After eliminating `q²` term with sum_CS, residual is not a sum of squares
- Residual is negative 88% of the time, positive 12% of the time
- Need additional constraints or different coefficient

### Strategy 3: Complete the Square

The quadratic can be written as:
```
a²b²[X - (b²-c²)p/(2a²b²)]² - [(b²-c²)²p²]/(4b²) - a²c²
```

For this to be `≤ 0`, need:
```
a²b²[X - center]² ≤ [(b²-c²)²p²]/(4b²) + a²c²
```

This is a ball constraint on `X`. The proof reduces to showing CS constraints keep `X` within this ball.

**Status:** Conceptually clear but algebraically involved.

## Expanded Goal Polynomial

```
goal = -a⁴p² - 4a⁴pq - 2a⁴pr - 4a⁴q² - 4a⁴qr - a⁴r²
       - a²c² + 2a²p² + 6a²pq + 3a²pr + 4a²q² + 4a²qr + a²r²
       + c²p² + 2c²pq + c²pr - p² - 2pq - pr
```

Coefficient of `q²`: `4a²(1 - a²) = 4a²b²`

## Constraint Tightness at Critical Points

At points where the inequality is nearly tight (slack ≈ 0):
- `r ≈ 0` (very small)
- `c` is small
- CS+ and CS- are both nearly tight: `q² ≈ (a² ± p)(c² ± r)`
- weighted_CS is nearly tight: `a²q² ≈ c²(a⁴ - p²)`
- sum_CS is nearly tight: `q² ≈ a²c² + pr`

## Recommendations for Lean Formalization

1. **Prove the quadratic root structure first:**
   - `spectral_gap_quadratic`: The expression is a quadratic in `X`
   - `quadratic_has_roots`: Compute discriminant
   - `quadratic_sign_between_roots`: Standard result

2. **Prove bounds on X from CS:**
   - `cs_bounds_X_max`: Upper bound on `X`
   - `cs_bounds_X_min`: Lower bound on `X`

3. **Connect bounds to roots:**
   - `X_in_root_interval`: Combine previous results

4. **Alternative: Direct SOS** (if found)
   - Express `-goal = λ₁·constraint₁ + λ₂·constraint₂ + ... + R²`
   - Each term proved separately

## Open Questions

1. What is the exact SOS decomposition? The numerical evidence suggests one exists, but finding explicit coefficients is non-trivial.

2. Is there a cleaner formulation using the reflection structure? The RVW paper uses `Σ²=I` (reflection) which suggests geometric interpretation.

3. Can we use the fact that tightness occurs at `c → 0` to simplify the proof? When `c = 0`, the inequality becomes `a²b²X² - b²pX ≤ 0`, which factors as `b²X(a²X - p) ≤ 0`.

## Files Generated

- `analyze_rvw_inequality.py` - Initial numerical verification
- `sos_search.py` - Search for sum-of-squares decomposition
- `quadratic_bound_analysis.py` - Quadratic form and root structure
- `verify_root_bounds.py` - Numerical verification of root bounds
- `final_sos_analysis.py` - Systematic SOS search with constraints

All scripts can be run with: `uv run --with sympy --with numpy scripts/<script_name>.py`
