# RVW Quadratic Inequality Proof Status

## Problem

Prove `rvw_quadratic_ineq` in `AKS/RVWBound.lean` — the core inequality for the RVW operator norm bound.

**Lean signature** (line ~784):
```lean
(p + 2 * q + r) ^ 2 ≤
  (1 - (c / b) ^ 2) * (|p| / a ^ 2) * |p + 2 * q + r| + (c / b) ^ 2
```

**After clearing denominators** (proved equivalent in the `suffices` block):
```
a²b²X² ≤ (b²-c²)|p||X| + a²c²
```

**After reducing to polynomial form** (proved: `(b²-c²)|p||X| ≥ (b²-c²)pX`):
```
G := a²c² + (b²-c²)pX - a²b²X² ≥ 0
```
where X = p+2q+r, a²+b²=1, |p|≤a², |r|≤c², c≤b, q²≤V₁=(a²+p)(c²+r), q²≤V₂=(a²-p)(c²-r).

## Current State of `RVWBound.lean`

**Only 2 sorries**: line ~331 (`rayleigh_quotient_bound`, unrelated) and the target `rvw_quadratic_ineq` (line ~805).

**Proved helper lemmas** (all compile):
- `rvw_X_le_sum_sq` (line ~722): `|p+2q+r| ≤ a²+c²` — AM-GM on V₁,V₂
- `rvw_q_sq_le` (line ~762): `q² ≤ a²c²+pr` — averaging V₁+V₂
- `rvw_weighted` (line ~769): `a²q² ≤ c²(a⁴-p²)` — weighted V₁+V₂

**Scaffolding** (compiles through to sorry):
- Fraction clearing via `suffices` + `le_div_iff₀` + `field_simp; ring`
- Reduction from `|p||X|` to `pX` via `(b²-c²)|p||X| ≥ (b²-c²)pX`

## What Has Been Proven Impossible

### Scalar multiplier nlinarith at degree ≤ 4 (LP infeasibility — PROVEN MULTIPLE TIMES)

1. **G ≥ 0 directly** (5 variables A,C,p,q,r): LP with 202 certificate terms. **INFEASIBLE.**
2. **G ≥ 0 with extended quadratic forms**: LP with additional degree-2 squares. **INFEASIBLE.**
3. **K ≥ 0** (4 variables A,C,p,r, the q-free part after substituting q²≤V₂): LP with 717 terms including triple products and constraint×square combinations. **INFEASIBLE.**
4. **Previous session results**: Two independent LP runs confirmed infeasibility with different variable sets.

**Root cause**: G has cross terms (pq, qr) with sign-varying coefficients that depend on parameters A, C. The constraint q²≤V has no linear-in-q terms. At degree 4, there is no way to generate the right parameter-dependent pq/qr coefficients from non-negative combinations of constraint products and squares. This is a structural impossibility, not a search failure.

**Implication**: No `nlinarith` proof exists for G ≥ 0 regardless of what product hints are provided, as long as all hints have total degree ≤ 4 in the variables. The same applies to K ≥ 0.

### AM-GM relaxation

K ≥ |β₀|·(A-p+C-r) fails numerically (min ≈ -0.23). The tight bound K²≥β²V₂ cannot be relaxed to degree < 8 via AM-GM.

### Discriminant/completing-the-square

Completing the square of G in X yields Z²≤RHS where Z=2a²b²X-(b²-c²)p, which is algebraically equivalent to G ≥ 0. Circular — no simplification.

### SDP/SOS numerical certificates (previous sessions)

Numerical SOS certificates found but too imprecise to extract exact rational proofs.

## What IS Known (Mathematical Analysis)

### The inequality is true and tight (minimum = 0)

Numerical optimization confirms G ≥ 0 with G = 0 at:
1. A = 1/2, C arbitrary, p=0, r=0, q=±√(AC): G = AC(2A-1)² = 0.
2. C = B = 1-A: G = 0 along a curve.

### Key structural insights

1. **G is concave in q** (coefficient -4AB < 0). So for q ∈ [-√V₂, √V₂], G is minimized at the boundary q = ±√V₂.
2. **G ≥ K + βq** where K = γ-4ABV₂ (substituting q²→V₂), β = 2[(B-C-2AB)p - 2ABr]. K ≥ 0 when V₂ ≤ V₁ (confirmed numerically). K² ≥ β²V₂ (confirmed numerically).
3. **|X| ≤ a²+c² ≤ 1** (proved in Lean), so X² ≤ |X| ≤ 1.
4. **WLOG V₂ ≤ V₁** by symmetry (p,r)→(-p,-r).
5. **(b²-c²)|p||X| ≥ (b²-c²)pX** always (since `|p||X| = |pX| ≥ pX`), so proving G ≥ 0 suffices.

### The K+βq decomposition (degree 8 bottleneck)

The proof chain is:
1. G ≥ K + βq (linear bound from q²≤V₂, valid since coeff of q² is negative)
2. K ≥ 0 (degree 4 in A,C,p,r — LP-infeasible at deg 4, needs higher degree or mathematical argument)
3. K² ≥ β²V₂ (degree 8 in A,C,p,r — only feasible at high degree)
4. K ≥ 0 and K² ≥ (βq)² imply K ≥ |βq|, so K+βq ≥ 0
5. Therefore G ≥ 0.

Steps 2 and 3 are the hard parts. Both require degree > 4 Positivstellensatz.

## Viable Proof Paths (for future sessions)

### Path A: Quadratic-in-r elimination

K is quadratic in r with negative leading coefficient -AB (concave in r). So K ≥ 0 on the feasible r interval [max(-C, -pC/A), C]. Check K at the endpoints:
- K(r=C): V₂=(A-p)·0=0 ⇒ q=0, simplifies to degree 2 in (A,C,p)
- K(r=-pC/A): V₁=V₂ intersection, simplifies via parametrization

If K at both endpoints can be shown ≥ 0 by nlinarith (each is degree ≤ 4 in 3 variables), the concavity gives K ≥ 0 for all feasible r.

### Path B: Lean proof via completing the square + sqrt bounds

Instead of polynomial certificates, use Lean's real analysis:
1. Complete the square: G = -AB(X-X₀)² + D where D = AC + (B-C)²p²/(4AB) ≥ 0
2. Need |X-X₀| ≤ √(D/AB). This involves √ but might be provable using existing `Real.sqrt_le_sqrt` etc.
3. Bound |X-X₀| using the constraints on q.

### Path C: Direct vector-level proof in the operator theory

Instead of proving the scalar inequality, prove the operator norm bound directly in Lean using inner product manipulations (avoiding the Rayleigh quotient reduction entirely). This would bypass the polynomial arithmetic bottleneck but requires significant restructuring.

### Path D: SOS at degree 6+ with rational arithmetic

Use an SDP solver with high-precision rational arithmetic (e.g., DSOS/SDSOS which reduce to LP/SOCP) to find exact rational certificates at degree 6 or 8. Then translate to Lean as explicit `have` statements.

## File Locations

- Main Lean file: `AKS/RVWBound.lean`
- This status doc: `scripts/RVW_QUADRATIC_PROOF_STATUS.md`
- LP feasibility scripts: `/tmp/rvw_lp.py`, `/tmp/rvw_k_lp.py`
- Numerical verification: `/tmp/rvw_g.py` (G≥0), `/tmp/rvw_decomp.py`
- Previous SDP attempts: `/tmp/rvw_clarabel.py`, `/tmp/rvw_full_psatz.py`
