# RVW Quadratic Inequality Proof Status

## Problem

Prove `rvw_quadratic_ineq` in `AKS/RVWBound.lean` — the core inequality for the RVW operator norm bound.

**Goal** (after clearing denominators):
```
G := AC + (B-C)pX - ABX² ≥ 0
```
where A = a², B = b² = 1-A, C = c², with constraints from Cauchy-Schwarz (V1, V2) and variable bounds.

**Lean signature** (`rvw_quad_same_sign`, line 752):
```lean
X ^ 2 * (a ^ 2 * b ^ 2) ≤ (b ^ 2 - c ^ 2) * p * X + a ^ 2 * c ^ 2
```

## Current Errors (7 total in RVWBound.lean)

1. **Line 747**: `linarith` failed in `X_le_sum_sq`
2. **Line 752**: `nlinarith` timeout in `rvw_quad_same_sign` (3.2M heartbeats exhausted)
3. **Line 822**: `linarith` failed in `rvw_quad_neg_neg`
4. **Line 864**: `linarith` failed in `rvw_quad_opp_sign`
5. **Lines 929, 931**: Type mismatch in `rvw_quadratic_ineq` neg-neg case

The three `sorry`s in the file are at lines 336 (rayleigh_quotient_bound, unrelated), 731 (concave_quad_nonneg), and 749 (X_le_sum_sq).

## What Has Been Proven Impossible

### Scalar multiplier nlinarith (LP infeasibility — PROVEN TWICE)

**Attempt 1** (previous session): LP with 7 variables (a,b,c,p,q,r,X), products of 9 constraints up to degree 4. Result: INFEASIBLE.

**Attempt 2** (this session): LP with 5 variables (A,C,p,r,X) after eliminating q via `h_Xpr` and substituting B=1-A. Used 827 nonneg basis terms (all products of constraints up to degree 4, including V1' and V2'). Matrix rank = 126 = full monomial count. Result: **INFEASIBLE** (HiGHS solver).

**Conclusion**: No set of `nlinarith` hints using products of the available hypotheses can close the goal. The current massive hint lists in `rvw_quad_same_sign` (lines 769-803), `rvw_quad_neg_neg` (822-848), and `rvw_quad_opp_sign` (864-868) are fundamentally unable to work.

### SDP numerical certificate approach

- SCS solver found a numerical Positivstellensatz certificate (SOS polynomial multipliers) with 2e-3 reconstruction error
- CLARABEL solver failed with NumericalError (ill-conditioned SDP)
- Rationalization of SCS solution: error grew to 2e-2
- LP for exact rational weights on rounded terms: INFEASIBLE (rank 52 vs 126 needed)

**Conclusion**: Numerical SOS certificates don't have enough precision to extract exact rational proofs.

## What IS Known (Mathematical Analysis)

### The inequality is true and tight (minimum = 0)

Numerical optimization confirms G ≥ 0 everywhere on the constraint set, with G = 0 achieved at:

1. **A = 1/2, any C, p=0, r=0, q=±√(AC)**: Here G = AC(2A-1)² = 0.
2. **C = B (i.e., C = 1-A)**: Here B-C = 0, so G = AC - ABX². With X ≤ A+C = 1 and AB·1 = A(1-A) = AC when C = 1-A, G = 0.

### Key structural insights

1. **G is concave in X** (coefficient of X² is -AB ≤ 0), so on any interval [0,T], G ≥ 0 if G(0) ≥ 0 and G(T) ≥ 0.

2. **G(0) = AC ≥ 0** trivially.

3. **X ≤ A+C** from V2 + AM-GM (the `X_le_sum_sq` lemma, almost proved).

4. **G(A+C) is NOT always ≥ 0** from the (B-C)pX term alone when A > C and p is small. So simple concavity with T = A+C doesn't work.

5. **At p=0, r=0**: G = AC - 4ABq² and with q² ≤ AC (from V1∩V2 Cauchy-Schwarz), G = AC(1 - 4AB) = AC(2A-1)² ≥ 0.

6. **The `h_weighted` hypothesis** (A·q² ≤ C·(A²-p²)) is a derived constraint from (A-p)·V1 + (A+p)·V2. It provides a p-dependent tightening of the q-bound.

### Proof approach that should work (not yet implemented)

The proof requires **polynomial SOS multipliers** (full Positivstellensatz), not scalar multipliers. Two viable paths:

**Path A: Mathematical proof via variable elimination and case analysis**
- Eliminate q via h_Xpr, substitute B = 1-A
- Case split on relationship between A and C
- For A ≤ C: X ≤ A+C is achievable, G(A+C) ≥ 0 can be shown
- For A > C: V1 constraint limits X below A+C; use V1∩V2 intersection analysis (r = -pC/A) and parametrize on unit circle
- At V1∩V2 intersection with parametrization s = p/A, u = √(1-s²): G becomes a quadratic form on s²+u²=1 whose minimum is exactly 0 via the identity (a-c)² + b² = (2AC+a+c)²

**Path B: Decompose into smaller lemmas that nlinarith CAN handle individually**
- Factor G into terms where each term's nonnegativity IS provable by nlinarith with simpler hint sets
- Use the concavity lemma for sub-cases where it applies
- Handle the tight cases (A ≈ 1/2, C ≈ 1/2) separately

## File Locations

- Main Lean file: `AKS/RVWBound.lean` (lines 722-934 for the relevant section)
- LP feasibility script: `/tmp/rvw_lp.py` (confirms scalar multiplier infeasibility)
- Numerical minimization: `/tmp/min_G.py` (confirms G ≥ 0 with min = 0)
- SDP scripts (from previous sessions): `/tmp/rvw_clarabel.py`, `/tmp/rvw_full_psatz.py`, `/tmp/rvw_psatz4.py`, `/tmp/rvw_psatz5.py`, `/tmp/rvw_extract_cert.py`

## Recommended Next Steps

1. **Abandon the current nlinarith approach entirely.** The hint lists cannot work (LP-proven).

2. **Implement Path A**: Restructure `rvw_quad_same_sign` and siblings as a series of small helper lemmas:
   - `X_le_sum_sq` (fix the existing almost-done proof)
   - `G_at_zero_nonneg` (trivial: AC ≥ 0)
   - `G_nonneg_at_p_zero` (use q² ≤ AC to get G = AC(2A-1)² ≥ 0)
   - Handle general p via monotonicity or interpolation from p=0 case
   - The V1∩V2 intersection analysis for the A > C case

3. **Key mathematical insight to formalize**: At the V1∩V2 intersection, with r = -pC/A and q² = C(A²-p²)/A, the function G evaluated at these values simplifies to an expression that is manifestly ≥ 0. The hardest part is connecting the constrained minimum of G to this evaluation point.
