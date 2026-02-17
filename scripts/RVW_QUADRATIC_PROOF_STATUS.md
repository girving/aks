# RVW Quadratic Inequality Proof Status

## Problem

Prove `rvw_quadratic_ineq` in `AKS/RVWBound.lean` (line ~756) — the core scalar inequality for the RVW operator norm bound.

**Goal** (after clearing denominators):
```
A*B*X^2 <= (B-C)*|p|*|X| + A*C
```
Equivalently:
```
G := A*C + (B-C)*|p|*|X| - A*B*X^2 >= 0
```
where `A = a^2`, `B = b^2 = 1-A`, `C = c^2`, `X = p + 2q + r`.

**Constraints:**
- `|p| <= A`, `|r| <= C`
- `q^2 <= (A+p)(C+r)` (CS+, or F1)
- `q^2 <= (A-p)(C-r)` (CS-, or F2)

**Derived constraints** (already proved in Lean):
- `q^2 <= A*C + p*r` (sum CS)
- `A*q^2 <= C*(A^2 - p^2)` (weighted CS)

## What Has Been Proven Impossible

### Scalar multiplier `nlinarith` (LP infeasibility — proven repeatedly)

The inequality G >= 0 CANNOT be proved by `nlinarith` using products of the available constraints (A, 1-A, C, 1-A-C, p, A-p, C+r, C-r, p+r, Ar+Cp) at any degree.

**Tested configurations (all INFEASIBLE):**
1. 4 variables (A,C,p,r), degree 4, 11 constraints, 1124 products: rank 70 = full. INFEASIBLE.
2. 5 variables (A,C,p,r,Q) with Q = sqrt(F), degree 4, 1814 products: rank 126 = full. INFEASIBLE.
3. 5 variables with equality Q^2 = F2 (ideal + nonneg), degree 5: 5107 columns, rank 252. INFEASIBLE.
4. 5 variables with equality, degree 6: 15081 columns, rank 462. INFEASIBLE.
5. Change of variables x = A-p, y = C-r: INFEASIBLE.
6. `D0 = gamma_0 - 4AB*F2 >= 0` (all 4 case splits on sign of s and Ar+Cp): INFEASIBLE.
7. `D0^2 - beta^2*F2 >= 0` (degree 8, with all constraints): INFEASIBLE.
8. `beta >= 0` implied by `D0 <= 0`: INFEASIBLE.
9. `16*A^2*B^2*F2 <= (B-C)^2*p^2 + 4*A^2*B*C` (degree 4 with alpha <= 0): INFEASIBLE.

**Conclusion**: The inequality inherently requires `Real.sqrt` reasoning. Every approach to eliminate sqrt leads to the same degree-8 polynomial inequality `D0^2 >= beta^2*F_min`, which is LP-infeasible. The S-lemma (Yakubovich) also reduces to this same condition. This is not a limitation of the hint search — the Positivstellensatz certificate literally does not exist in the product-of-linear-constraints form.

### Numerical SOS (SDP) approach — early attempts

- SCS solver found a numerical certificate with ~2e-3 reconstruction error
- Rationalization failed (error grew to 2e-2)
- LP for exact rational weights on rounded terms: INFEASIBLE

### MOSEK SOS results (Feb 2026)

**Fixed (A,C) — 3-variable Putinar SOS in (p,q,r):**
- `mosek_sos2.py`: Full Putinar SOS with 7 constraint multipliers (p, A-p, C+r, C-r, CS+, CS-, X)
- **Degree 4 (sos_deg=2): only 2/10 test points feasible**
- **Degree 6 (sos_deg=3): 9/10 test points FEASIBLE** — breakthrough result
  - MOSEK precision: min eigenvalues ~1e-12 (excellent)
  - Q₀: 20×20 PSD matrix with rank ~10; constraint multipliers 10×10
  - All feasible cases pass numerical verification (100K random samples)
  - Only failure: A=0.50, C=0.49 (very near tight manifold C ≈ B = 0.50)
- `mosek_sos.py`: Earlier attempt in (s,t) boundary variables, 4/7 feasible — less effective

**Universal 5-variable SOS in (A,C,p,q,r) — all FAILED:**
- `mosek_universal.py`: Degree 4 INFEASIBLE, Degree 6 INFEASIBLE (8s solve)
- `mosek_universal2.py`: Degree 8 — MOSEK status UNKNOWN after 840s
  - PRSTATUS went negative (-0.98) = strong infeasibility signal
  - Adding derived constraint (sumCS) did not help
  - 27K PSD variables, 1287 equality constraints — size was not the issue
- **Likely cause**: G = 0 on a 1D tight manifold in 5D space makes universal
  Putinar certificate impossible or require extremely high degree. The tight
  manifold forces σ₀ and all non-vanishing-constraint multipliers to vanish
  along a curve, which is very constraining in 5 variables.

## Key Mathematical Facts (Numerically Verified)

### Facts that ARE LP-provable (nlinarith-accessible)

1. **gamma_0 >= 0** when s >= 0: LP-FEASIBLE with certificate involving ~15 terms.
   `gamma_0 = AC + (B-C)*p*s - AB*s^2` where `s = p + r`.
   Certificate includes products like `A*(1-A)*(C-r)*(p+r)`, `(1-A)*(1-A-C)*p*(p+r)`, etc.

2. **gamma_0_neg >= 0** when s < 0: LP-FEASIBLE with certificate.
   `gamma_0_neg = AC - (B-C)*p*s - AB*s^2`.

3. **D_disc - alpha^2 = 4*AB*gamma_0**: algebraic identity.
   Where `D_disc = (B-C)^2*p^2 + 4*A^2*B*C` and `alpha = 2*AB*s - (B-C)*|p|`.
   This means `|alpha| <= sqrt(D_disc)` follows from `gamma_0 >= 0`.

### Facts that are TRUE but NOT LP-provable

4. **D0_min = gamma_0 - 4*AB*min(F1,F2) >= 0**: 0 violations in 100M+ samples.
   Minimum is essentially 0 (achieved at extreme parameters).

5. **D0^2 >= beta^2*F_min**: 0 violations in 10M samples.
   This is degree 8 and LP-infeasible.

6. **G(Q) = gamma_0 + beta*Q - 4*AB*Q^2 >= 0** at Q = sqrt(F_min): 0 violations in 10M samples.

7. **|s-T| + 2*sqrt(F_min) <= sqrt(D_disc)/(2*AB)**: 0 violations in 10M samples.
   Where T = (B-C)*|p|/(2*AB).

### Structural insights

8. **D0 < 0 AND beta <= 0 is IMPOSSIBLE** when s >= 0 (0 cases in 10M samples with either F1 or F2).

9. **F1 - F2 = 2*(Ar + Cp)**: determines which CS bound is tighter.

10. **h_worse(s/2) = AC**: when `beta >= 0`, evaluating the "worse boundary" concave function
    `h(v) = gamma_0 - beta*v - 4*AB*v^2` at `v = s/2` gives exactly `AC >= 0`.
    This is verified algebraically: `gamma_0 - beta*s/2 - AB*s^2 = AC`.

## Proof Strategy

### The double-concavity approach

The proof uses two levels of concavity:

**Level 1**: G(q) = gamma_0 + beta*q - 4*AB*q^2 is concave in q.
- G(0) = gamma_0 >= 0 (LP-provable)
- By `concave_quad_min_boundary`, G >= 0 on [-Q, Q] iff G(Q) >= 0 and G(-Q) >= 0
- where Q = Real.sqrt(F) for the appropriate CS bound F

**Level 2**: G(Q) = gamma_0 + beta*Q - 4*AB*Q^2 is concave in Q (viewed as a real variable).
- G(0) = gamma_0 >= 0 (same as above)
- For the case beta_tilde >= 0 (where beta_tilde = |beta| or -|beta| depending on boundary):
  - h_worse(v) = gamma_0 - |beta|*v - 4*AB*v^2
  - h_worse(0) = gamma_0 >= 0
  - h_worse(s/2) = AC >= 0 (algebraic identity, for the right sign of beta)
  - If sqrt(F) <= s/2: done by concavity (h_worse is nonneg on [0, s/2] and sqrt(F) is in this interval)

### Remaining gap

When sqrt(F) > s/2 (about 42% of parameter space), the double-concavity with evaluation at s/2 is insufficient. The AM-GM bound `sqrt(F2) <= (A-p+C-r)/2` also fails (~32% violations).

For these cases, the proof requires either:
- **A degree-8 polynomial certificate** (D0^2 >= beta^2*F): LP-infeasible, needs SOS/SDP
- **A trigonometric proof** following the paper (Section 4.2, Claim 4.4)
- **A different algebraic decomposition** not yet discovered

## File Locations

- Main Lean file: `AKS/RVWBound.lean` (line ~756 for the sorry)
- This status document: `scripts/RVW_QUADRATIC_PROOF_STATUS.md`
- Analysis scripts: `/tmp/rvw_*.py` (various LP and numerical checks)

## Recommended Next Steps (updated Feb 2026)

### Path A: Extract exact certificate from fixed-(A,C) MOSEK solutions
The 3-variable degree-6 Putinar SOS works for 9/10 test points. To get a Lean proof:
1. Run MOSEK at many (A,C) grid points, extract Q₀ eigendecompositions
2. Look for closed-form pattern in how eigenvectors depend on A,C
3. If entries are polynomial/rational in A,C, construct a parametric certificate
4. Verify the parametric identity symbolically → gives nlinarith hints
**Risk**: Q₀ entries might not have nice closed forms in A,C.

### Path B: 4-variable SOS in (A,C,s,t) boundary variables
At the CS- boundary, substitute s=√(A-p), t=√(C-r), q=st. Then G becomes
degree 6 in (A,C,s,t). Try MOSEK universal SOS in 4 variables — smaller than
the 5-variable attempt. Basis size 35 (vs 56 for 5 vars at degree 3).

### Path C: Trigonometric proof from RVW Section 4.2
Formalize the paper's geometric proof. Laborious but guaranteed.
Note: the paper only proves a *weaker* bound (Claim 4.4). We need the exact
rvwBound formula, which requires adapting the argument.

### Path D: Axiomatize and move on
Leave the sorry and work on other parts of the project.

## File Locations

- Main Lean file: `AKS/RVWBound.lean` (line ~756 for the sorry)
- Exploratory trig approach: `AKS/RVWBoundTrig.lean` (marked NOT USEFUL)
- This status document: `scripts/RVW_QUADRATIC_PROOF_STATUS.md`
- MOSEK SOS scripts: `scripts/rvw/mosek_sos.py`, `mosek_sos2.py`, `mosek_universal.py`, `mosek_universal2.py`
- Rust numerical validator: `rust/rvw-sample/`
- Analysis scripts: `scripts/rvw/` and `/tmp/rvw_*.py` (158 ephemeral scripts)
