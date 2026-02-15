#!/usr/bin/env python3
# DEAD END: This script explores discriminant-based algebraic certificates for
# rvw_quadratic_ineq. The concavity-in-X reduction is equivalent to the original
# problem — see scripts/RVW_QUADRATIC_PROOF_STATUS.md.
"""
RVW quadratic inequality: find algebraic certificate.

Key insight from previous attempts:
1. Degree-4 Psatz (with or without q) is INFEASIBLE (rank deficit and LP infeasible)
2. The S-lemma reduction to (A,C,p,r) leaves c0_base < 0 sometimes
3. G at the V1=V2 tight manifold is NOT zero (it's AC*(2A-1)^2 at p=0, positive elsewhere)

NEW APPROACH: Prove the inequality in the form
  AB*X^2 <= (B-C)*p*X + AC
using a CONCAVITY argument + the constraint X <= X_bound(p).

The proof structure:
  f(X) = -AB*X^2 + (B-C)*p*X + AC is concave in X with f(0) = AC >= 0.
  So f(X) >= 0 for X in [0, X_+] where X_+ is the positive root.
  We need: for all feasible X, X <= X_+.

Equivalently: f(X) >= 0 iff (2AB*X - (B-C)*p)^2 <= (B-C)^2*p^2 + 4*A^2*B*C
iff (2AB*X - (B-C)*p)^2 <= D where D = (B-C)^2*p^2 + 4*A^2*B*C.

So the proof reduces to: (2AB*X - (B-C)*p)^2 <= D.

Let's expand 2AB*X = 2AB*(p+2q+r) = 2ABp + 4ABq + 2ABr.
2AB*X - (B-C)*p = 2ABp + 4ABq + 2ABr - Bp + Cp = (2AB-B+C)p + 4ABq + 2ABr
= B(2A-1)p + Cp + 4ABq + 2ABr

Let Y = 2ABX - (B-C)p. We need Y^2 <= D.
Y = B(2A-1)p + Cp + 4ABq + 2ABr

Also D = (B-C)^2*p^2 + 4*A^2*BC = B^2*p^2 - 2BC*p^2 + C^2*p^2 + 4*A^2*BC.

Let me compute D - Y^2 and try to show it's nonneg using V1, V2.
"""

import numpy as np
import sympy as sp
from fractions import Fraction
from collections import defaultdict

A, C, p, r, q = sp.symbols('A C p r q', real=True)
B = 1 - A

# Y = 2*A*B*X - (B-C)*p where X = p+2q+r
X = p + 2*q + r
Y = 2*A*B*X - (B-C)*p
Y_expanded = sp.expand(Y)

D = (B-C)**2 * p**2 + 4*A**2*B*C
D_expanded = sp.expand(D)

diff = sp.expand(D - Y**2)
print(f"D - Y^2 = {diff}")
print(f"D - Y^2 collected by q:")

# Collect by q
diff_poly = sp.Poly(diff, q)
for monom, coeff in sorted(diff_poly.as_dict().items()):
    print(f"  q^{monom[0]}: {sp.factor(coeff)}")

# D - Y^2 as quadratic in q:
# coeff of q^2, q^1, q^0
dq2 = diff.coeff(q, 2)
dq1 = diff.coeff(q, 1)
dq0 = sp.expand(diff - dq2*q**2 - dq1*q)

print(f"\ncoeff q^2: {sp.expand(dq2)}")
print(f"coeff q^1: {sp.expand(dq1)}")
print(f"coeff q^0: {sp.expand(dq0)}")

# We need D - Y^2 >= 0, i.e., dq2*q^2 + dq1*q + dq0 >= 0 for all feasible q.

# coeff q^2 should be -16A^2B^2 (negative, since Y^2 has 16A^2B^2q^2)
print(f"\ncoeff q^2 = {sp.factor(dq2)}")
# So D - Y^2 is CONCAVE in q. Min is at boundary of q's domain.

# From V2: q^2 <= (A-p)(C-r), so q in [-sqrt(V2), sqrt(V2)].
# Min of a concave function on an interval is at an endpoint.

# Let's compute D - Y^2 at q = sqrt((A-p)(C-r)):
# D - Y^2|_{q^2=(A-p)(C-r)} = dq2*(A-p)(C-r) + dq1*sqrt((A-p)(C-r)) + dq0
# This involves sqrt. But we can use the S-lemma:
# D - Y^2 + tau*(q^2 - V2) >= 0 for all q
# = (dq2 + tau)*q^2 + dq1*q + (dq0 - tau*V2)
# With tau = -dq2 = 16A^2B^2:
# = dq1*q + (dq0 - 16A^2B^2*(A-p)(C-r))
# Linear in q, need it >= 0 for |q| <= sqrt(V2).
# This requires: (dq0 - 16A^2B^2*V2)^2 >= dq1^2 * V2

# OR with tau > -dq2: upward parabola, discriminant condition.
# tau = 16A^2B^2 + delta:
# = delta*q^2 + dq1*q + (dq0 - (16A^2B^2+delta)*V2)
# Need: dq1^2 <= 4*delta*(dq0 - (16A^2B^2+delta)*V2)

# Let's compute dq0 - 16A^2B^2*V2:
c0_new = sp.expand(dq0 - 16*A**2*B**2*(A-p)*(C-r))
print(f"\ndq0 - 16A^2B^2*V2 = {c0_new}")
print(f"  factored: {sp.factor(c0_new)}")

# Check numerically
min_c0_new = float('inf')
worst = None
for _ in range(500000):
    A_v = np.random.uniform(0.01, 0.99)
    C_v = np.random.uniform(0, 1-A_v)
    p_v = np.random.uniform(0, A_v)
    r_v = np.random.uniform(-C_v, C_v)
    B_v = 1 - A_v
    val = float(c0_new.subs([(A, A_v), (C, C_v), (p, p_v), (r, r_v)]))
    if val < min_c0_new:
        min_c0_new = val
        worst = (A_v, C_v, p_v, r_v)
print(f"\nmin(c0_new) over 500K: {min_c0_new:.8f}")
if worst:
    print(f"  at A={worst[0]:.6f}, C={worst[1]:.6f}, p={worst[2]:.6f}, r={worst[3]:.6f}")

# Also check D-Y^2 with tau=0 (just D-Y^2 at q=sqrt(V2)):
min_DY2 = float('inf')
for _ in range(200000):
    A_v = np.random.uniform(0.01, 0.99)
    C_v = np.random.uniform(0, 1-A_v)
    p_v = np.random.uniform(0, A_v)
    r_v = np.random.uniform(-C_v, C_v)
    B_v = 1 - A_v
    V2_v = max(0, (A_v-p_v)*(C_v-r_v))
    for q_v in [np.sqrt(V2_v), -np.sqrt(V2_v), 0]:
        val = float(diff.subs([(A, A_v), (C, C_v), (p, p_v), (r, r_v), (q, q_v)]))
        min_DY2 = min(min_DY2, val)

print(f"min(D - Y^2) at boundary q: {min_DY2:.8f}")

# Let's try the S-lemma with BOTH V1 and V2 as before, but for D - Y^2
# D - Y^2 + tau1*V1_slack + tau2*V2_slack >= 0 for all q

V1_slack = sp.expand((A+p)*(C+r) - q**2)
V2_slack = sp.expand((A-p)*(C-r) - q**2)

# Combined quadratic: (dq2 + tau1 + tau2)*q^2 + dq1*q + (dq0 - tau1*(A+p)(C+r) - tau2*(A-p)(C-r))
# Set tau1 + tau2 = -dq2 = 16A^2B^2.

# Then linear in q: dq1*q + [dq0 - tau1*V1 - (16A^2B^2-tau1)*V2]
# = dq1*q + [dq0 - 16A^2B^2*V2 - tau1*(V1-V2)]
# = dq1*q + [c0_new - tau1*2*(Ar+pC)]

# For linear to be nonneg for ALL q: need dq1 = 0, which it's not.
# So we need tau1 + tau2 > 16A^2B^2.

# With delta = tau1+tau2 - 16A^2B^2 > 0 and the discriminant condition:
# dq1^2 <= 4*delta*(dq0 - tau1*V1 - (16A^2B^2+delta-tau1)*V2)
# = 4*delta*(c0_new - tau1*2(Ar+pC) - delta*V2)

# Optimize tau1 to maximize c0_new - tau1*2(Ar+pC):
# If Ar+pC > 0: tau1 = 0 is optimal.
# If Ar+pC < 0: tau1 = 16A^2B^2 + delta is optimal (max tau1).

# But tau1 >= 0 and tau2 = 16A^2B^2 + delta - tau1 >= 0.
# So 0 <= tau1 <= 16A^2B^2 + delta.

# Case Ar+pC >= 0: tau1 = 0.
# c0_eff = c0_new, and we need: dq1^2 <= 4*delta*(c0_new - delta*V2)
# For this to be feasible: c0_new^2 >= V2*dq1^2 (same condition as before).

# Let's check if this new c0 works better:
print("\n=== Checking c0_new^2 >= V2*dq1^2 (with tau1=0) ===")

dq1_expanded = sp.expand(dq1)
check_new = sp.expand(c0_new**2 - (A-p)*(C-r)*dq1_expanded**2)

min_check = float('inf')
for _ in range(200000):
    A_v = np.random.uniform(0.01, 0.99)
    C_v = np.random.uniform(0, 1-A_v)
    p_v = np.random.uniform(0, A_v)
    r_v = np.random.uniform(-C_v, C_v)
    val = float(check_new.subs([(A, A_v), (C, C_v), (p, p_v), (r, r_v)]))
    min_check = min(min_check, val)

print(f"min(c0_new^2 - V2*dq1^2) over 200K: {min_check:.8f}")

if min_check >= -1e-8:
    print("CONDITION HOLDS! c0_new^2 >= V2*dq1^2")
    print("This means the S-lemma certificate exists (with tau1=0).")

    # The Psatz for c0_new^2 - V2*dq1^2 >= 0 is a polynomial in (A,C,p,r)
    # Let's determine its degree and try LP.

    check_poly = sp.Poly(check_new, A, C, p, r)
    print(f"Degree of c0_new^2 - V2*dq1^2: {check_poly.total_degree()}")

    # This is a polynomial in 4 variables. Try Psatz with constraints
    # on (A,C,p,r): 0 <= A <= 1, 0 <= C <= 1-A, 0 <= p <= A, -C <= r <= C.

    # Actually, we ALSO need c0_new >= 0 for the certificate to work.
    print("\n--- Checking c0_new >= 0 ---")
    min_c0_new2 = float('inf')
    for _ in range(500000):
        A_v = np.random.uniform(0.01, 0.99)
        C_v = np.random.uniform(0, 1-A_v)
        p_v = np.random.uniform(0, A_v)
        r_v = np.random.uniform(-C_v, C_v)
        val = float(c0_new.subs([(A, A_v), (C, C_v), (p, p_v), (r, r_v)]))
        min_c0_new2 = min(min_c0_new2, val)
    print(f"min(c0_new) over 500K: {min_c0_new2:.8f}")

    if min_c0_new2 < -1e-6:
        print("c0_new can be negative! Condition c0_new >= 0 DOES NOT HOLD.")
        print("But c0_new^2 >= V2*dq1^2 DOES hold, so we can use it differently.")

        # Key: we don't NEED c0_new >= 0 separately.
        # The certificate is: D - Y^2 >= 0 for all q^2 <= V2,
        # which follows from:
        # At optimal delta: D-Y^2 + (16A^2B^2+delta)*V2_slack = delta*q^2 + dq1*q + c0_new - delta*V2
        # = delta*(q + dq1/(2*delta))^2 + c0_new - dq1^2/(4*delta) - delta*V2
        # >= 0 if c0_new - dq1^2/(4*delta) - delta*V2 >= 0
        # i.e., c0_new >= dq1^2/(4*delta) + delta*V2
        # Minimizing over delta: delta = |dq1|/(2*sqrt(V2)), min = |dq1|*sqrt(V2)
        # So c0_new >= |dq1|*sqrt(V2), i.e., c0_new^2 >= dq1^2*V2 (IF c0_new >= 0).

        # If c0_new < 0: the certificate doesn't work with tau1=0 and tau2 > 0.
        # But wait, we also have V1! Let me use BOTH V1 and V2.

        # With tau1, tau2 >= 0 and tau1+tau2 = 16A^2B^2 + delta:
        # Residual constant = dq0 - tau1*V1_bound - tau2*V2_bound
        # = dq0 - tau1*(A+p)(C+r) - (16A^2B^2+delta-tau1)*(A-p)(C-r)
        # = c0_new + 16A^2B^2*V2 - tau1*V1 - 16A^2B^2*V2 + tau1*V2 - delta*V2
        # = c0_new + tau1*(V2-V1) - delta*V2
        # = c0_new - tau1*2(Ar+pC) - delta*V2

        # With tau1 = gamma*(A*r+p*C) for appropriate gamma (to cancel the negative part of c0_new):
        # Actually, need tau1 >= 0, so if Ar+pC < 0, we can set tau1 large and c0_eff = c0_new + 2*tau1*(Ar+pC) could decrease...

        # Hmm. The sign of Ar+pC matters.
        # If p >= 0 and r >= 0: Ar+pC >= 0.
        # If p >= 0 and r < 0: Ar+pC can be negative (Ar < 0, pC >= 0).
        #   Ar + pC < 0 iff A|r| > pC iff |r| > pC/A.
        #   With |r| <= C: need pC/A < C, i.e., p < A. Always true for p < A.

        # When c0_new < 0, maybe it's because r is very negative (r close to -C).
        # In that case, V2 = (A-p)(C-r) is LARGE (C-r large).
        # And V1 = (A+p)(C+r) is SMALL (C+r small).
        # So we want to "use up" V2 (subtract it) and V1 is small, not helpful.

        # Let's check: at the point where c0_new is most negative, what are the values?
        A_v, C_v, p_v, r_v = worst
        B_v = 1 - A_v
        print(f"\nAt worst point: A={A_v:.6f}, C={C_v:.6f}, p={p_v:.6f}, r={r_v:.6f}")
        print(f"  V1 = {(A_v+p_v)*(C_v+r_v):.6f}")
        print(f"  V2 = {(A_v-p_v)*(C_v-r_v):.6f}")
        print(f"  c0_new = {min_c0_new:.6f}")
        print(f"  dq1 = {float(dq1_expanded.subs([(A,A_v),(C,C_v),(p,p_v),(r,r_v)])):.6f}")
        print(f"  Ar+pC = {A_v*r_v + p_v*C_v:.6f}")

        # Let me try: use the ADDITIONAL constraints to help.
        # The constraints h3..h11 are on (A,C,p,r) and DON'T involve q.
        # So they can serve as multipliers for the residual c0_new.

        # c0_new is a polynomial in (A,C,p,r). We need to show it's nonneg
        # on the FEASIBLE set of (A,C,p,r), not everywhere.
        # The feasible set is: 0 < A < 1, 0 <= C <= 1-A, 0 <= p <= A, |r| <= C.

        print("\n=== LP for c0_new >= 0 on feasible set ===")
        # Is c0_new actually nonneg on the feasible set?
        # Let me be more careful about checking
        min_c0_feas = float('inf')
        worst_feas = None
        for _ in range(2000000):
            A_v = np.random.uniform(0.001, 0.999)
            C_v = np.random.uniform(0, 1-A_v)
            p_v = np.random.uniform(0, A_v)
            r_v = np.random.uniform(-C_v, C_v)
            val = float(c0_new.subs([(A, A_v), (C, C_v), (p, p_v), (r, r_v)]))
            if val < min_c0_feas:
                min_c0_feas = val
                worst_feas = (A_v, C_v, p_v, r_v)

        print(f"min(c0_new) over 2M feasible: {min_c0_feas:.8f}")
        if worst_feas:
            print(f"  at A={worst_feas[0]:.6f}, C={worst_feas[1]:.6f}, p={worst_feas[2]:.6f}, r={worst_feas[3]:.6f}")

        if min_c0_feas >= -1e-6:
            print("c0_new IS nonneg on feasible set (within tolerance)!")
        else:
            print("c0_new is NEGATIVE on feasible set. Need more work.")
            # Use scipy to minimize c0_new properly
            from scipy.optimize import minimize, LinearConstraint

            def neg_c0(x):
                return -float(c0_new.subs([(A, x[0]), (C, x[1]), (p, x[2]), (r, x[3])]))

            best_neg = 0
            best_x = None
            for _ in range(1000):
                A_v = np.random.uniform(0.01, 0.99)
                C_v = np.random.uniform(0, max(0.001, 1-A_v))
                p_v = np.random.uniform(0, A_v)
                r_v = np.random.uniform(-C_v, C_v)
                x0 = [A_v, C_v, p_v, r_v]
                try:
                    bounds = [(0.001, 0.999), (0.001, None), (0, None), (None, None)]
                    res = minimize(neg_c0, x0, method='Nelder-Mead',
                                  options={'maxiter': 1000, 'xatol': 1e-10, 'fatol': 1e-10})
                    x = res.x
                    # Check feasibility
                    if (0 < x[0] < 1 and 0 <= x[1] <= 1-x[0] and 0 <= x[2] <= x[0] and abs(x[3]) <= x[1]):
                        if -res.fun < best_neg:
                            best_neg = -res.fun
                            best_x = x
                except:
                    pass

            print(f"\nOptimized min(c0_new) = {best_neg:.10f}")
            if best_x is not None:
                print(f"  at A={best_x[0]:.8f}, C={best_x[1]:.8f}, p={best_x[2]:.8f}, r={best_x[3]:.8f}")
                B_v = 1 - best_x[0]
                print(f"  B = {B_v:.8f}")
                print(f"  V1 = {(best_x[0]+best_x[2])*(best_x[1]+best_x[3]):.8f}")
                print(f"  V2 = {(best_x[0]-best_x[2])*(best_x[1]-best_x[3]):.8f}")

elif min_check < -1e-4:
    print("CONDITION FAILS. c0_new^2 < V2*dq1^2 somewhere.")
    # Find the worst point
    worst_check = None
    for _ in range(200000):
        A_v = np.random.uniform(0.01, 0.99)
        C_v = np.random.uniform(0, 1-A_v)
        p_v = np.random.uniform(0, A_v)
        r_v = np.random.uniform(-C_v, C_v)
        val = float(check_new.subs([(A, A_v), (C, C_v), (p, p_v), (r, r_v)]))
        if val < 0 and (worst_check is None or val < worst_check[1]):
            worst_check = ((A_v, C_v, p_v, r_v), val)
    if worst_check:
        pt, val = worst_check
        print(f"  at A={pt[0]:.6f}, C={pt[1]:.6f}, p={pt[2]:.6f}, r={pt[3]:.6f}: {val:.8f}")

# Let's try yet ANOTHER decomposition: instead of Y = 2ABX - (B-C)p,
# use the SIGN-MATCHED decomposition.

print("\n" + "="*60)
print("ALTERNATIVE: Two-step proof via concavity + V2 bound")
print("="*60)

# G(X) = -AB*X^2 + (B-C)p*X + AC  (concave in X, f(0) = AC >= 0)
# Need: G(X) >= 0 for all feasible X.
# Sufficient: G(X_max) >= 0 where X_max = max feasible X.

# From V2 (with q = (X-p-r)/2):
# ((X-p-r)/2)^2 <= (A-p)(C-r)
# X <= p + r + 2*sqrt((A-p)(C-r)) =: UB(r)  (taking X >= 0)
# Also from V1: X >= p + r - 2*sqrt((A+p)(C+r)) (X could be at lower bound)
# But since X >= 0 and G(0) = AC >= 0, we only need the upper bound.

# G(UB(r)) = -AB*UB(r)^2 + (B-C)*p*UB(r) + AC

# Hmm, UB depends on r. We want max over r of UB(r).
# From earlier analysis: max UB over r (with |r| <= C) occurs at r = C-A+p if feasible.

# Actually, let me try a DIRECT approach: show G >= 0 using only the combined
# constraint q^2 <= AC + pr (from V1+V2) and the weighted constraint A*q^2 <= C*(A^2-p^2).

# Both constraints are provable from V1 and V2 alone.
# G = -4AB*q^2 + 2(B-C)*p*q + [AC + (B-C)*p*(p+r) - AB*(p+r)^2]

# Use the two quadratic constraints to bound G.
# Let's try: G >= 4AB*(AC+pr-q^2) + (something)
# Since 4AB*(AC+pr-q^2) >= 0 (from combined constraint), this would give G >= (something).
# G - 4AB*(AC+pr-q^2) = G + 4AB*q^2 - 4AB*AC - 4ABpr
# = [G + 4AB*q^2] - 4A^2BC - 4ABpr
# G + 4ABq^2 = 2(B-C)pq + [AC + (B-C)p(p+r) - AB(p+r)^2] + 4ABq^2 + (-4AB+4AB)q^2
# Wait: G = -4ABq^2 + 2(B-C)pq + a0. So G + 4ABq^2 = 2(B-C)pq + a0.
# G = (4AB*combined_slack) + 2(B-C)pq + a0 - 4AB(AC+pr)
# = 4AB*(AC+pr-q^2) + 2(B-C)pq + a0 - 4AB(AC+pr)

# So: G = 4AB*Slack_combined + 2(B-C)pq + [a0 - 4AB(AC+pr)]

# a0 - 4AB(AC+pr) = AC + (B-C)p(p+r) - AB(p+r)^2 - 4ABAC - 4ABpr
# = AC(1-4AB) + (B-C)p(p+r) - AB(p+r)^2 - 4ABpr
# = AC(2A-1)^2 + (B-C)p^2 + (B-C)pr - ABp^2 - 2ABpr - ABr^2 - 4ABpr
# = AC(2A-1)^2 + (B-C-AB)p^2 + (B-C-6AB)pr - ABr^2

# Let me simplify B-C-AB = B(1-A)-C = B^2-C. And B-C-6AB = B-C-6AB.
# Hmm.

a0_expr = sp.expand(A*C + (B-C)*p*(p+r) - A*B*(p+r)**2)
remainder = sp.expand(a0_expr - 4*A*B*(A*C + p*r))
print(f"\na0 - 4AB(AC+pr) = {remainder}")
print(f"  factored: {sp.factor(remainder)}")

# Check if this is always nonneg
min_rem = float('inf')
for _ in range(200000):
    A_v = np.random.uniform(0.01, 0.99)
    C_v = np.random.uniform(0, 1-A_v)
    p_v = np.random.uniform(0, A_v)
    r_v = np.random.uniform(-C_v, C_v)
    val = float(remainder.subs([(A, A_v), (C, C_v), (p, p_v), (r, r_v)]))
    min_rem = min(min_rem, val)
print(f"min(remainder): {min_rem:.8f}")

# G = 4AB*Slack_combined + 2(B-C)pq + remainder
# Slack_combined >= 0. Need: 2(B-C)pq + remainder >= 0.
# Since p >= 0, if B >= C (i.e., C <= B, which is a constraint), then (B-C)p >= 0.
# If q >= 0: 2(B-C)pq >= 0, so need remainder >= 0.
# If q < 0: 2(B-C)pq < 0. Need |2(B-C)pq| <= remainder.

# Can use weighted constraint for the q < 0 case:
# A*q^2 <= C*(A^2-p^2). So |q| <= sqrt(C(A^2-p^2)/A).
# 2(B-C)p*|q| <= 2(B-C)p*sqrt(C(A^2-p^2)/A)
# Need: remainder >= 2(B-C)p*sqrt(C(A^2-p^2)/A)
# i.e., remainder^2 >= 4(B-C)^2 * p^2 * C*(A^2-p^2)/A

# Let me check this.
print("\n=== Checking remainder >= 0 ===")
if min_rem >= -1e-6:
    print("remainder IS nonneg (approximately)! So G >= 2(B-C)pq.")
    print("When q >= 0: G >= 0 + 0 = 0.")
    print("When q < 0: G >= 4AB*Slack + 2(B-C)p*q + remainder")
    print("  >= 0 + 2(B-C)p*q + remainder")
    print("  >= remainder - 2(B-C)p*|q|")
    print("  Need: remainder >= 2(B-C)p*|q|")

    # Use q^2 <= AC + pr (combined): |q| <= sqrt(AC+pr)
    # 2(B-C)p*|q| <= 2(B-C)p*sqrt(AC+pr)
    # Need: remainder >= 2(B-C)p*sqrt(AC+pr)
    # Squaring: remainder^2 >= 4(B-C)^2*p^2*(AC+pr)

    check_sq = sp.expand(remainder**2 - 4*(B-C)**2*p**2*(A*C+p*r))
    min_sq = float('inf')
    for _ in range(200000):
        A_v = np.random.uniform(0.01, 0.99)
        C_v = np.random.uniform(0, 1-A_v)
        p_v = np.random.uniform(0, A_v)
        r_v = np.random.uniform(-C_v, C_v)
        val = float(check_sq.subs([(A, A_v), (C, C_v), (p, p_v), (r, r_v)]))
        min_sq = min(min_sq, val)
    print(f"  min(remainder^2 - 4(B-C)^2*p^2*(AC+pr)): {min_sq:.8f}")

    # Also try with weighted constraint:
    check_sq2 = sp.expand(remainder**2*A - 4*(B-C)**2*p**2*C*(A**2-p**2))
    min_sq2 = float('inf')
    for _ in range(200000):
        A_v = np.random.uniform(0.01, 0.99)
        C_v = np.random.uniform(0, 1-A_v)
        p_v = np.random.uniform(0, A_v)
        r_v = np.random.uniform(-C_v, C_v)
        val = float(check_sq2.subs([(A, A_v), (C, C_v), (p, p_v), (r, r_v)]))
        min_sq2 = min(min_sq2, val)
    print(f"  min(A*remainder^2 - 4(B-C)^2*p^2*C*(A^2-p^2)): {min_sq2:.8f}")

else:
    print(f"remainder can be negative ({min_rem:.8f}). This approach won't work directly.")

# Let me try yet another split using the WEIGHTED constraint directly.
print("\n" + "="*60)
print("Using weighted constraint: G = 4B*weighted_slack + linear_remainder")
print("="*60)

# Weighted slack = C*(A^2-p^2) - A*q^2 >= 0
# G = -4ABq^2 + 2(B-C)pq + a0
# = 4B*(C*(A^2-p^2) - A*q^2) + (something)
# 4B*(C*(A^2-p^2)-Aq^2) = 4BC*(A^2-p^2) - 4ABq^2
# So: G - 4B*(C*(A^2-p^2)-Aq^2) = 2(B-C)pq + a0 - 4BC*(A^2-p^2)

weighted_rem = sp.expand(a0_expr - 4*B*C*(A**2 - p**2))
print(f"a0 - 4BC(A^2-p^2) = {sp.expand(weighted_rem)}")
print(f"  = {sp.factor(weighted_rem)}")

# G = 4B*weighted_slack + 2(B-C)pq + weighted_rem
# Both weighted_slack >= 0 and 4B >= 0.
# Need: 2(B-C)pq + weighted_rem >= 0.

min_wr = float('inf')
for _ in range(200000):
    A_v = np.random.uniform(0.01, 0.99)
    C_v = np.random.uniform(0, 1-A_v)
    p_v = np.random.uniform(0, A_v)
    r_v = np.random.uniform(-C_v, C_v)
    val = float(weighted_rem.subs([(A, A_v), (C, C_v), (p, p_v), (r, r_v)]))
    min_wr = min(min_wr, val)
print(f"min(weighted_rem): {min_wr:.8f}")

if min_wr >= -1e-6:
    print("weighted_rem is nonneg! Good.")
    # For q >= 0: G >= 2(B-C)pq + weighted_rem >= 0 since all terms nonneg.
    # For q < 0: Need weighted_rem >= 2(B-C)p|q|.
    # Using |q| <= sqrt(AC+pr) from combined:
    # 2(B-C)p*|q| <= 2(B-C)p*sqrt(AC+pr)
    # Need: weighted_rem >= 2(B-C)p*sqrt(AC+pr)
    # Squaring: weighted_rem^2 >= 4(B-C)^2*p^2*(AC+pr) (when weighted_rem >= 0)

    check_wr = sp.expand(weighted_rem**2 - 4*(B-C)**2*p**2*(A*C+p*r))
    min_cwr = float('inf')
    for _ in range(200000):
        A_v = np.random.uniform(0.01, 0.99)
        C_v = np.random.uniform(0, 1-A_v)
        p_v = np.random.uniform(0, A_v)
        r_v = np.random.uniform(-C_v, C_v)
        val = float(check_wr.subs([(A, A_v), (C, C_v), (p, p_v), (r, r_v)]))
        min_cwr = min(min_cwr, val)
    print(f"  min(weighted_rem^2 - 4(B-C)^2*p^2*(AC+pr)): {min_cwr:.8f}")

    if min_cwr >= -1e-6:
        print("  Full condition holds!")
    else:
        # Try using V2 directly: |q| <= sqrt(V2) = sqrt((A-p)(C-r))
        # Need: weighted_rem^2 >= 4(B-C)^2*p^2*(A-p)(C-r)
        check_wr2 = sp.expand(weighted_rem**2 - 4*(B-C)**2*p**2*(A-p)*(C-r))
        min_cwr2 = float('inf')
        for _ in range(200000):
            A_v = np.random.uniform(0.01, 0.99)
            C_v = np.random.uniform(0, 1-A_v)
            p_v = np.random.uniform(0, A_v)
            r_v = np.random.uniform(-C_v, C_v)
            val = float(check_wr2.subs([(A, A_v), (C, C_v), (p, p_v), (r, r_v)]))
            min_cwr2 = min(min_cwr2, val)
        print(f"  min(weighted_rem^2 - 4(B-C)^2*p^2*V2): {min_cwr2:.8f}")

# At this point, let me just try the SIMPLEST possible decomposition that might work.
# G = AC + (B-C)pX - ABX^2
# = AC + (B-C)p(p+2q+r) - AB(p+2q+r)^2
# = AC + (B-C)p^2 + (B-C)pr + 2(B-C)pq - AB(p+r)^2 - 4AB(p+r)q - 4ABq^2

# Use 4ABq^2 <= 4AB(AC+pr) (combined constraint):
# G >= AC + (B-C)p^2 + (B-C)pr + 2(B-C)pq - AB(p+r)^2 - 4AB(p+r)q - 4AB(AC+pr)
# = AC(1-4AB) + (B-C)p^2 + (B-C)pr - AB(p+r)^2 - 4ABpr + [2(B-C)p - 4AB(p+r)]q
# = AC(2A-1)^2 + (B-C-AB)p^2 + (B-C-6AB)pr - ABr^2 + [2(B-C)p - 4AB(p+r)]q

print("\n" + "="*60)
print("Decomposition: G = 4AB*(q^2-AC-pr slack) + stuff")
print("="*60)

# Let me compute the constant part more carefully using sympy
const_after_combined = sp.expand(A*C*(2*A-1)**2 + (B-C-A*B)*p**2 + (B-C-6*A*B)*p*r - A*B*r**2)
print(f"Constant: {sp.expand(const_after_combined)}")
print(f"Constant factored: {sp.factor(const_after_combined)}")

# Now the linear-in-q part:
lin_q = sp.expand(2*(B-C)*p - 4*A*B*(p+r))
print(f"Linear in q coefficient: {sp.expand(lin_q)}")

# G = 4AB*combined_slack + lin_q*q + const_after_combined
# For q >= 0 and lin_q >= 0: G >= const_after_combined.
# For q < 0 and lin_q >= 0: G >= 4AB*slack + lin_q*q + const >= 4AB*slack + const - |lin_q|*sqrt(AC+pr)
# For q >= 0 and lin_q < 0: G >= 4AB*slack + const - |lin_q|*sqrt(AC+pr)

# In all cases: G >= const - |lin_q|*sqrt(AC+pr)
# Need: const >= |lin_q|*sqrt(AC+pr)
# i.e., const^2 >= lin_q^2*(AC+pr) (when const >= 0)

# First check: is const_after_combined always nonneg?
min_const = float('inf')
for _ in range(500000):
    A_v = np.random.uniform(0.01, 0.99)
    C_v = np.random.uniform(0, 1-A_v)
    p_v = np.random.uniform(0, A_v)
    r_v = np.random.uniform(-C_v, C_v)
    val = float(const_after_combined.subs([(A, A_v), (C, C_v), (p, p_v), (r, r_v)]))
    min_const = min(min_const, val)
print(f"\nmin(const_after_combined): {min_const:.8f}")

# At p=0, r=0: const = AC(2A-1)^2 >= 0. Good.
# At p=A, r=0: const = AC(2A-1)^2 + (B-C-AB)*A^2 = AC(2A-1)^2 + (B^2-C)*A^2
# = AC(2A-1)^2 + A^2B^2 - A^2C = A[C(2A-1)^2 + AB^2 - AC] = A[C(2A-1)^2 + A(B^2-C)]
# = A[C(4A^2-4A+1) + A(1-2A+A^2-C)] = A[4A^2C - 4AC + C + A - 2A^2 + A^3 - AC]
# ... complicated.

if min_const >= -1e-6:
    print("const_after_combined is nonneg! Now check the squaring condition.")
    # Actually wait - we also need to handle the linear-in-q term MORE CAREFULLY.
    # G = 4AB*combined_slack + lin_q*q + const
    # If const >= 0 and lin_q*q >= 0: G >= 0. Done.
    # If lin_q*q < 0: need combined_slack*4AB + const >= |lin_q*q|.
    # Using |q| <= sqrt(AC+pr) (and also |q| <= sqrt(V2)):
    # |lin_q*q| <= |lin_q|*sqrt(AC+pr)
    # So: G >= 4AB*0 + const - |lin_q|*sqrt(AC+pr) = const - |lin_q|*sqrt(AC+pr)
    # Need: const^2 >= lin_q^2 * (AC+pr)

    check_final = sp.expand(const_after_combined**2 - lin_q**2*(A*C+p*r))
    min_cf = float('inf')
    for _ in range(500000):
        A_v = np.random.uniform(0.01, 0.99)
        C_v = np.random.uniform(0, 1-A_v)
        p_v = np.random.uniform(0, A_v)
        r_v = np.random.uniform(-C_v, C_v)
        val = float(check_final.subs([(A, A_v), (C, C_v), (p, p_v), (r, r_v)]))
        min_cf = min(min_cf, val)
    print(f"  min(const^2 - lin_q^2*(AC+pr)): {min_cf:.8f}")

    if min_cf >= -1e-6:
        print("  BOTH conditions hold! Proof structure works!")
        # Decompose:
        # 1. const_after_combined >= 0 (a polynomial inequality in A,C,p,r)
        # 2. const^2 >= lin_q^2*(AC+pr) (another polynomial inequality)
        # Both are in 4 variables with simple constraints.
        # Try Psatz on each.

        deg_const = sp.Poly(const_after_combined, A, C, p, r).total_degree()
        deg_check = sp.Poly(check_final, A, C, p, r).total_degree()
        print(f"\n  const_after_combined degree: {deg_const}")
        print(f"  check_final degree: {deg_check}")
    else:
        print("  Squaring condition fails. Need different bound on |q|.")
        # Try: use |q| <= sqrt((A-p)(C-r)) from V2 instead
        check_V2 = sp.expand(const_after_combined**2 - lin_q**2*(A-p)*(C-r))
        min_V2 = float('inf')
        for _ in range(500000):
            A_v = np.random.uniform(0.01, 0.99)
            C_v = np.random.uniform(0, 1-A_v)
            p_v = np.random.uniform(0, A_v)
            r_v = np.random.uniform(-C_v, C_v)
            val = float(check_V2.subs([(A, A_v), (C, C_v), (p, p_v), (r, r_v)]))
            min_V2 = min(min_V2, val)
        print(f"  min(const^2 - lin_q^2*V2): {min_V2:.8f}")

        # Try: |q| <= sqrt(C(A^2-p^2)/A) from weighted
        check_W = sp.expand(const_after_combined**2*A - lin_q**2*C*(A**2-p**2))
        min_W = float('inf')
        for _ in range(500000):
            A_v = np.random.uniform(0.01, 0.99)
            C_v = np.random.uniform(0, 1-A_v)
            p_v = np.random.uniform(0, A_v)
            r_v = np.random.uniform(-C_v, C_v)
            val = float(check_W.subs([(A, A_v), (C, C_v), (p, p_v), (r, r_v)]))
            min_W = min(min_W, val)
        print(f"  min(A*const^2 - lin_q^2*C*(A^2-p^2)): {min_W:.8f}")

        if min_W >= -1e-6:
            print("  Weighted version works!")
else:
    print(f"const_after_combined can be negative ({min_const:.8f}). Need different approach.")
