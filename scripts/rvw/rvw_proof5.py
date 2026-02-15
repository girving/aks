#!/usr/bin/env python3
# DEAD END: This script explores combined-constraint decompositions for
# rvw_quadratic_ineq. The diagonal Positivstellensatz is structurally infeasible
# — see scripts/RVW_QUADRATIC_PROOF_STATUS.md.
"""
Focused script: Find decomposition for RVW quadratic inequality.

G = AC + (B-C)pX - ABX^2 >= 0 where B=1-A, X=p+2q+r.
Constraints: V1: q^2 <= (A+p)(C+r), V2: q^2 <= (A-p)(C-r)
Plus: 0<A<1, 0<=C<=B, 0<=p<=A, |r|<=C.

Strategy: G = alpha*V_slack + beta*something + nonneg_polynomial
where V_slack uses the combined constraint q^2 <= AC+pr.
"""
import sys
import numpy as np
import sympy as sp

A, C, p, r, q = sp.symbols('A C p r q', real=True)
B = 1 - A

# G as quadratic in q
a2 = sp.expand(-4*A*(1-A))  # coeff of q^2
a1 = sp.expand(2*(1-A-C)*p - 4*A*(1-A)*(p+r))  # coeff of q
a0 = sp.expand(A*C + (1-A-C)*p*(p+r) - A*(1-A)*(p+r)**2)  # constant

print("G = a2*q^2 + a1*q + a0")
print(f"a2 = {a2}")
print(f"a1 = {a1}", flush=True)

# Combined constraint: q^2 <= AC + pr
# G = a2*q^2 + a1*q + a0
# = a2*(AC+pr) + a1*q + a0 + a2*(q^2 - AC - pr)
# = a2*(AC+pr) + a0 + a1*q - |a2|*(AC+pr - q^2)
# Since a2 = -4AB < 0 and (AC+pr-q^2) >= 0:
# G = -4AB*(AC+pr) + a0 + a1*q + 4AB*(AC+pr-q^2)
# G = 4AB*combined_slack + a1*q + [a0 - 4AB*(AC+pr)]

const_term = sp.expand(a0 - 4*A*(1-A)*(A*C + p*r))
print(f"\nConst = a0 - 4AB(AC+pr) = {const_term}")
print(f"  Factor: {sp.factor(const_term)}", flush=True)

# Check if const_term >= 0 on feasible set
np.random.seed(42)
min_c = float('inf')
for _ in range(500000):
    Av = np.random.uniform(0.01, 0.99)
    Cv = np.random.uniform(0, 1-Av)
    pv = np.random.uniform(0, Av)
    rv = np.random.uniform(-Cv, Cv)
    val = Av*Cv*(2*Av-1)**2 + ((1-Av)-Cv-Av*(1-Av))*pv**2 + ((1-Av)-Cv-6*Av*(1-Av))*pv*rv - Av*(1-Av)*rv**2
    min_c = min(min_c, val)
print(f"\nmin(const) over 500K: {min_c:.8f}", flush=True)

# Now: G = 4AB*Slack + a1*q + const
# a1 = 2(B-C)p - 4AB(p+r) = 2[(1-A-C)p - 2A(1-A)(p+r)]
# For feasible q with q^2 <= AC+pr:

# Case 1: q >= 0 and a1 >= 0 => G >= const >= 0.
# Case 2: q >= 0 and a1 < 0 => a1*q >= a1*sqrt(AC+pr). Need: const + a1*sqrt(AC+pr) >= 0.
# Case 3: q < 0 and a1 >= 0 => a1*q <= 0. Need: const + a1*q >= 0, so const >= |a1|*|q| >= |a1|*sqrt(AC+pr).
# Case 4: q < 0 and a1 < 0 => a1*q >= 0. G >= const >= 0.

# In all cases: G >= const - |a1|*sqrt(AC+pr)
# Sufficient: const >= |a1|*sqrt(AC+pr)
# i.e., const^2 >= a1^2*(AC+pr) (when const >= 0)

# But wait, we could also use V2: q^2 <= (A-p)(C-r) as a tighter bound.
# |q| <= sqrt(min(AC+pr, (A-p)(C-r)))

# For CASE 2: q >= 0 and a1 < 0. a1*q ranges from a1*sqrt(V2) to 0 (worst at q = sqrt(V2)).
# Need: const >= |a1|*sqrt(V2) where V2 = (A-p)(C-r).
# i.e., const^2 >= a1^2*(A-p)(C-r)

# For CASE 3: q < 0 and a1 >= 0. a1*q ranges from -a1*sqrt(V2) to 0.
# Need: const >= a1*sqrt(V2).
# i.e., const^2 >= a1^2*V2

# So in BOTH bad cases: need const^2 >= a1^2 * V2.

# BUT: in case 2, q >= 0 means X = p+2q+r >= p+r. If a1 < 0, the q contribution is negative.
# In case 3, q < 0 means X <= p+r. If a1 >= 0, the q contribution is negative.

# Actually, we should use DIFFERENT q bounds for different cases.
# When q >= 0: use V2 gives q <= sqrt(V2). But also q <= sqrt(V1) where V1 = (A+p)(C+r).
# When q < 0: |q| <= sqrt(V2) (and sqrt(V1)).

# For case 2 (q >= 0, a1 < 0):
# We need |a1|*q <= const + 4AB*Slack.
# Since Slack = AC+pr-q^2 >= 0, we have 4AB*(AC+pr) >= 4AB*q^2.
# So: G = 4AB*Slack + a1*q + const >= a1*q + const (using slack >= 0).
# Need: a1*q + const >= 0, i.e., |a1|*q <= const.
# Best q bound depends on additional constraints.

# Alternatively: G = -4AB*q^2 + a1*q + a0 is a concave quadratic in q.
# It's maximized at q* = a1/(8AB). On the interval [0, sqrt(V2)]:
# If q* >= sqrt(V2): G is increasing on [0, sqrt(V2)], min at q=0: G(0) = a0.
# If q* <= 0: G is decreasing on [0, sqrt(V2)], min at q=sqrt(V2).
# If 0 < q* < sqrt(V2): min at q=0 or q=sqrt(V2) (since concave, max in middle).

# G(0) = a0 = AC + (B-C)p(p+r) - AB(p+r)^2

# Check if a0 >= 0 on feasible set:
min_a0 = float('inf')
for _ in range(500000):
    Av = np.random.uniform(0.01, 0.99)
    Cv = np.random.uniform(0, 1-Av)
    pv = np.random.uniform(0, Av)
    rv = np.random.uniform(-Cv, Cv)
    Bv = 1 - Av
    a0v = Av*Cv + (Bv-Cv)*pv*(pv+rv) - Av*Bv*(pv+rv)**2
    min_a0 = min(min_a0, a0v)
print(f"\nmin(a0 = G(q=0)) over 500K: {min_a0:.8f}", flush=True)

# Also check G at q = sqrt(V2):
min_G_at_V2 = float('inf')
for _ in range(500000):
    Av = np.random.uniform(0.01, 0.99)
    Cv = np.random.uniform(0, 1-Av)
    pv = np.random.uniform(0, Av)
    rv = np.random.uniform(-Cv, Cv)
    Bv = 1 - Av
    V2v = max(0, (Av-pv)*(Cv-rv))
    qv = np.sqrt(V2v)
    Gv = -4*Av*Bv*qv**2 + (2*(Bv-Cv)*pv - 4*Av*Bv*(pv+rv))*qv + Av*Cv + (Bv-Cv)*pv*(pv+rv) - Av*Bv*(pv+rv)**2
    min_G_at_V2 = min(min_G_at_V2, Gv)
print(f"min(G at q=sqrt(V2)) over 500K: {min_G_at_V2:.8f}", flush=True)

# Check G at q = -sqrt(V2):
min_G_at_mV2 = float('inf')
for _ in range(500000):
    Av = np.random.uniform(0.01, 0.99)
    Cv = np.random.uniform(0, 1-Av)
    pv = np.random.uniform(0, Av)
    rv = np.random.uniform(-Cv, Cv)
    Bv = 1 - Av
    V2v = max(0, (Av-pv)*(Cv-rv))
    qv = -np.sqrt(V2v)
    # But also need X >= 0: p + 2q + r >= 0
    Xv = pv + 2*qv + rv
    if Xv < 0:
        # Need to take |X| for the bound, but let's compute G for this q
        # Actually, the Lean statement uses |X|, so we should use |p+2q+r|
        pass
    Gv = -4*Av*Bv*qv**2 + (2*(Bv-Cv)*pv - 4*Av*Bv*(pv+rv))*qv + Av*Cv + (Bv-Cv)*pv*(pv+rv) - Av*Bv*(pv+rv)**2
    min_G_at_mV2 = min(min_G_at_mV2, Gv)
print(f"min(G at q=-sqrt(V2)) over 500K: {min_G_at_mV2:.8f}", flush=True)

# Wait - the problem uses |p+2q+r| not (p+2q+r). Let me re-read the Lean statement.
# Line 791: (p + 2 * q + r) ^ 2 <= ...
# So it's X^2 on the left side. And |p+2q+r| on the right multiplied by something.
# G = AC + (B-C)*|p|*|X| - AB*X^2 where X = p+2q+r.
# Since X^2 = |X|^2, we can set Y = |X| and G = AC + (B-C)*|p|*Y - AB*Y^2.
# This is the SAME for X and -X. So we need G >= 0 for all q (not just q giving X >= 0).

# So G(q) = AC + (B-C)*|p|*|p+2q+r| - AB*(p+2q+r)^2

# For WLOG p >= 0: G(q) = AC + (B-C)*p*|p+2q+r| - AB*(p+2q+r)^2

# Now |p+2q+r| makes this NOT a polynomial! It's piecewise.
# Case p+2q+r >= 0: G = AC + (B-C)*p*(p+2q+r) - AB*(p+2q+r)^2  (quadratic in q, concave)
# Case p+2q+r < 0: G = AC - (B-C)*p*(p+2q+r) - AB*(p+2q+r)^2  (different quadratic)

# Wait, re-reading the Lean more carefully:
# The Lean lemma `rvw_quadratic_ineq` proves:
# (p + 2*q + r)^2 <= (1 - (c/b)^2) * (|p|/a^2) * |p+2q+r| + (c/b)^2
# After mult by a^2*b^2:
# a^2*b^2*(p+2q+r)^2 <= (b^2-c^2)*|p|*|p+2q+r| + a^2*c^2
# i.e., AB*X^2 <= (B-C)*|p|*|X| + AC
# i.e., AC + (B-C)*|p|*|X| - AB*X^2 >= 0

# With Y = |X| >= 0: AC + (B-C)*|p|*Y - AB*Y^2 >= 0.
# This is just f(Y) = -AB*Y^2 + (B-C)*|p|*Y + AC, a downward parabola in Y.
# f(0) = AC >= 0.
# We need: Y <= Y_+ (positive root of f).

# Y = |p+2q+r|. So we need |p+2q+r| <= Y_+.
# From rvw_X_le_sum_sq: |p+2q+r| <= a^2+c^2 = A+C. This is already proved!
# Need: f(A+C) >= 0 FOR ALL FEASIBLE p.

# Wait, we showed f(A+C) < 0 for some (A,C,p). The issue is that
# X = |p+2q+r| <= A+C but the Y_+ bound ALSO depends on p.
# When p is small, Y_+ < A+C, so we can't use Y <= A+C.

# OK let me just focus on proving: f(Y) >= 0 for Y = |p+2q+r| using V1, V2.
# Since f is a downward parabola in Y with f(0) = AC >= 0,
# f(Y) >= 0 iff Y <= Y_+ = [(B-C)p + sqrt((B-C)^2*p^2 + 4*A^2*BC)]/(2AB)
# (here p = |p|, assuming WLOG p >= 0).

# So we need: |p+2q+r|^2 * (2AB)^2 <= [(B-C)p + sqrt(D)]^2 where D = (B-C)^2*p^2 + 4*A^2*BC
# <=> 4*A^2*B^2*(p+2q+r)^2 <= (B-C)^2*p^2 + 2(B-C)p*sqrt(D) + D
# <=> 4*A^2*B^2*(p+2q+r)^2 <= 2*(B-C)^2*p^2 + 4*A^2*BC + 2*(B-C)*p*sqrt(D)

# Hmm, involving sqrt(D). Hard to work with.

# BETTER: just prove 4*A^2*B^2*Y^2 <= (B-C)^2*p^2*Y^2/(AB)^{-1}... no.
# f(Y) >= 0 <=> AB*Y^2 - (B-C)*p*Y - AC <= 0
# <=> Y*(AB*Y - (B-C)*p) <= AC
# <=> Y * [AB*Y - (B-C)*p] <= AC

# If AB*Y <= (B-C)*p: LHS <= 0 <= AC. Done!
# If AB*Y > (B-C)*p: need Y*(AB*Y-(B-C)p) <= AC.

# The first case: AB*Y <= (B-C)*p, i.e., Y <= (B-C)p/(AB).
# This is trivially satisfied when Y is small or p is large.

# The second case: Y*(ABY - (B-C)p) <= AC.
# Using V1+V2 combined: 4q^2 <= 4(AC+pr), so |2q| <= 2*sqrt(AC+pr).
# Y = |p+2q+r| <= p + 2|q| + |r| <= p + 2*sqrt(AC+pr) + C.
# Not obviously useful.

# Let me try the CORRECT factorization.
# f(Y) = -AB*Y^2 + (B-C)*p*Y + AC
# = -AB*(Y - (B-C)p/(2AB))^2 + (B-C)^2*p^2/(4AB) + AC

# For f >= 0: (Y - (B-C)p/(2AB))^2 <= [(B-C)^2*p^2 + 4*A^2*BC]/(4*A^2*B^2)
# i.e., |Y - (B-C)p/(2AB)| <= sqrt(D)/(2AB) where D = (B-C)^2*p^2 + 4*A^2*BC

# Equivalently: (2*AB*Y - (B-C)*p)^2 <= D

# Let W = 2*AB*Y - (B-C)*p = 2AB|p+2q+r| - (B-C)p.
# Need: W^2 <= D = (B-C)^2*p^2 + 4*A^2*BC.

# Now D - W^2 = (B-C)^2*p^2 + 4*A^2*BC - [2AB|p+2q+r| - (B-C)p]^2

# Let's compute D - W^2 for the case X = p+2q+r >= 0 (WLOG):
# W = 2AB*(p+2q+r) - (B-C)p = 2ABp + 4ABq + 2ABr - Bp + Cp
# = (2AB-B+C)p + 4ABq + 2ABr = (C-B^2)p + 4ABq + 2ABr ... wait
# Actually: 2AB - B + C = B(2A-1) + C

W_expr = sp.expand(2*A*(1-A)*(p+2*q+r) - ((1-A)-C)*p)
D_expr = sp.expand(((1-A)-C)**2 * p**2 + 4*A**2*(1-A)*C)

diff = sp.expand(D_expr - W_expr**2)
print(f"\nD - W^2 = {diff}", flush=True)

# Collect by q
diff_q2 = diff.coeff(q, 2)
diff_q1 = diff.coeff(q, 1)
diff_q0 = sp.expand(diff - diff_q2*q**2 - diff_q1*q)

print(f"\nD - W^2 by q:")
print(f"  q^2: {sp.expand(diff_q2)}")
print(f"  q^1: {sp.expand(diff_q1)}")
print(f"  q^0: {sp.expand(diff_q0)}", flush=True)
print(f"  q^2 factored: {sp.factor(diff_q2)}")
print(f"  q^1 factored: {sp.factor(diff_q1)}")
print(f"  q^0 factored: {sp.factor(diff_q0)}", flush=True)

# D - W^2 is quadratic in q. Check if it's nonneg on the feasible set.
# q^2 coefficient determines concavity.
# If q^2 coeff < 0: concave in q, min at endpoints.
# If q^2 coeff > 0: convex in q, could be nonneg everywhere.

# q^2 coeff = -16A^2B^2 (should be negative since W^2 has 16A^2B^2q^2 term)
print(f"\nq^2 coeff = {sp.factor(diff_q2)}", flush=True)

# So D - W^2 is CONCAVE in q. We need it >= 0 at the extreme values of q.
# q ranges in [-sqrt(V2), sqrt(V2)] intersected with [-sqrt(V1), sqrt(V1)].
# Since we're working with X >= 0 WLOG, no additional constraint on q.

# The S-lemma: D-W^2 + tau1*(V1-q^2) + tau2*(V2-q^2) >= 0 for all q
# = (diff_q2+tau1+tau2)*q^2 + diff_q1*q + (diff_q0 - tau1*V1_bound - tau2*V2_bound)
# Set tau1+tau2 = -diff_q2 = 16A^2B^2. Then linear in q.
# Need: diff_q1*q + (diff_q0 - tau1*V1 - tau2*V2) >= 0 for all q... not bounded.
# So need tau1+tau2 > -diff_q2. Add delta > 0.
# Then: delta*q^2 + diff_q1*q + c_eff >= 0 for all q.
# Need: diff_q1^2 <= 4*delta*c_eff
# where c_eff = diff_q0 - tau1*V1 - (16A^2B^2+delta-tau1)*V2

# Optimize: tau1 = 0 (best if V2-V1 has correct sign).
# c_eff = diff_q0 - (16A^2B^2+delta)*V2
# For the optimal delta: delta* = |diff_q1|/(2*sqrt(V2)) ... involves sqrt.
# Overall condition: c_eff_0^2 >= diff_q1^2 * V2 where c_eff_0 = diff_q0 - 16A^2B^2*V2

c_eff_0 = sp.expand(diff_q0 - 16*A**2*(1-A)**2*(A-p)*(C-r))
print(f"\nc_eff_0 = diff_q0 - 16A^2B^2*V2 = {c_eff_0}")
print(f"  factored: {sp.factor(c_eff_0)}", flush=True)

# Check c_eff_0 numerically
min_ceff = float('inf')
for _ in range(500000):
    Av = np.random.uniform(0.01, 0.99)
    Cv = np.random.uniform(0, 1-Av)
    pv = np.random.uniform(0, Av)
    rv = np.random.uniform(-Cv, Cv)
    val = float(c_eff_0.subs([(A, Av), (C, Cv), (p, pv), (r, rv)]))
    min_ceff = min(min_ceff, val)
print(f"\nmin(c_eff_0) over 500K: {min_ceff:.8f}", flush=True)

# Check c_eff_0^2 >= diff_q1^2 * V2
check_main = sp.expand(c_eff_0**2 - diff_q1**2 * (A-p)*(C-r))
min_check = float('inf')
for _ in range(500000):
    Av = np.random.uniform(0.01, 0.99)
    Cv = np.random.uniform(0, 1-Av)
    pv = np.random.uniform(0, Av)
    rv = np.random.uniform(-Cv, Cv)
    val = float(check_main.subs([(A, Av), (C, Cv), (p, pv), (r, rv)]))
    min_check = min(min_check, val)
print(f"min(c_eff_0^2 - diff_q1^2*V2) over 500K: {min_check:.8f}", flush=True)

if min_check >= -1e-6:
    print("\n*** KEY CONDITION HOLDS: c_eff_0^2 >= diff_q1^2 * V2 ***")
    if min_ceff >= -1e-6:
        print("*** AND c_eff_0 >= 0 ***")
        print("*** PROOF STRUCTURE FOUND! ***")
        print("\nProof outline:")
        print("1. G >= 0 iff (2ABX - (B-C)p)^2 <= D = (B-C)^2p^2 + 4A^2BC")
        print("2. D - W^2 where W = 2ABX-(B-C)p is a concave quadratic in q")
        print("3. Using S-lemma with V2: D-W^2 + tau*V2_slack >= 0 for all q")
        print("   where tau = 16A^2B^2 + delta and delta chosen to match discriminant")
        print("4. The discriminant condition c_eff_0^2 >= diff_q1^2*V2 is a")
        print("   polynomial inequality in (A,C,p,r) provable on the feasible set")
        print("5. c_eff_0 >= 0 separately")
    else:
        print("c_eff_0 can be negative, but the PRODUCT condition holds.")
        print("Need more careful analysis.")
else:
    print("\nCondition FAILS. Try with both V1 and V2...")

    # Try with tau1 > 0 to improve c_eff
    # c_eff = c_eff_0 - tau1*(V1-V2) - delta*V2
    # V1-V2 = 2(Ar+pC)
    # If Ar+pC > 0: want tau1 = 0 (already tried, failed)
    # If Ar+pC < 0: increasing tau1 increases c_eff!

    # Let tau1 = alpha*(16A^2B^2) for alpha in [0,1]
    # c_eff_alpha = c_eff_0 + alpha*16A^2B^2*(V2-V1) = c_eff_0 - alpha*32A^2B^2*(Ar+pC)

    # For alpha = 1 (tau1 = 16A^2B^2, tau2 = delta):
    # c_eff_1 = diff_q0 - 16A^2B^2*V1 - delta*V2
    c_eff_1 = sp.expand(diff_q0 - 16*A**2*(1-A)**2*(A+p)*(C+r))
    print(f"\nc_eff_1 (using V1): {sp.factor(c_eff_1)}", flush=True)

    min_ceff1 = float('inf')
    for _ in range(500000):
        Av = np.random.uniform(0.01, 0.99)
        Cv = np.random.uniform(0, 1-Av)
        pv = np.random.uniform(0, Av)
        rv = np.random.uniform(-Cv, Cv)
        val = float(c_eff_1.subs([(A, Av), (C, Cv), (p, pv), (r, rv)]))
        min_ceff1 = min(min_ceff1, val)
    print(f"min(c_eff_1) over 500K: {min_ceff1:.8f}", flush=True)

    # Try optimal alpha (depending on sign of Ar+pC)
    # For each point, find best alpha:
    min_G_check = float('inf')
    for _ in range(200000):
        Av = np.random.uniform(0.01, 0.99)
        Cv = np.random.uniform(0, 1-Av)
        pv = np.random.uniform(0, Av)
        rv = np.random.uniform(-Cv, Cv)
        Bv = 1 - Av

        d_q0 = float(diff_q0.subs([(A, Av), (C, Cv), (p, pv), (r, rv)]))
        d_q1_v = float(diff_q1.subs([(A, Av), (C, Cv), (p, pv), (r, rv)]))
        V1v = (Av+pv)*(Cv+rv)
        V2v = (Av-pv)*(Cv-rv)

        # With tau1 = alpha*16A^2B^2, tau2 = (1-alpha)*16A^2B^2 + delta:
        # c_eff = d_q0 - alpha*16*Av**2*Bv**2*V1v - (1-alpha)*16*Av**2*Bv**2*V2v - delta*V2v
        # = d_q0 - 16*Av**2*Bv**2*(alpha*V1v+(1-alpha)*V2v) - delta*V2v
        # Discriminant: d_q1^2 <= 4*delta*c_eff

        # For fixed alpha, optimal delta gives: c_eff_alpha^2 >= d_q1^2*V2v
        # where c_eff_alpha = d_q0 - 16A^2B^2*(alpha*V1+(1-alpha)*V2)

        best_val = -float('inf')
        for alpha in np.linspace(0, 1, 20):
            c_eff = d_q0 - 16*Av**2*Bv**2*(alpha*V1v + (1-alpha)*V2v)
            if V2v > 0:
                check = c_eff**2 - d_q1_v**2 * V2v
            else:
                check = c_eff**2  # V2=0, any delta works
            if check > best_val:
                best_val = check

        min_G_check = min(min_G_check, best_val)

    print(f"\nmin over optimal alpha: {min_G_check:.8f}", flush=True)

    # Also try with both V1 and V2 as denominators:
    # Using V_bound = alpha*V1 + (1-alpha)*V2 for the denominator too.
    # Delta*q^2 + d_q1*q + c_eff >= 0 for all q where q^2 <= V_mix
    # Need: d_q1^2 <= 4*delta*c_eff. But also q^2 <= V_mix.
    # If we use q^2 <= V_mix: then delta plays role differently.

    # Actually the S-lemma uses individual constraints, not combined.
    # The discriminant cond with TWO constraints:
    # delta*q^2 + d_q1*q + c_eff >= 0 for all q with q^2 <= V1 AND q^2 <= V2
    # This is LESS restrictive than q^2 <= V2 alone.
    # So min over {q^2 <= V1 and q^2 <= V2} >= min over {q^2 <= V2}.
    # The S-lemma with both constraints doesn't help more than with just V2.
    # Unless we use tau1 for V1 and tau2 for V2 SEPARATELY.

    # Actually we ARE using both: tau1*V1_slack + tau2*V2_slack.
    # The residual constant is c_eff = d_q0 - tau1*V1 - tau2*V2.
    # To maximize c_eff: put tau on the SMALLER of V1, V2.

    # When Ar+pC > 0: V1 > V2. So V2 is smaller. tau on V2 is less costly.
    # When Ar+pC < 0: V1 < V2. So V1 is smaller. tau on V1 is less costly.

    # Optimal: tau1 on the bigger constraint, tau2 on the smaller.
    # Actually no: tau1*V1 + tau2*V2 with tau1+tau2 = 16A^2B^2+delta.
    # We want to minimize tau1*V1+tau2*V2 = tau1*V1+(16A^2B^2+delta-tau1)*V2 = (16A^2B^2+delta)*V2 + tau1*(V1-V2).
    # Minimize: if V1 > V2, set tau1 = 0. If V1 < V2, set tau1 = 16A^2B^2+delta (i.e., tau2 = 0).

    # So we should use EITHER V1 or V2 depending on which is smaller.
    # When Ar+pC >= 0: V1 >= V2, use tau on V2 (tau1=0). Already tried.
    # When Ar+pC < 0: V1 < V2, use tau on V1 (tau2=0).
    # c_eff with tau2=0: d_q0 - (16A^2B^2+delta)*V1. c_eff_V1 = d_q0 - 16A^2B^2*V1.
    # Need: c_eff_V1^2 >= d_q1^2*V1 (using q^2 <= V1 as the q bound).
    # Wait, with tau2=0, the S-lemma bound on q is from tau1 only:
    # (diff_q2 + tau1)*q^2 + d_q1*q + (d_q0 - tau1*V1) >= 0
    # With tau1 = -diff_q2 = 16A^2B^2: 0*q^2 + d_q1*q + (d_q0 - 16A^2B^2*V1) >= 0
    # This is LINEAR in q, unbounded. Need tau1 > 16A^2B^2.

    # With tau1 = 16A^2B^2 + delta:
    # delta*q^2 + d_q1*q + (d_q0 - (16A^2B^2+delta)*V1) >= 0 for all q
    # = delta*q^2 + d_q1*q + c_eff_V1 - delta*V1
    # Need: d_q1^2 <= 4*delta*(c_eff_V1 - delta*V1)
    # Optimizing: c_eff_V1^2 >= d_q1^2 * V1 (and c_eff_V1 >= 0)

    check_V1 = sp.expand(c_eff_1**2 - diff_q1**2 * (A+p)*(C+r))
    min_cV1 = float('inf')
    for _ in range(500000):
        Av = np.random.uniform(0.01, 0.99)
        Cv = np.random.uniform(0, 1-Av)
        pv = np.random.uniform(0, Av)
        rv = np.random.uniform(-Cv, Cv)
        val = float(check_V1.subs([(A, Av), (C, Cv), (p, pv), (r, rv)]))
        min_cV1 = min(min_cV1, val)
    print(f"\nmin(c_eff_1^2 - d_q1^2*V1) over 500K: {min_cV1:.8f}", flush=True)

    # Now: combine both cases.
    # When Ar+pC >= 0: use tau1=0, need c_eff_0^2 >= d_q1^2*V2 and c_eff_0 >= 0.
    # When Ar+pC < 0: use tau2=0, need c_eff_1^2 >= d_q1^2*V1 and c_eff_1 >= 0.
    print("\n--- Case split on Ar+pC ---")
    min_case_pos = float('inf')
    min_case_neg = float('inf')
    for _ in range(500000):
        Av = np.random.uniform(0.01, 0.99)
        Cv = np.random.uniform(0, 1-Av)
        pv = np.random.uniform(0, Av)
        rv = np.random.uniform(-Cv, Cv)
        ArpC = Av*rv + pv*Cv
        if ArpC >= 0:
            val = float(check_main.subs([(A, Av), (C, Cv), (p, pv), (r, rv)]))
            min_case_pos = min(min_case_pos, val)
        else:
            val = float(check_V1.subs([(A, Av), (C, Cv), (p, pv), (r, rv)]))
            min_case_neg = min(min_case_neg, val)

    print(f"Case Ar+pC >= 0: min(c_eff_0^2 - d_q1^2*V2) = {min_case_pos:.8f}")
    print(f"Case Ar+pC < 0:  min(c_eff_1^2 - d_q1^2*V1) = {min_case_neg:.8f}", flush=True)

    # Also check c_eff sign for each case
    min_ceff0_pos = float('inf')
    min_ceff1_neg = float('inf')
    for _ in range(500000):
        Av = np.random.uniform(0.01, 0.99)
        Cv = np.random.uniform(0, 1-Av)
        pv = np.random.uniform(0, Av)
        rv = np.random.uniform(-Cv, Cv)
        ArpC = Av*rv + pv*Cv
        if ArpC >= 0:
            val = float(c_eff_0.subs([(A, Av), (C, Cv), (p, pv), (r, rv)]))
            min_ceff0_pos = min(min_ceff0_pos, val)
        else:
            val = float(c_eff_1.subs([(A, Av), (C, Cv), (p, pv), (r, rv)]))
            min_ceff1_neg = min(min_ceff1_neg, val)

    print(f"Case Ar+pC >= 0: min(c_eff_0) = {min_ceff0_pos:.8f}")
    print(f"Case Ar+pC < 0:  min(c_eff_1) = {min_ceff1_neg:.8f}", flush=True)
