#!/usr/bin/env python3
# DEAD END: This script discovers D - W^2 = 4AB*G is a tautology, confirming the
# discriminant approach doesn't reduce the problem. All LP/SOS paths are structurally
# infeasible — see scripts/RVW_QUADRATIC_PROOF_STATUS.md.
"""
Key observation: D - W^2 = 4AB * G_original (up to sign).

D - W^2 = 4*A*B * [a0 + a1*q + a2*q^2 ... wait let me check]

Actually the factorization shows:
  D - W^2 (q^0) = -4*A*(A-1) * a0 = 4*A*B * a0
  D - W^2 (q^1) = -8*A*(A-1) * (a1/2) = 4*A*B * a1
  D - W^2 (q^2) = -16*A^2*(A-1)^2 = 4*A*B * (-4*A*B) = 4*A*B * a2

So: D - W^2 = 4*A*B * (a2*q^2 + a1*q + a0) = 4*A*B * G !!!

This is a tautology! (2ABX-(B-C)p)^2 + 4AB*G = D is just expanding G.

So the approach of showing D - W^2 >= 0 is EQUIVALENT to G >= 0, not a reduction.

Let me instead try a completely different approach: show G(q=0) >= 0 (already checked),
then show that G' w.r.t. q has the right sign, or use the concavity argument properly.
"""

import numpy as np
import sympy as sp

A, C, p, r, q = sp.symbols('A C p r q', real=True)
B = 1 - A

# G(q=0) = a0 = AC + (B-C)p(p+r) - AB(p+r)^2
a0 = sp.expand(A*C + (B-C)*p*(p+r) - A*B*(p+r)**2)
print(f"a0 = G(q=0) = {a0}")
print(f"  factor: {sp.factor(a0)}", flush=True)

# Check a0 >= 0 on feasible set
np.random.seed(42)
min_a0 = float('inf')
for _ in range(1000000):
    Av = np.random.uniform(0.001, 0.999)
    Cv = np.random.uniform(0, 1-Av)
    pv = np.random.uniform(0, Av)
    rv = np.random.uniform(-Cv, Cv)
    val = float(a0.subs([(A, Av), (C, Cv), (p, pv), (r, rv)]))
    min_a0 = min(min_a0, val)
print(f"min(a0) over 1M: {min_a0:.10f}", flush=True)

# a0 = AC + (B-C)(p^2+pr) - AB(p+r)^2
# = AC + (B-C)p^2 + (B-C)pr - AB(p^2+2pr+r^2)
# = AC + (B-C-AB)p^2 + (B-C-2AB)pr - ABr^2
# B-C-AB = (1-A)-C-A(1-A) = 1-A-C-A+A^2 = (1-A)^2-C = B^2-C
# B-C-2AB = B-C-2AB = (1-A)-C-2A(1-A) = 1-3A+2A^2-C = B^2+B-2A-C = ... let me just compute
# B-C-2AB = 1-A-C-2A+2A^2 = 2A^2-3A+1-C = (2A-1)(A-1)-C = -(2A-1)B-C

bc_minus_ab = sp.expand((1-A) - C - A*(1-A))
bc_minus_2ab = sp.expand((1-A) - C - 2*A*(1-A))
print(f"\nB-C-AB = {sp.factor(bc_minus_ab)}")
print(f"B-C-2AB = {sp.factor(bc_minus_2ab)}")

# a0 = AC + (B^2-C)p^2 + (-(2A-1)B-C)pr - ABr^2
# = AC - C(p^2+pr) + B^2*p^2 - (2A-1)B*pr - ABr^2
# = C(A - p^2 - pr) + B^2*p^2 - (2A-1)B*pr - ABr^2
# = C(A-p(p+r)) + B[Bp^2 - (2A-1)pr - Ar^2]
# = C*A(1-p(p+r)/A) + B[Bp^2 - (2A-1)pr - Ar^2]

# Hmm. Let me try a different factorization.
# a0 = AC + (B-C)p(p+r) - AB(p+r)^2
# = AC - (p+r)[AB(p+r) - (B-C)p]
# = AC - (p+r)[ABp + ABr - Bp + Cp]
# = AC - (p+r)[B(A-1)p + ABr + Cp]
# = AC - (p+r)[-B^2*p + ABr + Cp]
# = AC - (p+r)[C*p - B^2*p + ABr]
# = AC - (p+r)[p(C-B^2) + ABr]

# C - B^2 = C - (1-A)^2. This can be positive or negative.

# Actually, let me try the KEY OBSERVATION: G(q=0) >= 0 seems to ALWAYS hold.
# This would be a HUGE simplification: if G(q=0) >= 0, then since G is concave in q,
# we just need G at the boundary values of q to be nonneg.

# Wait, G is CONCAVE in q (a2 = -4AB < 0). So its max is in the interior.
# For concave function: G >= 0 on [q_min, q_max] iff G(q_min) >= 0 AND G(q_max) >= 0.
# G(q=0) is NOT an endpoint (unless 0 is an endpoint).
# The actual q domain is [-sqrt(min(V1,V2)), sqrt(min(V1,V2))].
# The concavity means: the min of G on this interval is at one of the endpoints.

# So we DON'T need G(q=0) >= 0 to be relevant. We need G at the boundary.
# But G(q=0) = a0 IS nonneg! And since G is concave with G(0) >= 0 and
# G(q_max) = G at q = sqrt(V2), the minimum is at one of the endpoints.

# The key question is: are BOTH G(q_min) and G(q_max) nonneg?

# From the numerical check above: G at q=sqrt(V2) can be negative! (-0.026)
# And G at q=-sqrt(V2) can be very negative! (-0.68)
# But the feasible domain for q is q^2 <= min(V1, V2), NOT just V2.
# When V1 < V2, the q bound is from V1, not V2.

# Also, G at q=-sqrt(V2) with X = p+2q+r might give X < 0.
# Since the original problem uses |X|, we should really evaluate G(|X|).
# G = AC + (B-C)*p*|X| - AB*X^2 = AC + (B-C)*p*|X| - AB*|X|^2

# If X < 0: |X| = -X. G = AC - (B-C)*p*X - AB*X^2.
# This is a DIFFERENT quadratic in X than the X >= 0 case!
# G = -AB*X^2 - (B-C)*p*X + AC (note the MINUS sign on the linear term)
# = -AB*[X + (B-C)p/(2AB)]^2 + (B-C)^2*p^2/(4AB) + AC

# For X < 0 (i.e., X = -(negative value)):
# Need -AB*X^2 - (B-C)*p*X + AC >= 0
# This is an UPWARD-opening... no, still -AB < 0 coefficient on X^2.
# It's concave in X. Maxed at X = -(B-C)p/(2AB) < 0 (since p >= 0, B >= C).
# f(0) = AC >= 0. f(X) as X -> -inf goes to -inf.

# So for X < 0: G >= 0 iff X >= X_- (the negative root of the new quadratic)
# X_- = [-(B-C)p - sqrt((B-C)^2*p^2 + 4*A^2*BC)]/(2AB) < 0.
# We need X >= X_-, i.e., |X| <= |X_-| = [(B-C)p + sqrt(D)]/(2AB).
# This is the SAME bound as the X > 0 case!

# So the universal condition is: |X| <= [(B-C)p + sqrt(D)]/(2AB) = Y_+.
# And G(|X|) = -AB*|X|^2 + (B-C)*p*|X| + AC >= 0 iff |X| <= Y_+.

# Therefore: the proof reduces to showing Y^2 <= D (where Y = 2AB|X|-(B-C)p is NOT right...
# Actually: AB*Y^2 - (B-C)*p*Y - AC <= 0 where Y = |X| >= 0.

# Anyway, the KEY is: G >= 0 iff |p+2q+r| <= Y_+.

# And Y_+ depends on p. For p = A: Y_+ = [(B-C)*A + sqrt((B-C)^2*A^2+4A^2BC)]/(2AB)
# = A[(B-C) + sqrt((B-C)^2+4BC)]/(2AB) = [(B-C)+sqrt(B^2-2BC+C^2+4BC)]/(2B)
# = [(B-C)+sqrt(B^2+2BC+C^2)]/(2B) = [(B-C)+(B+C)]/(2B) = 2B/(2B) = 1.
# So Y_+(A) = 1. And |X| <= 1 needs |p+2q+r| <= 1.
# From |p| <= A and |2q+r| <= A+C (from AM-GM) ... hmm, that gives |X| <= 2A+C which is > 1.

# But for p < A, Y_+ is larger, so the constraint is weaker.

# KEY INSIGHT: Y_+ is a DECREASING function of... hmm, it depends on p.
# For p=0: Y_+ = sqrt(4A^2BC)/(2AB) = 2A*sqrt(BC)/(2AB) = sqrt(C/B)/... = sqrt(C/(1-A)). Hmm:
# = sqrt(4A^2B*C)/(2AB) = sqrt(4A^2BC)/(2AB). Let me compute:
# 4A^2BC/(2AB)^2 = 4A^2BC/(4A^2B^2) = C/B. So Y_+ = sqrt(C/B).
# Then |X| <= sqrt(C/B). And from V1=V2 at p=0, r=0: q^2 <= AC, |X| = |2q| <= 2*sqrt(AC).
# Need: 2*sqrt(AC) <= sqrt(C/B), i.e., 4AC <= C/B, i.e., 4AB <= 1, i.e., 4A(1-A) <= 1. TRUE!

# This confirms the proof works at p=0. For general p, we need |X| <= Y_+(p).

# Let me compute Y_+^2 - X^2 where X = p+2q+r (using WLOG X >= 0 since we can take |X|).
# Y_+^2 = [(B-C)p + sqrt(D)]^2 / (4A^2B^2)
# This is hard because of sqrt(D).

# ALTERNATIVE APPROACH: Don't compute Y_+. Instead, prove G >= 0 DIRECTLY.

# G = AC + (B-C)*p*Y - AB*Y^2 where Y = |p+2q+r|.
# G is concave in Y with G(0) = AC >= 0.

# CASE 1: p+2q+r >= 0 (Y = p+2q+r).
# G = -4AB*q^2 + [2(B-C)p - 4AB(p+r)]*q + [AC + (B-C)*p*(p+r) - AB*(p+r)^2]
# = a2*q^2 + a1*q + a0

# Since a2 < 0 (concave in q), min is at endpoints.
# Endpoints: q = sqrt(V2) and q = 0 (or q = max from X >= 0, which is -(p+r)/2).
# Wait, if we're in case p+2q+r >= 0: q >= -(p+r)/2. And q^2 <= V2.

# If -(p+r)/2 >= -sqrt(V2): lower bound is q = -(p+r)/2.
# G(q=-(p+r)/2) = G(X=0) = AC >= 0. (Since X = p+2q+r = 0.)
# So G(q=-(p+r)/2) = AC >= 0.
# G(q=sqrt(V2)): need to show this >= 0.

# If -(p+r)/2 < -sqrt(V2): lower bound is q = -sqrt(V2).
# Then X = p+2*(-sqrt(V2))+r = (p+r) - 2*sqrt(V2).
# Need X >= 0: (p+r) >= 2*sqrt(V2), i.e., (p+r)^2 >= 4*V2 = 4*(A-p)(C-r).
# This may or may not hold.

# CASE 2: p+2q+r < 0 (Y = -(p+2q+r)).
# G = AC - (B-C)*p*(p+2q+r) - AB*(p+2q+r)^2
# = -4AB*q^2 + [-2(B-C)*p - 4AB*(p+r)]*q + [AC - (B-C)*p*(p+r) - AB*(p+r)^2]
# Different quadratic in q!

# So we really have TWO quadratics (one for each sign of X).
# For X >= 0: G1(q) = a2*q^2 + a1*q + a0 with q >= -(p+r)/2, q^2 <= V_bounds.
# For X <= 0: G2(q) = a2*q^2 + a1'*q + a0' with q <= -(p+r)/2, q^2 <= V_bounds.
# Both are concave in q, so minimum at boundary.

# KEY: At q = -(p+r)/2 (X = 0): both G1 and G2 equal AC >= 0.
# So the only endpoints to check are:
# For G1: q = sqrt(min(V1,V2)) (max q in the X >= 0 region)
# For G2: q = -sqrt(min(V1,V2)) (min q in the X <= 0 region)

# By symmetry considerations (replacing p by -p, r by -r, q by -q):
# G2 at q = -sqrt(V2') is related to G1 at q = sqrt(V2) by some symmetry.

# Anyway, the CORE problem is: prove G1(sqrt(V2)) >= 0 where V2 = (A-p)(C-r).
# G1(sqrt(V2)) = a2*V2 + a1*sqrt(V2) + a0
# = -4AB*V2 + a1*sqrt(V2) + a0

# This involves sqrt(V2). To avoid it, we can square:
# G1(sqrt(V2)) >= 0 iff
#   a0 - 4AB*V2 >= 0 AND a1 <= 0, OR
#   a0 - 4AB*V2 >= 0 AND a1 >= 0, OR (trivially true if first part holds)
#   (a0 - 4AB*V2 + a1*sqrt(V2))^2 ... no, squaring doesn't preserve direction.

# Actually: let f(t) = a2*t^2 + a1*t + a0 for t = sqrt(V2) >= 0.
# f(0) = a0 >= 0 (verified numerically).
# f is concave in t. So f(t) >= 0 for t in [0, t_max] where t_max is the positive root.
# We need sqrt(V2) <= t_max.
# t_max = (-a1 + sqrt(a1^2 + 4*|a2|*a0)) / (2*|a2|) (using a2 < 0)
# = (a1 + sqrt(a1^2 - 4*a2*a0)) / (-2*a2)

# For f(sqrt(V2)) >= 0:
# a2*V2 + a1*sqrt(V2) + a0 >= 0
# <=> a1*sqrt(V2) >= -(a0 + a2*V2) = -(a0 - 4AB*V2)

# Define c0 = a0 - 4AB*V2 (= a0 + a2*V2 since a2 = -4AB).
# Then: a1*sqrt(V2) + c0 >= 0.

# Case a1 >= 0: a1*sqrt(V2) >= 0. Need c0 >= 0 (i.e., a0 >= 4AB*V2).
#   If c0 >= 0: done.
#   If c0 < 0: need a1*sqrt(V2) >= |c0|, i.e., a1^2*V2 >= c0^2.

# Case a1 < 0: a1*sqrt(V2) < 0. Need c0 >= |a1|*sqrt(V2), i.e., c0 >= 0 and c0^2 >= a1^2*V2.

# In all cases: the condition is c0^2 >= a1^2*V2 WHEN c0 >= 0, OR
#                                   a1^2*V2 >= c0^2 WHEN c0 < 0 AND a1 >= 0.

# Actually: a1*sqrt(V2) + c0 >= 0 is equivalent to:
# If a1 >= 0: automatic if c0 >= 0. If c0 < 0: need a1*sqrt(V2) >= -c0, so a1^2*V2 >= c0^2.
# If a1 < 0: need c0 >= |a1|*sqrt(V2) >= 0, so c0 >= 0 AND c0^2 >= a1^2*V2.

# The condition c0^2 >= a1^2*V2 with c0 >= 0 covers BOTH cases (it's sufficient).
# But c0 = a0 - 4AB*V2 might be negative.

# When c0 < 0 and a1 >= 0: a1*sqrt(V2) + c0 >= 0 iff a1*sqrt(V2) >= -c0 = |c0|.
# Squaring: a1^2*V2 >= c0^2. Note direction: a1^2*V2 >= c0^2, not c0^2 >= a1^2*V2.

# So the COMPLETE condition is:
# (c0 + a1*sqrt(V2))^2 >= ... no. Just: c0 + a1*sqrt(V2) >= 0.

# Let me denote s = sqrt(V2) >= 0. Then:
# Need: c0 + a1*s >= 0 where s >= 0 and s^2 = V2.
# c0 = a0 - 4AB*V2 = a0 - 4AB*s^2.

# So: (a0 - 4AB*s^2) + a1*s >= 0
# i.e., -4AB*s^2 + a1*s + a0 >= 0 (same as G with s = sqrt(V2) = q_max!)
# This is just G(q = s) = G(sqrt(V2)) >= 0. CIRCULAR!

# The issue: f(sqrt(V2)) >= 0 is exactly the condition we're trying to prove.
# The S-lemma / squaring approaches are just restating the same thing.

# We need a FUNDAMENTALLY different approach.

# NEW IDEA: Use V1 and V2 together to bound q more tightly.
# At q = sqrt(V2): V2 slack = 0 (tight). But V1 slack = V1 - V2 = 2(Ar + pC).
# So V1 is NOT tight (unless Ar + pC = 0).

# G at q = sqrt(V2):
# G = -4AB*V2 + a1*sqrt(V2) + a0
# = a0 + a2*V2 + a1*sqrt(V2)
# Use V1 slack: q^2 = V2 <= V1, so V1 - V2 >= 0.
# But this doesn't directly help G.

# ALTERNATIVE: Reduce to a problem in FEWER variables by eliminating r.
# For fixed (A, C, p), optimize G over (q, r) subject to V1, V2, |r| <= C.
# Show that the minimum over the feasible set is >= 0.

# For fixed p, G depends on r through a0 = AC + (B-C)p(p+r) - AB(p+r)^2 and a1.
# G(q) is quadratic in q; the minimum (at boundary) depends on r.
# The minimum over q is: min(G(q_lo), G(q_hi)) where q ranges over feasible values.

# Let me try: for fixed (A, C, p), find the WORST r and then prove G >= 0.

# G depends on r through (p+r) appearing in a0 and a1:
# a0 = AC + (B-C)*p*(p+r) - AB*(p+r)^2
# a1 = 2(B-C)*p - 4AB*(p+r)

# Let u = p + r (so u ranges in [p-C, p+C]). Then:
# a0 = AC + (B-C)*p*u - AB*u^2
# a1 = 2(B-C)*p - 4AB*u
# V2 = (A-p)*(C-r) = (A-p)*(C-(u-p)) = (A-p)*(C+p-u)

# G(q) = -4AB*q^2 + (2(B-C)p - 4ABu)*q + AC + (B-C)pu - ABu^2
# At the V2 boundary: q = sqrt((A-p)(C+p-u)):
# G = -4AB*(A-p)(C+p-u) + (2(B-C)p-4ABu)*sqrt((A-p)(C+p-u)) + AC + (B-C)pu - ABu^2

# This is still complex. Let me try the PARAMETRIC approach.
# Set t = sqrt((A-p)(C+p-u)) >= 0, so u = C+p - t^2/(A-p).
# Then: a0 = AC + (B-C)p(C+p-t^2/(A-p)) - AB(C+p-t^2/(A-p))^2
# Hmm, this substitution is messy.

# Let me try NUMERICAL OPTIMIZATION to understand the worst case.
from scipy.optimize import minimize

def neg_G_at_V2(params):
    """Negative of G at q = sqrt(V2) for minimization."""
    Av, Cv, pv, rv = params
    Bv = 1 - Av
    V2v = (Av-pv)*(Cv-rv)
    if V2v < 0:
        return 0  # infeasible
    qv = np.sqrt(V2v)
    Xv = pv + 2*qv + rv
    Gv = Av*Cv + (Bv-Cv)*pv*abs(Xv) - Av*Bv*Xv**2
    return -Gv

best_neg_G = 0
best_params = None
np.random.seed(42)
for _ in range(10000):
    Av = np.random.uniform(0.01, 0.99)
    Cv = np.random.uniform(0, 1-Av)
    pv = np.random.uniform(0, Av)
    rv = np.random.uniform(-Cv, Cv)
    x0 = [Av, Cv, pv, rv]

    try:
        res = minimize(neg_G_at_V2, x0, method='Nelder-Mead',
                      options={'maxiter': 2000, 'xatol': 1e-12, 'fatol': 1e-12})
        x = res.x
        Av2, Cv2, pv2, rv2 = x
        Bv2 = 1 - Av2
        # Check feasibility
        if (0.001 < Av2 < 0.999 and 0 <= Cv2 <= Bv2 and 0 <= pv2 <= Av2 and abs(rv2) <= Cv2):
            V2v = (Av2-pv2)*(Cv2-rv2)
            V1v = (Av2+pv2)*(Cv2+rv2)
            if V2v >= -1e-10 and V1v >= -1e-10:
                val = -res.fun
                if val < best_neg_G:
                    best_neg_G = val
                    best_params = x
    except:
        pass

print(f"\nmin(G at V2 boundary): {best_neg_G:.10f}")
if best_params is not None:
    Av, Cv, pv, rv = best_params
    print(f"  A={Av:.8f}, C={Cv:.8f}, p={pv:.8f}, r={rv:.8f}")
    Bv = 1 - Av
    V2v = (Av-pv)*(Cv-rv)
    V1v = (Av+pv)*(Cv+rv)
    qv = np.sqrt(max(0, V2v))
    Xv = pv + 2*qv + rv
    print(f"  B={Bv:.8f}, V1={V1v:.8f}, V2={V2v:.8f}, q={qv:.8f}")
    print(f"  X = {Xv:.8f}, |X| = {abs(Xv):.8f}")
    print(f"  G = {Av*Cv + (Bv-Cv)*pv*abs(Xv) - Av*Bv*Xv**2:.10f}")
    # Verify V1 holds
    print(f"  V1 check: q^2={qv**2:.8f} <= V1={V1v:.8f}: {qv**2 <= V1v + 1e-10}")

    # Check: is V1 also nearly tight?
    print(f"  V1-V2 = {V1v-V2v:.8f} = 2(Ar+pC) = {2*(Av*rv+pv*Cv):.8f}")

# The G at V2 boundary can be negative because V1 might NOT hold at that q value!
# We need q^2 <= BOTH V1 AND V2.
# At the negative point: q^2 = V2 but also need q^2 <= V1.
# If V2 > V1: the actual q bound is sqrt(V1), not sqrt(V2).

print("\n--- Corrected: G at q = sqrt(min(V1,V2)) ---")
min_G_correct = float('inf')
for _ in range(1000000):
    Av = np.random.uniform(0.001, 0.999)
    Cv = np.random.uniform(0, 1-Av)
    pv = np.random.uniform(0, Av)
    rv = np.random.uniform(-Cv, Cv)
    Bv = 1 - Av
    V1v = (Av+pv)*(Cv+rv)
    V2v = (Av-pv)*(Cv-rv)
    q_max = np.sqrt(max(0, min(V1v, V2v)))
    for qv in [q_max, -q_max]:
        Xv = pv + 2*qv + rv
        Yv = abs(Xv)
        Gv = Av*Cv + (Bv-Cv)*pv*Yv - Av*Bv*Yv**2
        min_G_correct = min(min_G_correct, Gv)

print(f"min(G at q=±sqrt(min(V1,V2))): {min_G_correct:.10f}", flush=True)

if min_G_correct >= -1e-8:
    print("G IS nonneg at boundary! The inequality holds.")

    # Now: the proof structure is:
    # 1. G is concave in q (a2 = -4AB < 0)
    # 2. G(q=0) = a0 >= 0 (need to prove this)
    # 3. For q in [-q_max, q_max] where q_max = sqrt(min(V1,V2)):
    #    min G = min(G(-q_max), G(q_max)) since G is concave.
    # 4. G(0) >= 0 and the interval [-q_max, q_max] contains 0, so
    #    the minimum is at one of the endpoints.
    # 5. Need: G(q_max) >= 0 AND G(-q_max) >= 0.

    # By symmetry: G(q, p, r) with X = p+2q+r.
    # G(-q) uses X' = p-2q+r. G(-q) = AC + (B-C)*p*|X'| - AB*X'^2.
    # |X'| = |p-2q+r|.

    # Actually, G(-q_max) where q_max = sqrt(V2):
    # X = p - 2*sqrt(V2) + r. This can be negative.
    # G = AC + (B-C)*p*|X| - AB*X^2.
    # If X < 0: |X| = -X. G = AC - (B-C)*p*X - AB*X^2.

    # For the CORRECT proof, we need q_max = sqrt(min(V1, V2)), not just sqrt(V2).

    # Let me structure the proof differently.
    # We want: for ALL q with q^2 <= V1 and q^2 <= V2,
    #   AC + (B-C)*p*|p+2q+r| - AB*(p+2q+r)^2 >= 0.

    # Equivalently: AB*(p+2q+r)^2 <= (B-C)*p*|p+2q+r| + AC.
    # Setting Y = |p+2q+r|: AB*Y^2 - (B-C)*p*Y <= AC.
    # Since AB*Y^2 - (B-C)*p*Y = Y*(AB*Y-(B-C)*p), this is <= 0 when Y <= (B-C)*p/(AB),
    # and grows quadratically after that.

    # For the proof: AB*Y^2 <= (B-C)*p*Y + AC.
    # <=> AB*Y^2 - (B-C)*p*Y - AC <= 0.
    # This holds for Y in [0, Y_+] where Y_+ = [(B-C)*p + sqrt(D)]/(2AB).

    # We need: Y <= Y_+ where Y = |p+2q+r| and q^2 <= min(V1, V2).

    # Y^2 = (p+2q+r)^2 = (p+r)^2 + 4(p+r)q + 4q^2
    # <= (p+r)^2 + 4(p+r)*sqrt(min(V1,V2)) + 4*min(V1,V2)

    # Hmm, Y involves |...|. Let's just bound Y^2:
    # Y^2 = (p+2q+r)^2 <= something.
    # From V1+V2: q^2 <= AC+pr. 4q^2 <= 4AC+4pr.
    # Y^2 = (p+r)^2 + 4(p+r)q + 4q^2.
    # |4(p+r)q| <= 2*((p+r)^2 + 4q^2) by AM-GM. Not sharp.

    # Actually, for the PROOF, maybe we should use the decomposition approach:
    # Prove G(q=0) >= 0 separately (it's a0).
    # Then show the q-dependent part 2(B-C)p*q - 4AB*q^2 is bounded below
    # using the constraints.

    # G = a0 + [2(B-C)p - 4ABu]*q - 4AB*q^2 where u = p+r.
    # = a0 + a1*q + a2*q^2

    # The q-dependent part: a1*q + a2*q^2 = -4AB*q^2 + a1*q = -4AB*(q - a1/(8AB))^2 + a1^2/(16AB)
    # This is maximized at q* = a1/(8AB) with max value a1^2/(16AB).
    # Its minimum on [-s, s] (where s = sqrt(V)) is at one of the endpoints (concave).
    # min(-4AB*s^2 + a1*s, -4AB*s^2 - a1*s) = -4AB*s^2 - |a1|*s

    # So: G >= a0 - 4AB*s^2 - |a1|*s where s = sqrt(min(V1, V2)).
    # = a0 - 4AB*V_min - |a1|*sqrt(V_min)

    # This is what we need to show >= 0. It involves sqrt.

    # Squaring approach: need a0 - 4AB*V_min >= |a1|*sqrt(V_min)
    # Case a0 - 4AB*V_min >= 0:
    #   (a0-4AB*V_min)^2 >= a1^2*V_min
    # Case a0 - 4AB*V_min < 0:
    #   Even with +|a1|*sqrt(V_min), might not recover. But numerics say G >= 0.

    # Actually, let me try to show: a0 - 4AB*min(V1,V2) - |a1|*sqrt(min(V1,V2)) >= 0.
    # Use the CASE SPLIT on which of V1, V2 is smaller.

    # Case V2 <= V1 (Ar+pC >= 0): min(V1,V2) = V2 = (A-p)(C-r).
    # Need: a0 - 4AB*V2 - |a1|*sqrt(V2) >= 0, i.e., c0 >= |a1|*sqrt(V2).
    # This was shown to SOMETIMES fail (c0 can be negative).

    # BUT: we also proved a0 >= 0 (G(q=0) >= 0). And the minimum of G
    # is not just at q = sqrt(V2), but at q such that both V1 AND V2 hold.
    # The interplay between V1 and V2 is crucial.

    # FINAL APPROACH: Prove it using the PRODUCT V1*V2.
    # V1*V2 >= q^4. So q^4 <= (A+p)(C+r)(A-p)(C-r) = (A^2-p^2)(C^2-r^2).
    # Combined with V1+V2 >= 2q^2: q^2 <= (AC+pr).
    # And product: q^2 <= sqrt((A^2-p^2)(C^2-r^2)).

    # For G: need AB*Y^2 <= (B-C)*p*Y + AC where Y = |p+2q+r|.
    # Y^2 = p^2 + 4pq + 4q^2 + 2pr + 4qr + r^2
    # AB*Y^2 = AB*p^2 + 4ABpq + 4ABq^2 + 2ABpr + 4ABqr + ABr^2
    # (B-C)*p*Y = (B-C)*p*|p+2q+r|. With Y >= 0 (WLOG X >= 0):
    # = (B-C)*p*(p+2q+r) = (B-C)p^2 + 2(B-C)pq + (B-C)pr.

    # AB*Y^2 - (B-C)*p*Y = (AB-B+C)*p^2 + (4AB-2B+2C)*pq + 4ABq^2 + (2AB-B+C)*pr + 4ABqr + ABr^2
    # = (C-B^2)*p^2 + 2(2AB-B+C)*pq + 4ABq^2 + (2AB-B+C)*pr + 4ABqr + ABr^2

    # 2AB-B+C = B(2A-1)+C = -(2A-1)(1-A)+C ... hmm.
    # C-B^2 can be negative (when C < B^2 = (1-A)^2).

    # Let me try to use V1 and V2 to eliminate the q terms.
    # 4ABq^2: use q^2 <= AC+pr => 4ABq^2 <= 4AB(AC+pr) = 4A^2BC + 4ABpr.
    # pq: use |pq| <= p*sqrt(AC+pr) (AM-GM gives |pq| <= (p^2+q^2)/2, also q^2 <= AC+pr).
    # qr: use |qr| <= |r|*sqrt(AC+pr).

    # For the pq term: 2(2AB-B+C)*pq.
    # Let alpha = 2AB-B+C.
    # |2*alpha*pq| <= 2|alpha|*p*|q|.
    # Using Cauchy-Schwarz: |q| <= sqrt(AC+pr).
    # 2|alpha|*p*|q| <= 2|alpha|*p*sqrt(AC+pr).

    # For the qr term: 4ABqr.
    # |4ABqr| <= 4AB*|r|*|q| <= 4AB*C*sqrt(AC+pr).

    # These bounds involve sqrt. Let's try AM-GM instead.
    # 2*alpha*pq: by Cauchy-Schwarz, 2|alpha*p*q| <= alpha^2*p^2/epsilon + epsilon*q^2.
    # Choose epsilon to make things cancel.

    # Actually, let me just try the direct Positivstellensatz approach at DEGREE 6.
    # The key insight: including q in the monomial basis SHOULD help, since the problem
    # naturally involves q.

    # But our earlier attempt (with 378 columns) was infeasible at degree 4.
    # Let me try degree 6.

    print("\n" + "="*60)
    print("DIRECT PROOF: G(q=0) >= 0")
    print("="*60)

    # a0 = AC + (B-C)p(p+r) - AB(p+r)^2
    # This is a polynomial in (A,C,p,r). Let's find a Psatz certificate.

    a0_poly = sp.expand(A*C + ((1-A)-C)*p*(p+r) - A*(1-A)*(p+r)**2)
    print(f"a0 = {a0_poly}")
    print(f"a0 factored = {sp.factor(a0_poly)}", flush=True)

    # a0 = AC + (p+r)[(B-C)p - AB(p+r)]
    # = AC + (p+r)[Bp - Cp - ABp - ABr]
    # = AC + (p+r)[p(B-C-AB) - ABr]
    # = AC + (p+r)[p(B^2-C) - ABr]
    # = AC + p(p+r)(B^2-C) - AB*r*(p+r)

    # At r = 0: a0 = AC + p^2*(B^2-C) - 0 = AC + p^2(B^2-C).
    # If C >= B^2: a0 >= AC >= 0.
    # If C < B^2: a0 = AC + p^2(B^2-C) >= 0 since both terms nonneg.
    # Wait: AC >= 0 and p^2(B^2-C) >= 0 when C <= B^2. So a0(r=0) >= 0.

    # At r = C: p+r = p+C. a0 = AC + (p+C)(B^2-C)p - AB*C*(p+C)
    # At r = -C: p+r = p-C. a0 = AC + (p-C)(B^2-C)p - AB*(-C)*(p-C)
    # = AC + (p-C)(B^2-C)p + ABC(p-C)

    # For r != 0: the -ABr(p+r) term can make things negative.
    # But we showed numerically a0 >= 0.

    # a0 = AC + (B-C)p(p+r) - AB(p+r)^2
    # = AC - (p+r)[(p+r)AB - (B-C)p]
    # = AC - (p+r)*[AB(p+r) - (B-C)p]
    # = AC - (p+r)*[ABr + (AB-B+C)p]
    # = AC - (p+r)*[ABr + (C-B^2)p]
    # = AC - (p+r)*[ABr - (B^2-C)p]

    # When (B^2-C)p >= ABr: the bracket is <= 0, so -(p+r)*(...) >= 0 if p+r >= 0.
    # p+r >= 0 when r >= -p (which holds since r >= -C and p <= A; not always p >= C though).
    # Hmm, p >= 0 and r >= -C, so p+r >= p-C. If p >= C: p+r >= 0. If p < C: p+r might be < 0.

    # This is getting complicated. Let me just try the LP approach for a0 >= 0.
    # Constraints on (A,C,p,r):
    # h1 = A, h2 = 1-A, h3 = C, h4 = 1-A-C, h5 = p, h6 = A-p, h7 = C-r, h8 = C+r

    from scipy.optimize import linprog
    from collections import defaultdict

    # Variables: A, C, p, r (4 vars, indices 0,1,2,3)
    def gen_mons(n, d):
        if n == 0: return [()]
        result = []
        for i in range(d+1):
            for rest in gen_mons(n-1, d-i):
                result.append((i,) + rest)
        return result

    # a0 as polynomial in 4 vars
    a0_sp = sp.Poly(a0_poly, A, C, p, r)
    a0_dict = dict(a0_sp.as_dict())
    a0_deg = a0_sp.total_degree()
    print(f"\na0 degree: {a0_deg}", flush=True)

    # Constraints
    h_list = [A, 1-A, C, 1-A-C, p, A-p, C-r, C+r]
    h_names = ['A', '1-A', 'C', '1-A-C', 'p', 'A-p', 'C-r', 'C+r']
    h_degs = [sp.Poly(h, A, C, p, r).total_degree() for h in h_list]

    # Build columns: m^2*h_i, products m^2*h_i*h_j
    columns_4v = []

    # SOS
    for m in gen_mons(4, a0_deg//2):
        m_expr = A**m[0] * C**m[1] * p**m[2] * r**m[3]
        term = sp.expand(m_expr**2)
        if sp.Poly(term, A, C, p, r).total_degree() <= a0_deg:
            columns_4v.append(('SOS', term))

    # m^2*h_i
    for ci, (h, hd) in enumerate(zip(h_list, h_degs)):
        md = (a0_deg - hd) // 2
        if md < 0: continue
        for m in gen_mons(4, md):
            m_expr = A**m[0] * C**m[1] * p**m[2] * r**m[3]
            term = sp.expand(m_expr**2 * h)
            if sp.Poly(term, A, C, p, r).total_degree() <= a0_deg:
                columns_4v.append((f'{h_names[ci]}', term))

    # m^2*h_i*h_j
    for ci in range(len(h_list)):
        for cj in range(ci, len(h_list)):
            pd = h_degs[ci] + h_degs[cj]
            if pd > a0_deg: continue
            md = (a0_deg - pd) // 2
            if md < 0: continue
            for m in gen_mons(4, md):
                m_expr = A**m[0] * C**m[1] * p**m[2] * r**m[3]
                term = sp.expand(m_expr**2 * h_list[ci] * h_list[cj])
                if sp.Poly(term, A, C, p, r).total_degree() <= a0_deg:
                    columns_4v.append((f'{h_names[ci]}*{h_names[cj]}', term))

    print(f"\nColumns for a0 >= 0: {len(columns_4v)}")

    # Collect monomials
    all_mons = set()
    for m, c in a0_dict.items():
        all_mons.add(m)
    for name, expr in columns_4v:
        pd = sp.Poly(expr, A, C, p, r).as_dict()
        for m in pd:
            all_mons.add(m)

    all_mons = sorted(all_mons)
    mon_idx = {m: i for i, m in enumerate(all_mons)}
    n_mons = len(all_mons)
    n_cols = len(columns_4v)
    print(f"Monomials: {n_mons}")

    # Build LP
    A_mat = np.zeros((n_mons, n_cols))
    g_vec = np.zeros(n_mons)

    for m, c in a0_dict.items():
        if m in mon_idx:
            g_vec[mon_idx[m]] = float(c)

    for col_i, (name, expr) in enumerate(columns_4v):
        pd = sp.Poly(expr, A, C, p, r).as_dict()
        for m, c in pd.items():
            if m in mon_idx:
                A_mat[mon_idx[m], col_i] += float(c)

    rank = np.linalg.matrix_rank(A_mat)
    print(f"Matrix: {n_mons}x{n_cols}, rank: {rank}")

    c_obj = np.zeros(n_cols)
    result = linprog(c_obj, A_eq=A_mat, b_eq=g_vec,
                    bounds=[(0, None)] * n_cols, method='highs')

    if result.success:
        print("\nSUCCESS: a0 >= 0 has Psatz certificate!")
        sigma = result.x
        active = [(i, sigma[i]) for i in range(n_cols) if sigma[i] > 1e-10]
        print(f"Active terms: {len(active)}")
        for i, val in sorted(active, key=lambda x: -x[1])[:15]:
            print(f"  {columns_4v[i][0]}: {val:.8f}")
    else:
        print(f"\nINFEASIBLE for a0 >= 0: {result.message}")

else:
    print("G is NEGATIVE at corrected boundary. Something is wrong.")
    # Double-check with actual V1 constraint
    for _ in range(5):
        while True:
            Av = np.random.uniform(0.01, 0.99)
            Cv = np.random.uniform(0, 1-Av)
            pv = np.random.uniform(0, Av)
            rv = np.random.uniform(-Cv, Cv)
            Bv = 1 - Av
            V1v = (Av+pv)*(Cv+rv)
            V2v = (Av-pv)*(Cv-rv)
            if V1v > 0 and V2v > 0:
                break
        q_bound = np.sqrt(min(V1v, V2v))
        for qv in [q_bound, -q_bound, 0]:
            Xv = pv + 2*qv + rv
            Yv = abs(Xv)
            Gv = Av*Cv + (Bv-Cv)*pv*Yv - Av*Bv*Yv**2
            if Gv < -1e-6:
                print(f"  VIOLATION: A={Av:.6f} C={Cv:.6f} p={pv:.6f} r={rv:.6f} q={qv:.6f} G={Gv:.8f}")
                print(f"    V1={V1v:.6f} V2={V2v:.6f} q^2={qv**2:.6f} min={min(V1v,V2v):.6f}")
