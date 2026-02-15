#!/usr/bin/env python3
# DEAD END: This script explores the S-lemma + SOS approach for
# rvw_quadratic_ineq. The residual polynomial after S-lemma elimination
# still needs an LP-infeasible certificate — see scripts/RVW_QUADRATIC_PROOF_STATUS.md.
"""
Find algebraic proof of RVW quadratic inequality via S-lemma + SOS.

G = AC + (B-C)pX - ABX^2 where B = 1-A, X = p+2q+r.

G is a quadratic in q. The S-lemma approach:
For a quadratic f(q) = alpha*q^2 + beta*q + gamma >= 0 on the set {q : g_i(q) >= 0},
find tau_i >= 0 such that f - sum tau_i * g_i is nonneg for ALL q.

Concretely: G = a2*q^2 + a1*q + a0 where
  a2 = -4A(1-A)
  a1 = 2(1-A-C)p - 4A(1-A)(p+r) = 2p(1-3A+2A^2-C) - 4A(1-A)r
  a0 = AC + (1-A-C)p(p+r) - A(1-A)(p+r)^2

Constraints on q:
  V1: (A+p)(C+r) - q^2 >= 0
  V2: (A-p)(C-r) - q^2 >= 0

S-lemma says: G >= 0 for all q satisfying V1,V2 iff there exist tau1,tau2 >= 0 such that:
  G(q) - tau1*[(A+p)(C+r) - q^2] - tau2*[(A-p)(C-r) - q^2] >= 0 for ALL q.

The residual is: (a2 + tau1 + tau2)*q^2 + a1*q + (a0 - tau1*V1_bound - tau2*V2_bound)
For this to be nonneg for ALL q:
  1. a2 + tau1 + tau2 >= 0 (upward parabola or constant)
  2. discriminant <= 0: a1^2 - 4*(a2+tau1+tau2)*(a0-tau1*V1_bound-tau2*V2_bound) <= 0

Alternatively, if a2 + tau1 + tau2 = 0, need a1 = 0 and a0 - tau1*V1 - tau2*V2 >= 0.

We still need OTHER constraint multipliers for the nonnegativity in (A,C,p,r).
So the full certificate is:
  G - tau1*V1_slack - tau2*V2_slack = SOS_in_q_and_parameters * other_constraints

The key insight: this SEPARATES the q variable from the rest.
After eliminating q via the S-lemma, we get POLYNOMIAL conditions on (A,C,p,r)
that can potentially be certified by degree-4 Positivstellensatz.
"""

import numpy as np
from fractions import Fraction
from collections import defaultdict
import sympy as sp

# Variables
A, C, p, r = sp.symbols('A C p r', real=True)
B = 1 - A

# Quadratic coefficients in q
a2 = -4*A*(1-A)
a1 = 2*(1-A-C)*p - 4*A*(1-A)*(p+r)
a0 = A*C + (1-A-C)*p*(p+r) - A*(1-A)*(p+r)**2

# Constraint bounds
V1_bound = (A+p)*(C+r)
V2_bound = (A-p)*(C-r)

print("Quadratic in q: G = a2*q^2 + a1*q + a0")
print(f"a2 = {sp.expand(a2)}")
print(f"a1 = {sp.expand(a1)}")
print(f"a0 = {sp.expand(a0)}")
print(f"V1 = {sp.expand(V1_bound)}")
print(f"V2 = {sp.expand(V2_bound)}")

# After S-lemma with tau1, tau2:
# New quadratic: (a2+tau1+tau2)*q^2 + a1*q + (a0 - tau1*V1 - tau2*V2) >= 0 for ALL q
# Need: a2+tau1+tau2 > 0 and discriminant <= 0.
# Discriminant: a1^2 <= 4*(a2+tau1+tau2)*(a0 - tau1*V1 - tau2*V2)

# Let tau1 + tau2 = 4A(1-A) + delta where delta > 0.
# Then the new leading coefficient is delta.
# Need: a1^2 <= 4*delta*(a0 - tau1*V1 - tau2*V2)
# i.e., a0 - tau1*V1 - tau2*V2 >= a1^2 / (4*delta) >= 0

# Also need tau1, tau2 >= 0 individually.

# Let tau1 = alpha * 4A(1-A), tau2 = (1-alpha) * 4A(1-A) + delta
# for alpha in [0,1] and delta > 0.
# Then tau1 + tau2 = 4A(1-A) + delta.
# Need tau2 >= 0: (1-alpha)*4A(1-A) + delta >= 0, OK.

# The key choice: how to split tau1 and tau2.
# Observation from numerics: tau1 = 0 seems to work!
# Let tau1 = 0, tau2 = 4A(1-A) + delta.
# Then:
# c0 = a0 - (4A(1-A) + delta)*V2
# Need: a1^2 <= 4*delta*c0

# c0 = a0 - 4A(1-A)*V2 - delta*V2
# Let's compute a0 - 4A(1-A)*V2:

c0_base = sp.expand(a0 - 4*A*(1-A)*V2_bound)
print(f"\na0 - 4AB*V2 = {c0_base}")
print(f"Factored: {sp.factor(c0_base)}")

# With tau1 = 0, tau2 = 4AB + delta:
# Leading coeff = delta
# Constant = c0_base - delta*V2
# Discriminant condition: a1^2 <= 4*delta*(c0_base - delta*V2)
# This is quadratic in delta: 4*delta*(c0_base - delta*V2) >= a1^2
# => -4*V2*delta^2 + 4*c0_base*delta - a1^2 >= 0
# This is a downward parabola in delta, so feasible iff discriminant >= 0:
# (4*c0_base)^2 - 4*(-4*V2)*(-a1^2) >= 0
# 16*c0_base^2 - 16*V2*a1^2 >= 0
# c0_base^2 >= V2 * a1^2

print("\nCheck: need c0_base^2 >= V2*a1^2")
check = sp.expand(c0_base**2 - V2_bound * a1**2)
print(f"c0_base^2 - V2*a1^2 = {sp.factor(check)}")

# Let me try a cleaner approach. Instead of the general delta,
# use the OPTIMAL delta that maximizes 4*delta*(c0 - delta*V2):
# d/d(delta) [4*delta*c0_base - 4*delta^2*V2] = 4*c0_base - 8*delta*V2 = 0
# delta* = c0_base / (2*V2)
# Maximum = 4 * (c0_base/(2V2)) * (c0_base - c0_base/(2V2)*V2) = 4*(c0_base/(2V2))*(c0_base/2) = c0_base^2/V2

# So the discriminant condition becomes: a1^2 <= c0_base^2/V2, i.e., a1^2*V2 <= c0_base^2.
# Equivalently: (a1*sqrt(V2))^2 <= c0_base^2, i.e., |a1|*sqrt(V2) <= |c0_base|.
# Since we need c0_base >= 0 (for the constant term), this is a1^2*V2 <= c0_base^2.

print("\n=== Reduced problem: show c0_base^2 >= V2*a1^2 ===")
print(f"c0_base = {sp.expand(c0_base)}")
print(f"a1 = {sp.expand(a1)}")
print(f"V2 = {sp.expand(V2_bound)}")

# Actually, we also need c0_base >= 0 and c0_base - delta*V2 >= 0 at delta*.
# c0_base - delta**V2 = c0_base - c0_base/(2V2)*V2 = c0_base/2.
# So need c0_base >= 0.

print("\n=== Also need: c0_base >= 0 ===")
print(f"c0_base factored = {sp.factor(c0_base)}")

# Let me compute c0_base more carefully:
# a0 = AC + (1-A-C)*p*(p+r) - A(1-A)(p+r)^2
#    = AC + (B-C)p(p+r) - AB(p+r)^2
# 4AB*V2 = 4AB*(A-p)(C-r)
# c0_base = AC + (B-C)p(p+r) - AB(p+r)^2 - 4AB(A-p)(C-r)

c0_check = sp.expand(A*C + (B-C)*p*(p+r) - A*B*(p+r)**2 - 4*A*B*(A-p)*(C-r))
print(f"\nc0_base expanded: {c0_check}")
assert sp.expand(c0_check - c0_base) == 0

# Factor c0_base
c0_f = sp.factor(c0_base)
print(f"c0_base factored: {c0_f}")

# Let's try direct expansion
c0_terms = sp.expand(c0_base)
print(f"\nc0_base = {c0_terms}")

# Collect by p,r powers
c0_poly = sp.Poly(c0_base, p, r)
print(f"\nc0_base as polynomial in p,r:")
for monom, coeff in c0_poly.as_dict().items():
    print(f"  p^{monom[0]} * r^{monom[1]} : {coeff}")

a1_poly = sp.Poly(sp.expand(a1), p, r)
print(f"\na1 as polynomial in p,r:")
for monom, coeff in a1_poly.as_dict().items():
    print(f"  p^{monom[0]} * r^{monom[1]} : {coeff}")

# Now the big question: is c0_base^2 - V2*a1^2 >= 0 on the feasible set?
# This is a degree-6 polynomial in (A,C,p,r) (since c0_base is degree 3 and a1 is degree 2).
# The constraint set is simpler (no q variable).

# Let's check numerically first.
import numpy as np

def eval_check(A_v, C_v, p_v, r_v):
    B_v = 1 - A_v
    c0 = A_v*C_v + (B_v-C_v)*p_v*(p_v+r_v) - A_v*B_v*(p_v+r_v)**2 - 4*A_v*B_v*(A_v-p_v)*(C_v-r_v)
    a1_v = 2*(1-A_v-C_v)*p_v - 4*A_v*(1-A_v)*(p_v+r_v)
    V2_v = (A_v-p_v)*(C_v-r_v)
    return c0, c0**2 - V2_v * a1_v**2

# Random tests
np.random.seed(42)
min_check = float('inf')
min_c0 = float('inf')
for _ in range(100000):
    A_v = np.random.uniform(0.01, 0.99)
    C_v = np.random.uniform(0, 1-A_v)
    p_v = np.random.uniform(0, A_v)  # WLOG p >= 0
    r_v = np.random.uniform(-C_v, C_v)
    c0, check_val = eval_check(A_v, C_v, p_v, r_v)
    min_check = min(min_check, check_val)
    min_c0 = min(min_c0, c0)

print(f"\nNumerical check over 100K random points:")
print(f"  min(c0_base): {min_c0:.6f}")
print(f"  min(c0_base^2 - V2*a1^2): {min_check:.6f}")

# c0_base might be negative! Let me check.
# If c0_base < 0, the S-lemma with tau1=0 doesn't work.

# Let me search for c0_base < 0 more aggressively
min_c0 = float('inf')
worst_params = None
for _ in range(1000000):
    A_v = np.random.uniform(0.01, 0.99)
    C_v = np.random.uniform(0, 1-A_v)
    p_v = np.random.uniform(0, A_v)
    r_v = np.random.uniform(-C_v, C_v)
    c0, _ = eval_check(A_v, C_v, p_v, r_v)
    if c0 < min_c0:
        min_c0 = c0
        worst_params = (A_v, C_v, p_v, r_v)

print(f"\nmin(c0_base) over 1M points: {min_c0:.8f}")
print(f"  at A={worst_params[0]:.6f}, C={worst_params[1]:.6f}, p={worst_params[2]:.6f}, r={worst_params[3]:.6f}")

if min_c0 < 0:
    print("  c0_base CAN BE NEGATIVE. Need tau1 > 0 or different approach.")
    # Try with tau1 > 0
    # Or: use BOTH V1 and V2 in a different split.

    # Alternative: tau1 = tau2 = 2AB + delta/2
    # Then c0 = a0 - (2AB+delta/2)(V1+V2)
    # V1+V2 = (A+p)(C+r) + (A-p)(C-r) = 2AC + 2pr - 2... no:
    # = AC+Ar+pC+pr + AC-Ar-pC+pr = 2AC+2pr
    # c0_sym = a0 - (2AB + delta/2)*2*(AC+pr)
    c0_sym = sp.expand(a0 - 2*A*(1-A) * 2*(A*C + p*r))
    print(f"\nWith tau1=tau2=2AB: c0_sym = {sp.expand(c0_sym)}")
    print(f"  factored: {sp.factor(c0_sym)}")

    # Check numerically
    min_c0_sym = float('inf')
    for _ in range(100000):
        A_v = np.random.uniform(0.01, 0.99)
        C_v = np.random.uniform(0, 1-A_v)
        p_v = np.random.uniform(0, A_v)
        r_v = np.random.uniform(-C_v, C_v)
        B_v = 1 - A_v
        c0_v = A_v*C_v + (B_v-C_v)*p_v*(p_v+r_v) - A_v*B_v*(p_v+r_v)**2 - 4*A_v*B_v*(A_v*C_v+p_v*r_v)
        min_c0_sym = min(min_c0_sym, c0_v)
    print(f"  min(c0_sym) over 100K: {min_c0_sym:.8f}")

# Now try: asymmetric split tau1 = alpha, tau2 = 4AB - alpha + delta
# With alpha as a function of (A,C,p,r).
# The key: what alpha makes c0 = a0 - alpha*V1 - (4AB-alpha+delta)*V2 nonneg?
# c0 = a0 - 4AB*V2 + alpha*(V2-V1) - delta*V2
# V2 - V1 = (A-p)(C-r) - (A+p)(C+r) = -2Ar - 2pC = -2(Ar+pC)
# c0 = c0_base - alpha*2(Ar+pC) - delta*V2

# For the discriminant condition:
# a1^2 <= 4*delta*(c0_base - alpha*2(Ar+pC) - delta*V2)
# Optimize over alpha to maximize c0: alpha should be as negative as possible (or small).
# But alpha >= 0 (tau1 >= 0). So alpha = 0 is best if that makes c0_base >= 0.
# But c0_base can be negative.

# If alpha < 0, tau1 < 0 which is not allowed.
# So we need a DIFFERENT decomposition.

print("\n" + "="*60)
print("Alternative: Use additional linear constraints as multipliers")
print("="*60)

# After the S-lemma eliminates q, we need:
# (I) c0_base - delta*V2 >= 0  (for some delta >= 0)
# (II) a1^2 <= 4*delta*(c0_base - delta*V2)

# But (I) with delta=0 requires c0_base >= 0, which can fail.
# So we need to use the REMAINING constraints (h3..h11) to help.

# Idea: instead of requiring c0_base >= 0 pointwise, show:
# c0_base = sum of (nonneg_multiplier * remaining_constraint)

# Or: use a TWO-LAYER S-lemma.
# Layer 1: S-lemma on q with tau dependent on (A,C,p,r).
# Layer 2: Resulting conditions on (A,C,p,r) certified by other constraints.

# Let's figure out the structure of c0_base:
print(f"\nc0_base = a0 - 4AB*V2 =")
# a0 = AC + (B-C)p(p+r) - AB(p+r)^2
# 4AB*V2 = 4AB(A-p)(C-r) = 4AB(AC-Ar-Cp+pr)
# c0_base = AC + (B-C)(p^2+pr) - AB(p+r)^2 - 4AB(AC-Ar-Cp+pr)

# Expand fully:
c0_e = sp.expand(c0_base)
print(c0_e)

# Let me try a different S-lemma split.
# Use ONLY V2 constraint (tau1 = 0) but also multiply by a NONNEG multiplier of (A,C,p,r).
# G * multiplier = ... This changes the problem.

# ACTUALLY: what if we use the S-lemma with tau2 ONLY, but also add extra "free" constraints?
# G = tau2*V2_slack + [delta*q^2 + a1*q + (a0 - tau2*V2)] where tau2 = 4AB + delta
# The bracketed term = delta*q^2 + a1*q + (a0 - (4AB+delta)*V2)
# = delta*q^2 + a1*q + c0_base - delta*V2
# = delta*(q^2 - V2) + a1*q + c0_base
# = -delta*V2_slack + a1*q + c0_base
# Hmm, circular.

# Let me try yet ANOTHER approach: split G into two parts,
# handle each with different constraints.

# G = [AC - ABX^2] + [(B-C)pX]
# Part 1: AC - ABX^2 = AC(1 - BX^2/C) ... no.

# G = AC + (B-C)pX - ABX^2
# = AC(1 - (B/C)X^2) + (B-C)pX   (if C > 0)
# Hmm.

# G = AC - AB(X^2 - (B-C)p/(AB)*X)
# = AC - AB(X - (B-C)p/(2AB))^2 + (B-C)^2*p^2/(4AB)
# = AC + (B-C)^2*p^2/(4AB) - AB*(X - (B-C)p/(2AB))^2

# This is just completing the square. The maximum of G over X is:
# G_max = AC + (B-C)^2*p^2/(4AB)
# at X = (B-C)p/(2AB).

# G >= 0 iff X is in the interval where the parabola is nonneg.
# The roots are at X = [(B-C)p ± sqrt(D)]/(2AB) where D = (B-C)^2*p^2 + 4*A^2*B*C.
# G >= 0 iff 0 <= X <= [(B-C)p + sqrt(D)]/(2AB) (positive root).

# So proving G >= 0 is equivalent to proving X <= X_+ where:
# X_+ = [(B-C)p + sqrt((B-C)^2*p^2 + 4*A^2*BC)]/(2AB)

# And from V1,V2: X = p + 2q + r <= p + r + 2*sqrt((A-p)(C-r)) (from V2).

# So we need: p + r + 2*sqrt((A-p)(C-r)) <= [(B-C)p + sqrt((B-C)^2*p^2 + 4*A^2*BC)]/(2AB)

# Equivalently: 2AB(p+r) + 4AB*sqrt((A-p)(C-r)) <= (B-C)p + sqrt(D)

# This involves square roots on both sides. Not directly algebraic.
# BUT: we can square both sides (carefully) if we can establish signs.

# Let me instead try the LP approach on the S-lemma-reduced problem,
# using tau1 as a polynomial in (A,C,p,r) as well.

# Actually, let me try a more targeted approach.
# From numerics, tau1 ≈ 0 was good. Let me try tau1 = epsilon * something small.

# OR: try the S-lemma with the COMBINED constraint q^2 <= AC + pr
# (this is V1+V2 average).

print("\n" + "="*60)
print("S-lemma with combined constraint q^2 <= AC + pr")
print("="*60)

# Combined: q^2 <= AC + pr
# S-lemma: G + tau*(q^2 - AC - pr) >= 0 for ALL q
# = (a2+tau)*q^2 + a1*q + (a0 - tau*(AC+pr))
# With tau = -a2 = 4AB: leading coeff = 0.
# Need: a1 = 0 (for a constant to be nonneg). But a1 != 0 in general.

# With tau = 4AB + delta:
# = delta*q^2 + a1*q + (a0 - (4AB+delta)*(AC+pr))
# Need: a1^2 <= 4*delta*(a0 - (4AB+delta)*(AC+pr))

c0_combined = sp.expand(a0 - 4*A*(1-A)*(A*C + p*r))
print(f"c0 with combined V: {c0_combined}")
print(f"  factored: {sp.factor(c0_combined)}")

# Numerically check c0_combined
min_c0_comb = float('inf')
for _ in range(100000):
    A_v = np.random.uniform(0.01, 0.99)
    C_v = np.random.uniform(0, 1-A_v)
    p_v = np.random.uniform(0, A_v)
    r_v = np.random.uniform(-C_v, C_v)
    B_v = 1 - A_v
    a0_v = A_v*C_v + (B_v-C_v)*p_v*(p_v+r_v) - A_v*B_v*(p_v+r_v)**2
    c0_v = a0_v - 4*A_v*B_v*(A_v*C_v + p_v*r_v)
    min_c0_comb = min(min_c0_comb, c0_v)
print(f"min(c0_combined) over 100K: {min_c0_comb:.8f}")

# Use WEIGHTED constraint: alpha*V1 + (1-alpha)*V2 for different alpha values
# V_alpha = alpha*(A+p)(C+r) + (1-alpha)*(A-p)(C-r)
# = alpha[AC+Ar+pC+pr] + (1-alpha)[AC-Ar-pC+pr]
# = AC + pr + alpha*(2Ar+2pC) - (2Ar+2pC)  ... hmm
# = AC + pr + (2*alpha-1)*(Ar + pC)

# With tau = 4AB:
# c0_alpha = a0 - 4AB * [AC + pr + (2alpha-1)(Ar+pC)]
# = c0_combined - 4AB*(2alpha-1)*(Ar+pC)

# To maximize c0_alpha, want alpha small when Ar+pC > 0.
# Since p >= 0, r can be negative. Ar+pC can be positive or negative.

# Try alpha_opt = something that makes c0_alpha largest.
# Best: alpha = 0 (use only V2). c0_alpha = c0_base.
# Or alpha = 1 (use only V1). c0_V1 = a0 - 4AB*V1.

c0_V1 = sp.expand(a0 - 4*A*(1-A)*V1_bound)
print(f"\nc0 with only V1: {c0_V1}")

# Try alpha as function of parameters
# Let's try the "balanced" approach: use BOTH V1 and V2 with the WEIGHTED constraint.

# Actually, let me try a completely different decomposition.
# From the status doc insight: At the tight point (V1=V2 both tight), G = 0.
# So near the tight point, G is approximately the Hessian * displacement.
# The proof should use the fact that moving OFF the tight manifold increases G.

# Let me define: S1 = V1_slack = (A+p)(C+r) - q^2, S2 = V2_slack = (A-p)(C-r) - q^2.
# These are both >= 0.
# At the tight manifold: S1 = S2 = 0, so (A+p)(C+r) = (A-p)(C-r) = q^2.
# This gives r = -pC/A and q^2 = C(A^2-p^2)/A.

# Express G in terms of S1, S2, and check the remainder.
# S1 - S2 = (A+p)(C+r) - (A-p)(C-r) = 2Ar + 2pC
# S1 + S2 = (A+p)(C+r) + (A-p)(C-r) - 2q^2 = 2(AC+pr) - 2q^2

# From S1 = (A+p)(C+r) - q^2 and S2 = (A-p)(C-r) - q^2:
# (A+p)(C+r) = S1 + q^2, (A-p)(C-r) = S2 + q^2
# Product: (A^2-p^2)(C^2-r^2) = (S1+q^2)(S2+q^2)
# So: A^2C^2 - A^2r^2 - p^2C^2 + p^2r^2 = S1*S2 + (S1+S2)q^2 + q^4

# Express q^2 in terms of S1, S2:
# From S1: q^2 = (A+p)(C+r) - S1
# From S2: q^2 = (A-p)(C-r) - S2
# Consistent: (A+p)(C+r) - S1 = (A-p)(C-r) - S2 => S1-S2 = 2(Ar+pC)

# Now: G = a2*q^2 + a1*q + a0
# = -4AB*q^2 + a1*q + a0
# Using q^2 = (A+p)(C+r) - S1:
# G = -4AB[(A+p)(C+r) - S1] + a1*q + a0
# = 4AB*S1 + [-4AB(A+p)(C+r) + a0] + a1*q
# = 4AB*S1 + [a0 - 4AB*V1] + a1*q

# Similarly using V2: G = 4AB*S2 + [a0 - 4AB*V2] + a1*q

# So: G = 4AB*S1 + c0_V1 + a1*q  where c0_V1 = a0 - 4AB*V1
# Or:  G = 4AB*S2 + c0_base + a1*q  where c0_base = a0 - 4AB*V2

# We want G >= 0. Since S1 >= 0 and 4AB >= 0, the first term helps.
# Need: c0_V1 + a1*q >= 0 (potentially, if 4AB*S1 can help).
# But we need it for all feasible q, not just the worst case.

# The WEIGHTED version: G = 4AB*(w1*S1 + w2*S2) + [a0 - 4AB*(w1*V1+w2*V2)] + a1*q
# where w1+w2 = 1, w1,w2 >= 0.
# = 4AB*(w1*S1+w2*S2) + c0_w + a1*q
# where c0_w = a0 - 4AB*(w1*V1+w2*V2).

# For G >= 0, sufficient that: c0_w + a1*q >= 0 (since the first term is nonneg).
# a1*q >= 0 depends on signs. Since q can be positive or negative, we need:
# c0_w >= |a1| * |q_max|

# OR: use different weights and handle the linear term differently.

# KEY IDEA: Write G = alpha*S1 + beta*S2 + gamma*q + delta
# and show gamma*q + delta >= 0 for feasible q.

# From G = 4AB*S2 + c0_base + a1*q:
# Need: c0_base + a1*q >= 0 for all q with q^2 <= V2.
# This is: c0_base + a1*q >= 0 for q in [-sqrt(V2), sqrt(V2)].
# For a linear function in q: min is at endpoint.
# If a1 >= 0: min at q = -sqrt(V2), need c0_base - a1*sqrt(V2) >= 0.
# If a1 <= 0: min at q = +sqrt(V2), need c0_base + a1*sqrt(V2) >= 0.
# In both cases: c0_base >= |a1|*sqrt(V2), i.e., c0_base^2 >= a1^2*V2.

# But we showed c0_base can be negative! So G = 4AB*S2 + (negative) + a1*q
# means the 4AB*S2 term needs to contribute.

# BETTER: use DIFFERENT coefficients for S1, S2.
# G = mu*S1 + nu*S2 + (remainder)
# From G = a2*q^2 + a1*q + a0 and q^2 = V1-S1 = V2-S2:
# Using a GENERAL combination of both:
# q^2 = lambda*V1 + (1-lambda)*V2 - lambda*S1 - (1-lambda)*S2
# G = a2*[lambda*V1 + (1-lambda)*V2 - lambda*S1 - (1-lambda)*S2] + a1*q + a0
# = -a2*lambda*S1 - a2*(1-lambda)*S2 + a2*lambda*V1 + a2*(1-lambda)*V2 + a1*q + a0
# = 4AB*lambda*S1 + 4AB*(1-lambda)*S2 + [a0 + a2*lambda*V1 + a2*(1-lambda)*V2] + a1*q

# c0_lambda = a0 - 4AB*[lambda*V1 + (1-lambda)*V2]

# Need: c0_lambda + a1*q >= -4AB*lambda*S1 - 4AB*(1-lambda)*S2
# Since S1,S2 >= 0 and 4AB >= 0, the RHS is <= 0.
# So sufficient: c0_lambda + a1*q >= 0.
# Again: c0_lambda^2 >= a1^2 * (min of V used as q bound).

# The q constraint is q^2 <= min(V1, V2). Let's say q^2 <= V2 (since V2 <= V1 when p,r >= 0 roughly).
# Then: need c0_lambda^2 >= a1^2*V2 (and c0_lambda >= 0).
# c0_lambda = a0 - 4AB*lambda*V1 - 4AB*(1-lambda)*V2
# = c0_base - 4AB*lambda*(V1-V2)
# = c0_base - 4AB*lambda*2(Ar+pC)
# = c0_base - 8AB*lambda*(Ar+pC)

# To make c0_lambda larger: want lambda negative (if Ar+pC > 0) or positive (if Ar+pC < 0).
# But lambda must be in [0,1] (for both coefficients to be nonneg).
# If Ar+pC > 0, want lambda = 0 (c0_lambda = c0_base).
# If Ar+pC < 0, want lambda = 1 (c0_lambda = c0_V1).

# Neither c0_base nor c0_V1 is always nonneg.

# Let me try a COMPLETELY different approach:
# Don't use the S-lemma on q. Instead, use V1 and V2 to derive
# BOTH an upper bound and a lower bound on q, then plug into G.

# From V1: q^2 <= (A+p)(C+r) => q <= sqrt((A+p)(C+r))
# From V2: q^2 <= (A-p)(C-r) => |q| <= sqrt((A-p)(C-r))

# G is linear in q after using q^2 <= V2 (concave quadratic maximized at q*).
# Wait, that's the S-lemma approach again.

# DIFFERENT IDEA: Instead of S-lemma, use the CAUCHY-SCHWARZ form directly.
# From V1: |q| <= sqrt((A+p)(C+r)), and from V2: |q| <= sqrt((A-p)(C-r)).
# These are symmetric constraints. Use the PRODUCT:
# q^4 <= (A+p)(C+r)(A-p)(C-r) = (A^2-p^2)(C^2-r^2)
# q^2 <= sqrt((A^2-p^2)(C^2-r^2))

# From V1+V2 averaging: q^2 <= (AC+pr) (added)/2
# From weighted: A*q^2 <= C*(A^2-p^2)

# The WEIGHTED constraint is strongest. Let me use it.
# S-lemma with A*q^2 <= C*(A^2-p^2):
# G + tau*(A*q^2 - C*(A^2-p^2)) >= 0 for ALL q
# = (a2 + tau*A)*q^2 + a1*q + (a0 - tau*C*(A^2-p^2))
# Setting a2 + tau*A = 0: tau = -a2/A = 4(1-A) = 4B
# Then: a1*q + a0 - 4B*C*(A^2-p^2) >= 0 for ALL q??
# No! With leading coeff = 0 and a1 != 0, this is linear in q, unbounded below.

# So need tau > -a2/A = 4B, say tau = 4B + delta/A:
# Leading: a2 + (4B+delta/A)*A = -4AB + 4AB + delta = delta
# Constant: a0 - (4B+delta/A)*C*(A^2-p^2)
# Disc: a1^2 <= 4*delta*(a0 - (4B+delta/A)*C*(A^2-p^2))

c0_weighted = sp.expand(a0 - 4*(1-A)*C*(A**2 - p**2))
print(f"\nc0 with weighted constraint (tau=4B): {sp.expand(c0_weighted)}")
print(f"  factored: {sp.factor(c0_weighted)}")

# Numerically check
min_c0_w = float('inf')
for _ in range(100000):
    A_v = np.random.uniform(0.01, 0.99)
    C_v = np.random.uniform(0, 1-A_v)
    p_v = np.random.uniform(0, A_v)
    r_v = np.random.uniform(-C_v, C_v)
    B_v = 1 - A_v
    a0_v = A_v*C_v + (B_v-C_v)*p_v*(p_v+r_v) - A_v*B_v*(p_v+r_v)**2
    c0_v = a0_v - 4*B_v*C_v*(A_v**2 - p_v**2)
    min_c0_w = min(min_c0_w, c0_v)
print(f"min(c0_weighted) over 100K: {min_c0_w:.8f}")

# OK let me try a very different approach:
# Instead of the S-lemma, use a DIRECT substitution.
# Set q = s*sqrt((A-p)(C-r)) where -1 <= s <= 1 (from V2).
# Then also need q^2 <= (A+p)(C+r), i.e., s^2*(A-p)(C-r) <= (A+p)(C+r).
# If (A-p)(C-r) <= (A+p)(C+r) (which holds when Ar+pC >= 0), this is automatic for s in [-1,1].

# G = a2*s^2*(A-p)(C-r) + a1*s*sqrt((A-p)(C-r)) + a0
# This involves sqrt.

# SET u = s*sqrt((A-p)(C-r)), so u = q. Back to square one.

# APPROACH: Use the factored form of G at the tight manifold.

# At V1=V2 tight: r = -pC/A, q^2 = C(A^2-p^2)/A.
# Define: dr = r - (-pC/A) = r + pC/A (deviation in r)
# dq2 = q^2 - C(A^2-p^2)/A (deviation in q^2, nonpositive from constraints)

# Express G in terms of (A, C, p, dr, q) where r = -pC/A + dr.
# V2 constraint: q^2 <= (A-p)(C-(-pC/A+dr)) = (A-p)(C+pC/A-dr) = (A-p)((AC+pC)/A - dr) = (A-p)(C(A+p)/A - dr)
# At dr = 0: V2 = (A-p)*C*(A+p)/A = C(A^2-p^2)/A. So q^2 <= C(A^2-p^2)/A. Good.

# G in terms of r = -pC/A + dr:
# p + r = p - pC/A + dr = p(A-C)/A + dr
# X = p + 2q + r = p(A-C)/A + dr + 2q

print("\n" + "="*60)
print("Approach: Express G in terms of deviation from tight manifold")
print("="*60)

dr = sp.Symbol('dr', real=True)
q_sym = sp.Symbol('q', real=True)

r_dev = -p*C/A + dr
X_dev = p + 2*q_sym + r_dev

G_dev = A*C + (1-A-C)*p*X_dev - A*(1-A)*X_dev**2
G_dev_expanded = sp.expand(G_dev)

print(f"G with r = -pC/A + dr:")
G_dev_poly = sp.Poly(G_dev_expanded, q_sym, dr)
print(f"As poly in (q, dr):")
for monom, coeff in sorted(G_dev_poly.as_dict().items()):
    print(f"  q^{monom[0]} * dr^{monom[1]} : {sp.simplify(coeff)}")

# The key question: at dr = 0 and q^2 = C(A^2-p^2)/A, G = 0.
# So G should factor nicely when expressed as deviation from this point.

# Let's also substitute q^2 = C(A^2-p^2)/A - dq2 where dq2 >= 0.
# G is quadratic in q: G = a2_dev*q^2 + a1_dev*q + a0_dev (where a2_dev, a1_dev, a0_dev depend on A,C,p,dr)

a2_dev = G_dev_expanded.coeff(q_sym, 2)
a1_dev = G_dev_expanded.coeff(q_sym, 1)
a0_dev = sp.expand(G_dev_expanded - a2_dev*q_sym**2 - a1_dev*q_sym)

print(f"\na2_dev = {sp.expand(a2_dev)}")
print(f"a1_dev = {sp.expand(a1_dev)}")
print(f"a0_dev = {sp.expand(a0_dev)}")

# G = a2_dev*q^2 + a1_dev*q + a0_dev
# = a2_dev*(C(A^2-p^2)/A - dq2) + a1_dev*q + a0_dev
# = a2_dev*C(A^2-p^2)/A + a0_dev + a1_dev*q - a2_dev*dq2

# The first part (at dr=0, dq2=0, and with q^2 replaced by its value) should be 0!
# But it also depends on q (linear term).

# Actually, G = a2*q^2 + a1*q + a0, and a2 doesn't depend on dr, q.
# a2 = -4A(1-A), same as before.

# At the tight point: q = Q where Q^2 = C(A^2-p^2)/A, dr = 0.
# G(Q, 0) = a2*Q^2 + a1(dr=0)*Q + a0(dr=0)

# We showed earlier that the Q coefficient of G at tight point is 0.
# Hmm wait, that's saying G at the tight point simplifies.

# Actually from the sympy calculation above, after substituting Q^2 = C(A^2-p^2)/A,
# G = (expression with sqrt terms) which was hard to verify = 0.

# Let me just CHECK NUMERICALLY.
def G_at_tight(A_v, C_v, p_v):
    """Evaluate G at the V1=V2 tight manifold."""
    if A_v <= 0 or C_v < 0:
        return None
    r_v = -p_v * C_v / A_v
    if abs(r_v) > C_v + 1e-12:
        return None  # |r| > C
    q2 = C_v * (A_v**2 - p_v**2) / A_v
    if q2 < -1e-12:
        return None
    q_v = np.sqrt(max(0, q2))  # positive root (for X >= 0)
    X_v = p_v + 2*q_v + r_v
    B_v = 1 - A_v
    return A_v*C_v + (B_v - C_v)*abs(p_v)*abs(X_v) - A_v*B_v*X_v**2

# Test
for A_v in [0.3, 0.5, 0.7, 0.9]:
    for C_v in [0.01, 0.1, 0.2]:
        if C_v > 1 - A_v:
            continue
        for p_v in [0, 0.1, A_v/2, A_v*0.9]:
            g = G_at_tight(A_v, C_v, p_v)
            if g is not None:
                print(f"  A={A_v}, C={C_v}, p={p_v}: G={g:.8f}")

print("\n" + "="*60)
print("CONCLUSION from above: G at tight manifold is NOT always 0!")
print("The tight manifold is NOT where G=0.")
print("="*60)

# The issue is that in G = AC + (B-C)*|p|*|X| - AB*X^2,
# the |p|*|X| term uses ABSOLUTE VALUES, but in our formulation
# G = AC + (B-C)*p*X - AB*X^2 we took WLOG p >= 0 and X >= 0.
# But X might not be >= 0 at the tight point!

# With p > 0 and r = -pC/A < 0 and q = sqrt(C(A^2-p^2)/A):
# X = p + 2q + r = p(A-C)/A + 2q.
# For A > C and p > 0: p(A-C)/A > 0 and q > 0, so X > 0. Good.
# For A < C and p > 0: p(A-C)/A < 0. X could be negative.

# Actually wait, the Lean formulation (line 791):
# (p + 2 * q + r) ^ 2 <= (1 - (c / b) ^ 2) * (|p| / a ^ 2) * |p + 2 * q + r| + (c / b) ^ 2
# This uses |p| and |p+2q+r|, not p*X.

# After multiplying by a^2*b^2 and using a^2+b^2=1:
# a^2*b^2*(p+2q+r)^2 <= (b^2-c^2)*|p|*|p+2q+r| + a^2*c^2
# Setting A = a^2, B = b^2, C = c^2, X = |p+2q+r|:
# AB*X^2 <= (B-C)*|p|*X + AC
# i.e., AC + (B-C)*|p|*X - AB*X^2 >= 0

# With |p| (not p) and X = |p+2q+r| (absolute value).
# So we should work with u = |p| (nonneg) and X = |p+2q+r| (nonneg).
# G = AC + (B-C)*u*X - AB*X^2 where u = |p|.

# Now: can we WLOG take p >= 0?
# If we replace p by -p, then q changes sign too (from V1/V2 structure),
# so p+2q+r -> -p-2q+r. And |p+2q+r| -> |-p-2q+r| = |p+2q-r|.
# This is NOT the same as |p+2q+r| unless r=0.
# So we CAN'T simply WLOG p >= 0 while keeping everything else.

# But we CAN take WLOG X >= 0 (since G depends on X^2 and u*X = |p|*|X|).
# So G = AC + (B-C)*|p|*X - AB*X^2 where X >= 0.

# The problem is that |p| appears, not p. In the Lean code, the WLOG is on |p| directly.
# Let me re-read the Lean more carefully.

# From line 784-793:
# rvw_quadratic_ineq proves:
# (p + 2*q + r)^2 <= (1 - (c/b)^2) * (|p|/a^2) * |p+2q+r| + (c/b)^2
# This is equivalent to (with A=a^2, B=b^2=1-A, C=c^2):
# Let X = p+2q+r, u = |p|/A (so u <= 1).
# X^2 <= (1-C/B)*u*|X| + C/B
# X^2 - (B-C)/B * u * |X| - C/B <= 0
# Multiply by AB: AB*X^2 - (B-C)*u*|X|/A*A - AC <= 0  ... hmm, let me be more careful.

# (p+2q+r)^2 <= (1 - (c/b)^2) * (|p|/a^2) * |p+2q+r| + (c/b)^2
# = (1 - C/B) * (|p|/A) * |X| + C/B
# = ((B-C)/B) * (|p|/A) * |X| + C/B

# Multiply both sides by AB:
# AB*X^2 <= (B-C)*|p|*|X|/... hmm this is getting confused.

# Let me just directly multiply by a^2*b^2:
# a^2*b^2*(p+2q+r)^2 <= a^2*b^2 * [(1-c^2/b^2)*(|p|/a^2)*|p+2q+r| + c^2/b^2]
# = a^2*(b^2-c^2)*(|p|/a^2)*|X| + a^2*c^2
# = (b^2-c^2)*|p|*|X| + a^2*c^2
# = (B-C)*|p|*|X| + AC

# So: AB*X^2 <= (B-C)*|p|*|X| + AC, i.e., G = AC + (B-C)*|p|*|X| - AB*X^2 >= 0.

# With u = |p| >= 0 and Y = |X| >= 0:
# G = AC + (B-C)*u*Y - AB*Y^2

# This is the clean formulation. No sign ambiguity.
# Constraints: 0 <= u <= A, 0 <= Y, and the V1/V2 constraints on q.

# Now let me think about what bounds on Y we can derive.
# From V2 (p replaced by ±u, taking the one that gives tighter bound):
# q^2 <= (A-u)(C-|r|) (worst case for V2 when |p| = u)
# Actually V1 and V2 involve p (with sign), not |p|.

# WAIT: Going back to the problem statement.
# The constraints are on the ACTUAL p (with sign), not |p|.
# V1: q^2 <= (a^2+p)(c^2+r)
# V2: q^2 <= (a^2-p)(c^2-r)
# These hold for the specific p (which can be positive or negative).
# |p| <= a^2 is separate.

# The WLOG we can take is: p >= 0 (by symmetry p -> -p, r -> -r, q -> -q).
# Under this WLOG: |p| = p, and |X| = |p+2q+r|. X can still be negative.

# For the inequality G = AC + (B-C)*p*|X| - AB*X^2 >= 0:
# Since G depends on |X| and X^2, and |X|^2 = X^2:
# G = AC + (B-C)*p*|X| - AB*|X|^2

# With Y = |X| >= 0: G = AC + (B-C)*p*Y - AB*Y^2.
# This is a downward parabola in Y (since AB > 0).
# G(0) = AC >= 0.
# G(Y) = 0 at Y_+ = [(B-C)p + sqrt((B-C)^2*p^2 + 4*A^2*BC)]/(2AB).
# Need: Y <= Y_+.

# Y = |p + 2q + r|. Upper bound on Y:
# From rvw_X_le_sum_sq: Y <= A + C (already proved in Lean!).

# So the proof reduces to: EITHER Y <= Y_+ OR use a sharper bound.
# Since G(A+C) can be negative (as we showed), Y <= A+C is not enough.

# We need: Y <= Y_+ = [(B-C)p + sqrt((B-C)^2*p^2 + 4*A^2*BC)]/(2AB)

# Let's check if Y <= A+C always implies G >= 0 at the EXTREMES.
# Actually we need to check whether p being large ENOUGH makes it work.

# When p is large: Y_+ grows linearly with p (since the sqrt term is ~(B-C)p),
# so Y_+ ~ (B-C)p/(AB) for large p.
# Meanwhile Y <= A+C (fixed). So for large p, Y_+ >> Y. Good.

# When p is small (p ≈ 0): Y_+ ≈ sqrt(4*A^2*BC)/(2AB) = sqrt(AC)/B... no.
# Y_+ = sqrt(4*A^2*BC)/(2AB) = 2A*sqrt(BC)/(2AB) = sqrt(C/B)/... hmm.
# Actually Y_+ = [0 + sqrt(0 + 4A^2BC)]/(2AB) = 2A*sqrt(BC)/(2AB) = sqrt(BC)/B*... let me just compute.
# = sqrt(C/B). Hmm: Y_+ = sqrt(4A^2BC)/(2AB) = 2A*sqrt(BC)/(2AB) = sqrt(BC)/B = sqrt(C/B).
# And Y <= 2*sqrt(AC) (from the tight case at p=0, r=0).
# Need: 2*sqrt(AC) <= sqrt(C/B) = sqrt(C/(1-A)).
# 4AC <= C/(1-A), 4A <= 1/(1-A), 4A(1-A) <= 1. YES! Since 4A(1-A) = 1-(2A-1)^2 <= 1.
# Equal when A = 1/2. So at p=0, G = AC - AB*4AC = AC(1-4AB) = AC(2A-1)^2 >= 0.

# So the proof at p=0 is: Y <= 2*sqrt(AC) and G(2*sqrt(AC)) = AC(2A-1)^2 >= 0.
# But we need it for general p!

# The KEY: for general p, we need a bound on Y that DEPENDS on p.
# From the two constraints:
# V1: (X-p-r)^2/4 <= (A+p)(C+r)
# V2: (X-p-r)^2/4 <= (A-p)(C-r)
# With X = p+2q+r, so X-p-r = 2q.

# IDEA: Square both sides of G >= 0 after rearranging.
# G = AC + (B-C)*p*Y - AB*Y^2 >= 0
# (B-C)*p*Y >= AB*Y^2 - AC
# If AB*Y^2 <= AC, we're done.
# If AB*Y^2 > AC, then: (B-C)*p >= AB*Y - AC/Y.
# Hmm, we need p to be large enough. But we also need it for p=0!

# At p=0: G = AC - AB*Y^2. Need Y^2 <= C/B.
# From constraints: q^2 <= (A)(C+r) and q^2 <= A(C-r).
# So q^2 <= A*min(C+r, C-r) = A*(C-|r|).
# Y = |2q+r| <= 2|q| + |r|.
# Need to show: (2|q| + |r|)^2 * AB <= AC when p=0.
# Hmm this isn't quite right either because Y = |p+2q+r| = |2q+r| here.

# Actually with p=0: V1 and V2 both give q^2 <= A(C+r) and q^2 <= A(C-r).
# So q^2 <= A*(C-|r|). Let s = |r| <= C. Then q^2 <= A(C-s).
# Y = |2q+r|. If q >= 0 and r = s: Y = 2q+s, Y^2 = 4q^2 + 4qs + s^2.
# If q >= 0 and r = -s: Y = |2q-s|. Could be 2q-s or s-2q.

# Y^2 <= (2|q|+|r|)^2 = 4q^2 + 4|q||r| + r^2 <= 4A(C-s) + 4*sqrt(A(C-s))*s + s^2

# This is getting complicated. Let me take a step back and think about what approach
# could work in Lean. The SIMPLEST proof structure would be a chain of inequalities
# that nlinarith can close.

print("\n" + "="*60)
print("Final approach: Prove G >= 0 by showing Y^2 <= Y_+^2")
print("="*60)

# G >= 0 iff Y^2 <= [(B-C)pY + AC]/(AB)
# iff AB*Y^2 <= (B-C)*p*Y + AC
# iff AB*Y^2 - (B-C)*p*Y - AC <= 0

# This is true iff Y <= Y_+ (the positive root of the quadratic AB*t^2 - (B-C)*p*t - AC = 0).
# Y_+^2 = [(B-C)pY_+ + AC]/(AB)  ... but Y_+ involves Y_+ on both sides.

# Actually, Y_+ satisfies: AB*Y_+^2 = (B-C)*p*Y_+ + AC.
# So Y_+^2 = ((B-C)*p*Y_+ + AC)/(AB).

# We want to show AB*Y^2 <= (B-C)*p*Y + AC.
# i.e., AB*Y^2 - (B-C)*p*Y <= AC.

# From V1: q^2 <= (A+p)(C+r), i.e., q^2 <= AC + Ar + pC + pr.
# From V2: q^2 <= (A-p)(C-r), i.e., q^2 <= AC - Ar - pC + pr.
# Combined: 2q^2 <= 2AC + 2pr, i.e., q^2 <= AC + pr.
# Weighted: A*q^2 <= C(A^2-p^2) = C*A^2 - C*p^2.

# Y = p + 2q + r.
# Y^2 = p^2 + 4q^2 + r^2 + 4pq + 2pr + 4qr
# AB*Y^2 = AB*(p^2 + 4q^2 + r^2 + 4pq + 2pr + 4qr)
# (B-C)*p*Y = (B-C)*p*(p + 2q + r) = (B-C)*(p^2 + 2pq + pr)

# AB*Y^2 - (B-C)*p*Y = AB*(p^2 + 4q^2 + r^2 + 4pq + 2pr + 4qr)
#                      - (B-C)*(p^2 + 2pq + pr)
# = ABp^2 + 4ABq^2 + ABr^2 + 4ABpq + 2ABpr + 4ABqr
#   - (B-C)p^2 - 2(B-C)pq - (B-C)pr
# = [AB-(B-C)]p^2 + 4ABq^2 + ABr^2 + [4AB-2(B-C)]pq + [2AB-(B-C)]pr + 4ABqr
# = [AB-B+C]p^2 + 4ABq^2 + ABr^2 + [4AB-2B+2C]pq + [2AB-B+C]pr + 4ABqr
# Since B=1-A: AB = A(1-A), AB-B+C = A-A^2-1+A+C = 2A-A^2-1+C = -(1-A)^2+C = C-B^2
# Hmm: AB - (B-C) = AB - B + C = B(A-1) + C = -B^2 + C = C - B^2

# Hmm. Let me just use the combined constraint q^2 <= AC + pr to bound 4ABq^2:
# 4ABq^2 <= 4AB(AC + pr) = 4A^2BC + 4ABpr

# AB*Y^2 - (B-C)pY <= [C-B^2]p^2 + 4A^2BC + 4ABpr + ABr^2 + [4AB-2B+2C]pq + [2AB-B+C]pr + 4ABqr

# This still has q terms. We need to bound the pq and qr terms too.

# |pq| <= p*sqrt(AC+pr) (from combined). This involves sqrt.
# |qr| <= |r|*sqrt(AC+pr).

# Using AM-GM: 2|pq| <= p^2/eps + eps*q^2 for any eps > 0.
# But this introduces free parameters.

# I think the cleanest approach for Lean is:
# 1. Already proved: Y <= A + C.
# 2. Show: if Y <= A+C and p >= 0, then G >= 0 is equivalent to a condition on p.
# 3. Use the constraints to establish that condition.

# Let me check: what is the MINIMUM p needed for G(A+C) >= 0?
# G(A+C) = AC + (B-C)*p*(A+C) - AB*(A+C)^2
# G(A+C) >= 0 iff (B-C)*p*(A+C) >= AB*(A+C)^2 - AC
# iff p >= [AB*(A+C)^2 - AC] / [(B-C)*(A+C)]  (if B > C)
# = [AB*(A+C) - AC/(A+C)] / (B-C)
# = [AB*(A+C) - AC/(A+C)] / (B-C)

# At A=0.5, C=0.1, B=0.5: p >= [0.25*0.6 - 0.05/0.6]/0.4 = [0.15-0.0833]/0.4 = 0.0667/0.4 = 0.167.
# But p can be 0! So G(A+C) < 0 at p=0. Confirmed.

# The point is: Y doesn't reach A+C when p is small.
# At p=0: Y <= 2*sqrt(AC) < A+C (for A != C).
# And G(2*sqrt(AC)) = AC - AB*4AC = AC(1-4AB) = AC*(2A-1)^2 >= 0.

# So we need a TIGHTER Y bound that depends on p.
# From the weighted constraint: A*q^2 <= C*(A^2-p^2)
# q^2 <= C*(A^2-p^2)/A = C*A - C*p^2/A
# Y = p + 2q + r. For Y max over r (with |r| <= C):
# Take r = C (to maximize p+r+2q): Y = p + C + 2q.
# But then V1: q^2 <= (A+p)*2C and V2: q^2 <= (A-p)*0 = 0 (if r=C, C-r=0). So q=0.
# Y = p + C. That's small.
# Take r = -C: V1: q^2 <= (A+p)*0 = 0. q=0. Y = p - C.

# For intermediate r: tradeoff between r and q.
# Max Y = p + r + 2*sqrt(min((A+p)(C+r), (A-p)(C-r)))
# For large A (A >> C): V2 = (A-p)(C-r) is the binding constraint (for small |r|).
# Max over r of [r + 2*sqrt((A-p)(C-r))]:
# d/dr [r + 2*sqrt((A-p)(C-r))] = 1 - (A-p)/sqrt((A-p)(C-r)) = 1 - sqrt((A-p)/(C-r))
# = 0 when C-r = A-p, i.e., r = C-A+p.
# If p < A and C < A (which is common since C <= B = 1-A): r = C-A+p < C (OK) and r >= -C iff C-A+p >= -C iff 2C >= A-p.
# When 2C < A-p: boundary r = -C, and V2 = (A-p)*2C.
# Y = p - C + 2*sqrt(2C(A-p)).

# The bound Y <= p + r_opt + 2*sqrt(V2(r_opt)) is complex.
# In Lean, we might need multiple cases.

# Let me try ONE MORE APPROACH: SDP-based proof at degree 6.

print("\n" + "="*60)
print("Degree 6 SOS via SDP (using sympy)")
print("="*60)

# G is degree 4 in (A,C,p,r,q) with B=1-A.
# Trying a degree-6 Positivstellensatz: m^2 * h_i where deg(m) = 2 and deg(h_i) = 2
# gives degree 6 terms. We match against G (degree 4).
# But ALL terms in our sum are degree >= deg(h_i) >= 1, and any SOS term is degree >= 0.
# We need terms that produce degree-4 monomials.
# SOS: degree 0, 2, 4. h_i: degree 1,2. m^2*h_i: degree 1+, 2+, ...
# Products h_i*h_j: degree 2-4. Triple products: degree 3-6. Etc.

# The issue: all our nonneg basis elements (m^2 * h_i) necessarily have
# monomials of degree >= deg(h_i). So we can't produce a bare constant from h_i*m^2.
# And G has degree 4, not 6. So degree-6 terms must cancel.

# For a degree-6 certificate, we'd need NEGATIVE coefficients on some high-degree terms.
# But all coefficients must be nonneg (since each m^2*h_i is nonneg and multiplied by nonneg coeff).
# So high-degree terms can only cancel via matching from different basis elements.

# The degree-4 Psatz was already dense enough (1038 columns, 126 monomials, full rank).
# The infeasibility means there's NO way to write G as a sum of such terms.

# Maybe the problem is that we NEED SOS POLYNOMIAL multipliers (not just m^2*constant).
# I.e., sigma_i(A,C,p,r,q) * h_i where sigma_i is a full SOS polynomial.

# For a full SOS multiplier of degree d: sigma_i = v^T M v where v = [monomials of degree <= d/2]
# and M is PSD. This requires SDP.

# Let me try the SDP approach with DSOS (diagonally-dominant SOS) which reduces to LP.

print("Trying DSOS (diagonal SOS) relaxation...")

# DSOS: sigma_i = sum_j alpha_j * m_j^2 where alpha_j >= 0.
# This is what we already tried. It was infeasible.

# SDSOS: sigma_i = sum_j (a_j * m_j + b_j * m_k)^2. More terms.
# This includes cross terms m_j*m_k. Let me try this.

# For each constraint h_i, the multiplier sigma_i is SDSOS of some degree.
# sigma_i * h_i contributes to the certificate.

# Actually, let me try the SIMPLEST possible SOS multiplier:
# For h1 (V1, degree 2): sigma_1 is SOS of degree 2.
# sigma_1 = sum_j (a_j + b_j*var)^2 = sum of affine squared terms.
# sigma_1 * h1 is degree 4.

# For h3..h11 (degree 1): sigma_i is SOS of degree 3.
# But SOS of degree 3 is impossible (odd degree). So sigma_i of degree 2.
# sigma_i * h_j is degree 3 (odd). This can't help with degree-4 target.
# Unless paired with another constraint.

# So the affine-multiplier approach naturally leads to:
# sigma_j * (h_i * h_k) where sigma_j is SOS and h_i*h_k is a product of constraints.
# We already tried this (products of pairs).

# What we HAVEN'T tried: SOS multipliers for V1, V2 specifically.
# Sigma = (a0 + a1*q)^2 is SOS of degree 2 in q.
# Sigma * V1_slack is degree 4 in q (V1_slack is degree 2 in q).
# But we only need degree 2 in q (G is degree 2 in q).
# So the coefficient matching might not work.

# WAIT: V1_slack = (A+p)(C+r) - q^2 is quadratic in q with negative leading coeff.
# (a + b*q)^2 * [(A+p)(C+r) - q^2] has degree 4 in q, but we only need degree 2 in G.
# The q^4 and q^3 terms must cancel. This constrains a,b.

# (a+bq)^2 = a^2 + 2abq + b^2*q^2
# (a+bq)^2 * V1_slack = (a^2+2abq+b^2q^2)((A+p)(C+r) - q^2)
# q^4: -b^2
# q^3: -2ab
# q^2: b^2*(A+p)(C+r) - a^2
# q^1: 2ab*(A+p)(C+r)
# q^0: a^2*(A+p)(C+r)

# For no q^4 term: b = 0. Then sigma = a^2 (constant). Already tried.
# For no q^3 term: ab = 0. Either a=0 or b=0.

# So with a SINGLE (a+bq)^2 multiplier for V1, we can't get anything new.
# BUT: with a sum of such terms with DIFFERENT coefficients on V1, V2, and other constraints,
# the q^4 and q^3 terms could cancel across different constraints.

# This is the full SOS+S-lemma approach, which requires SDP.
# Let me set up a SMALL SDP problem.

print("\nSetting up SDP for SOS multipliers on V1 and V2...")

# Basis: we want G = sum_i sigma_i * h_i where sigma_i are SOS.
# For V1, V2 (degree 2): sigma_i = (a_i)^2 (constant). This was tried.
# For linear constraints h_j (degree 1): sigma_j of degree <= 3.
#   SDSOS: sigma_j = (a + b*q)^2 (degree 2 in q).
# sigma_j * h_j: degree 3, which has q terms.

# For product constraints: h_i * h_j with i,j linear => degree 2.
# sigma * h_i * h_j: degree 2 (sigma constant). Already tried.

# NEW: sigma * h_V1 where sigma = (a + b*q)^2 (degree 2 in q).
# The overall degree in q is 4. We need q^4 and q^3 terms to cancel.

# Let me set up the problem systematically.
# Variables: A, C, p, r, q. G depends on all.
# Constraints: V1, V2, plus h3..h11 (no q dependence).

# Certificate basis elements:
# 1. SOS terms: m(A,C,p,r,q)^2 for monomials m of degree <= 2.
# 2. m(A,C,p,r,q)^2 * h_i for each constraint h_i, deg(m) chosen so total deg <= 4.
# 3. m^2 * h_i * h_j for pairs, total deg <= 4.

# IMPORTANT: include q-dependent monomials in the SOS multipliers!
# Previous attempts used m = m(A,C,p,r) only (no q). Let's add q.

from collections import defaultdict

def poly_from_sympy(expr, vars_list):
    """Convert sympy expression to our dict representation."""
    # vars_list = [A, C, p, r, q_sym]
    poly = sp.Poly(sp.expand(expr), *vars_list)
    d = defaultdict(lambda: Fraction(0))
    for monom, coeff in poly.as_dict().items():
        d[monom] = Fraction(coeff)
    return dict(d)

# Setup with q as 5th variable
from sympy import Symbol
q_var = Symbol('q')
vars_5 = [A, C, p, r, q_var]

# G in terms of A,C,p,r,q (B = 1-A, X = p+2q+r)
G_5 = A*C + (1-A-C)*p*(p+2*q_var+r) - A*(1-A)*(p+2*q_var+r)**2
G_5 = sp.expand(G_5)

# Constraints
h_V1 = sp.expand((A+p)*(C+r) - q_var**2)
h_V2 = sp.expand((A-p)*(C-r) - q_var**2)
h_Ap = A - p  # p <= A
h_p = p  # p >= 0
h_Cr = C - r  # r <= C
h_Cpr = C + r  # r >= -C
h_X = p + 2*q_var + r  # X >= 0
h_ACX = A + C - (p + 2*q_var + r)  # X <= A+C
h_1AC = 1 - A - C  # C <= B
h_A = A  # A >= 0
h_C = C  # C >= 0

constraints_5 = [h_V1, h_V2, h_Ap, h_p, h_Cr, h_Cpr, h_X, h_ACX, h_1AC, h_A, h_C]
cnames_5 = ['V1', 'V2', 'A-p', 'p', 'C-r', 'C+r', 'X', 'A+C-X', '1-A-C', 'A', 'C']
cdegs_5 = [sp.Poly(h, *vars_5).total_degree() for h in constraints_5]

print("Constraints and degrees:")
for name, deg in zip(cnames_5, cdegs_5):
    print(f"  {name}: degree {deg}")

G_deg = sp.Poly(G_5, *vars_5).total_degree()
print(f"G degree: {G_deg}")

# Generate SOS basis with q included
def gen_monomials(nvars, max_deg):
    """Generate all monomials up to max_deg in nvars variables."""
    result = []
    def gen(remaining, deg, current):
        if remaining == 0:
            result.append(tuple(current))
            return
        for d in range(deg + 1):
            gen(remaining - 1, deg - d, current + [d])
    gen(nvars, max_deg, [])
    return result

# Build columns: m^2 * h_i where deg(m^2 * h_i) <= 4
nvars = 5
columns_expr = []

# SOS: m^2, deg(m) <= 2
for m_exp in gen_monomials(nvars, 2):
    m = 1
    for i, e in enumerate(m_exp):
        m *= vars_5[i]**e
    m_sq = sp.expand(m**2)
    if sp.Poly(m_sq, *vars_5).total_degree() <= G_deg:
        columns_expr.append(('SOS', m_sq))

# m^2 * h_i
for ci, (h, cdeg) in enumerate(zip(constraints_5, cdegs_5)):
    max_m = (G_deg - cdeg) // 2
    if max_m < 0:
        continue
    for m_exp in gen_monomials(nvars, max_m):
        m = 1
        for i, e in enumerate(m_exp):
            m *= vars_5[i]**e
        term = sp.expand(m**2 * h)
        if sp.Poly(term, *vars_5).total_degree() <= G_deg:
            columns_expr.append((f'm^2*{cnames_5[ci]}', term))

# h_i * h_j (constant multiplier)
for ci in range(len(constraints_5)):
    for cj in range(ci, len(constraints_5)):
        prod_deg = cdegs_5[ci] + cdegs_5[cj]
        if prod_deg > G_deg:
            continue
        max_m = (G_deg - prod_deg) // 2
        if max_m < 0:
            max_m = 0
        prod = sp.expand(constraints_5[ci] * constraints_5[cj])
        for m_exp in gen_monomials(nvars, max_m):
            m = 1
            for i, e in enumerate(m_exp):
                m *= vars_5[i]**e
            term = sp.expand(m**2 * prod)
            if sp.Poly(term, *vars_5).total_degree() <= G_deg:
                columns_expr.append((f'm^2*{cnames_5[ci]}*{cnames_5[cj]}', term))

print(f"\nTotal columns (with q): {len(columns_expr)}")

# Collect monomials
all_monoms_set = set()
G_dict = sp.Poly(G_5, *vars_5).as_dict()
for m in G_dict:
    all_monoms_set.add(m)
for name, expr in columns_expr:
    p_dict = sp.Poly(expr, *vars_5).as_dict()
    for m in p_dict:
        all_monoms_set.add(m)

all_monoms = sorted(all_monoms_set)
monom_idx = {m: i for i, m in enumerate(all_monoms)}
num_monoms = len(all_monoms)
num_cols = len(columns_expr)

print(f"Monomials: {num_monoms}")

# Build matrix
A_matrix = np.zeros((num_monoms, num_cols), dtype=np.float64)
g_vector = np.zeros(num_monoms, dtype=np.float64)

for m, c in G_dict.items():
    if m in monom_idx:
        g_vector[monom_idx[m]] = float(c)

for col_idx, (name, expr) in enumerate(columns_expr):
    p_dict = sp.Poly(expr, *vars_5).as_dict()
    for m, c in p_dict.items():
        if m in monom_idx:
            A_matrix[monom_idx[m], col_idx] += float(c)

rank = np.linalg.matrix_rank(A_matrix)
print(f"Matrix: {num_monoms} x {num_cols}, rank: {rank}")

from scipy.optimize import linprog
c_obj = np.zeros(num_cols)
result = linprog(c_obj, A_eq=A_matrix, b_eq=g_vector,
                bounds=[(0, None)] * num_cols,
                method='highs')

if result.success:
    print("\nSUCCESS with q-dependent basis!")
    sigma = result.x
    active = [(i, sigma[i]) for i in range(num_cols) if sigma[i] > 1e-10]
    print(f"Active terms: {len(active)}")
    for i, val in sorted(active, key=lambda x: -x[1])[:20]:
        print(f"  {columns_expr[i][0]}: {val:.8f}")
else:
    print(f"\nINFEASIBLE with q-dependent basis: {result.message}")
