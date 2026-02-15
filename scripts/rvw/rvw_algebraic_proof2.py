#!/usr/bin/env python3
# DEAD END: This script explores concavity-in-X variable elimination for
# rvw_quadratic_ineq. The resulting subproblems still require SOS certificates
# that are LP-infeasible — see scripts/RVW_QUADRATIC_PROOF_STATUS.md.
"""
Find an algebraic proof of the RVW quadratic inequality using variable elimination.

The key insight: G = A*C + (B-C)*p*X - A*B*X^2 is CONCAVE in X (since A*B > 0).
So G >= 0 on [0, X_max] iff G(0) >= 0 and G(X_max) >= 0.

G(0) = A*C >= 0 (trivially true).

The hard part: what is X_max? We need to use the V1/V2 constraints to bound X.

From V1: q^2 <= (A+p)(C+r)  and  q = (X-p-r)/2
  => (X-p-r)^2 <= 4(A+p)(C+r)
  => X <= p + r + 2*sqrt((A+p)(C+r))

From V2: q^2 <= (A-p)(C-r)
  => (X-p-r)^2 <= 4(A-p)(C-r)
  => X <= p + r + 2*sqrt((A-p)(C-r))

Strategy: Use V2 to bound X, then show G(X_max) >= 0 where X_max = p+r+2*sqrt((A-p)(C-r)).

But this involves square roots. Instead, we can use the concavity directly:
G(X) = -A*B*X^2 + (B-C)*p*X + A*C
This is maximized at X* = (B-C)*p/(2*A*B)
G(X*) = A*C + (B-C)^2*p^2/(4*A*B)

For G(X) >= 0, we need X to be between the two roots:
X = [(B-C)*p ± sqrt((B-C)^2*p^2 + 4*A^2*B*C)] / (2*A*B)

The positive root is:
X_+ = [(B-C)*p + sqrt((B-C)^2*p^2 + 4*A^2*B*C)] / (2*A*B)

So we need: X <= X_+, i.e., X^2*A*B - (B-C)*p*X <= A*C.

Equivalently, from V2: (X-p-r)^2 <= 4*(A-p)*(C-r), i.e. X <= p+r+2*sqrt((A-p)*(C-r)).

So the proof reduces to showing that the V2 bound on X implies G(X) >= 0.

Let me try substituting X = p + r + 2*t where t^2 <= (A-p)(C-r) (= V2 constraint, t=q).

Then G = A*C + (B-C)*p*(p+r+2t) - A*B*(p+r+2t)^2

Let's expand and try to show G >= 0 using t^2 <= (A-p)(C-r).
"""

import sympy as sp
from sympy import symbols, expand, collect, factor, simplify, sqrt, Rational
from sympy import Poly, groebner, solve
from fractions import Fraction

A, C, p, r, t, B = symbols('A C p r t B', real=True)

# B = 1 - A
Bval = 1 - A

# X = p + r + 2*t (where t = q, and t^2 <= (A-p)(C-r))
X = p + r + 2*t

# G = A*C + (B-C)*p*X - A*B*X^2
G = A*C + (Bval - C)*p*X - A*Bval*X**2
G_expanded = expand(G)

print("G(X = p+r+2t) =")
print(G_expanded)
print()

# Constraint: t^2 <= (A-p)(C-r)
# Let's write: slack = (A-p)(C-r) - t^2 >= 0
slack = (A-p)*(C-r) - t**2

# We want to show: G >= 0 given slack >= 0 and other bounds.
# Try: G = f(A,C,p,r,t) * slack + g(A,C,p,r,t)
# where f >= 0 on the feasible set and g >= 0 on the feasible set.

# First, let's see if G is a polynomial multiple of slack + something nice.
# Polynomial division of G by slack w.r.t. t^2:
# In G, the t^2 term is: -4*A*B (from -A*B*(2t)^2 = -4*A*B*t^2)
# Replace t^2 with (A-p)(C-r) - slack:
G_sub = G_expanded.subs(t**2, (A-p)*(C-r) - sp.Symbol('slack'))
G_sub_expanded = expand(G_sub)
print("G with t^2 = (A-p)(C-r) - slack:")
print(G_sub_expanded)
print()

# Actually let's be more systematic. Collect G by powers of t.
G_collected = collect(expand(G_expanded), t)
print("G collected by t:")
print(G_collected)
print()

# G = coeff_t2 * t^2 + coeff_t1 * t + coeff_t0
coeff_t2 = G_expanded.coeff(t, 2)
coeff_t1 = G_expanded.coeff(t, 1)
coeff_t0_full = G_expanded - coeff_t2 * t**2 - coeff_t1 * t
coeff_t0 = expand(coeff_t0_full)

print(f"coeff of t^2: {expand(coeff_t2)}")
print(f"coeff of t^1: {expand(coeff_t1)}")
print(f"coeff of t^0: {expand(coeff_t0)}")
print()

# G = coeff_t2 * t^2 + coeff_t1 * t + coeff_t0
# Using slack: t^2 = (A-p)(C-r) - slack
# G = coeff_t2 * ((A-p)(C-r) - slack) + coeff_t1 * t + coeff_t0
# G = coeff_t2*(A-p)(C-r) + coeff_t0 + coeff_t1*t - coeff_t2*slack
# G = [something] + coeff_t1*t + (-coeff_t2)*slack

# So: G = (-coeff_t2) * slack + (coeff_t2*(A-p)(C-r) + coeff_t0) + coeff_t1*t

minus_coeff_t2 = expand(-coeff_t2)
remainder = expand(coeff_t2 * (A-p)*(C-r) + coeff_t0)

print(f"-coeff_t2 = {minus_coeff_t2}")
print(f"remainder (no t) = {expand(remainder)}")
print(f"coeff_t1 = {expand(coeff_t1)}")
print()

# So G = 4*A*(1-A) * slack + remainder + coeff_t1 * t
# The slack term is >= 0 if A*(1-A) >= 0 (true for 0 < A < 1)
# We need: remainder + coeff_t1 * t >= 0

print("=" * 60)
print("G = 4*A*(1-A) * [(A-p)(C-r) - t^2]")
print(f"  + ({expand(coeff_t1)}) * t")
print(f"  + ({expand(remainder)})")
print("=" * 60)
print()

# Let's factor remainder
remainder_factored = factor(remainder)
print(f"remainder factored: {remainder_factored}")
print()

# remainder + coeff_t1 * t is a LINEAR function of t.
# For this to be nonneg for all t with t^2 <= (A-p)(C-r), we need...
# Actually t can be positive or negative (q can have either sign).
# So we need: remainder + coeff_t1*t >= 0 for |t| <= sqrt((A-p)(C-r))
# Actually we took X >= 0, so X = p+r+2t >= 0, i.e., t >= -(p+r)/2.
# And from V1: t^2 <= (A+p)(C+r), from V2: t^2 <= (A-p)(C-r).

# The constraint is really:
# G = 4A(1-A) * V2_slack + linear_in_t
# So we need: linear_in_t >= 0 on the feasible region for t.

# linear_in_t = coeff_t1 * t + remainder
# = expansion involving A, C, p, r, t

# For the linear function of t, its minimum on an interval is at one of the endpoints.
# If coeff_t1 > 0, minimum is at t = t_min = max(-(p+r)/2, -sqrt((A-p)(C-r)))
# If coeff_t1 < 0, minimum is at t = t_max = sqrt((A-p)(C-r))
# If coeff_t1 = 0, it's just remainder >= 0.

# Let's check what coeff_t1 looks like
c1 = expand(coeff_t1.subs(B, 1-A))
print(f"coeff_t1 = {c1}")

# coeff_t1 = 2*(B-C)*p - 4*A*B*(p+r)
# = 2(1-A-C)*p - 4A(1-A)(p+r)
# = 2p - 2Ap - 2Cp - 4Ap + 4A^2*p - 4A(1-A)r
# = 2p(1 - 3A + 2A^2 - C) - 4A(1-A)r
# This can be positive or negative.

# Let's try a different approach: instead of using V2 alone, use BOTH V1 and V2.
# We have 4 degrees of freedom in combining:
# G = alpha * V1_slack + beta * V2_slack + gamma*something + ...
# where V1_slack = (A+p)(C+r) - t^2, V2_slack = (A-p)(C-r) - t^2

print("\n" + "="*60)
print("Approach 2: Use both V1 and V2 as multipliers")
print("="*60)

# G = alpha(A,C,p,r,t) * V1_slack + beta(A,C,p,r,t) * V2_slack + nonneg_remainder
# where V1_slack = (A+p)(C+r) - t^2, V2_slack = (A-p)(C-r) - t^2

V1_slack = (A+p)*(C+r) - t**2
V2_slack = (A-p)*(C-r) - t**2

# Let alpha, beta be LINEAR in t (since G has degree 1 in t after removing t^2 terms).
# alpha = a0 + a1*t
# beta = b0 + b1*t
# Then alpha*V1_slack + beta*V2_slack has terms up to t^3, but G has max degree 2 in t.
# So we need the t^3 coefficient to be 0: -a1 - b1 = 0, i.e., b1 = -a1.
# Also alpha >= 0 and beta >= 0 on the feasible set.

# Actually, for Positivstellensatz we want alpha,beta to be SOS (sums of squares).
# If alpha and beta are constants (degree 0), then:
# alpha*V1 + beta*V2 = alpha*(A+p)(C+r) + beta*(A-p)(C-r) - (alpha+beta)*t^2
# Matching t^2 coefficient: -(alpha+beta) must equal coeff_t2 = -4A(1-A)
# So alpha + beta = 4*A*(1-A). But alpha,beta are constants, not functions of A.
# This doesn't work for constant alpha, beta.

# Let alpha, beta be functions of A,C,p,r (not t):
a0, b0 = symbols('a0 b0')

# G = a0 * V1_slack + b0 * V2_slack + nonneg_residual
combined = expand(a0 * V1_slack + b0 * V2_slack)
residual = expand(G_expanded - combined)
print(f"\nG - a0*V1 - b0*V2 (collected by powers of t):")
res_collected = collect(residual, t)
print(res_collected)

# The t^2 coefficient of residual should be >= 0 or we handle it.
res_t2 = residual.coeff(t, 2)
res_t1 = residual.coeff(t, 1)
res_t0 = expand(residual - res_t2*t**2 - res_t1*t)

print(f"\nresidual t^2 coeff: {expand(res_t2)}")
print(f"residual t^1 coeff: {expand(res_t1)}")
print(f"residual t^0 coeff: {expand(res_t0)}")

# For residual to have no t^2 or t^1 terms:
# res_t2 = 0: -4A(1-A) + a0 + b0 = 0 => a0 + b0 = 4A(1-A)
# res_t1 = 0: 2(1-A-C)p - 4A(1-A)(p+r) = ... hmm this doesn't depend on a0, b0

# Actually: combined = a0*(A+p)(C+r) + b0*(A-p)(C-r) - (a0+b0)*t^2
# So the t^2 coeff of G - combined = -4A(1-A) + (a0+b0)
# For this to be 0: a0+b0 = 4A(1-A)

# The t^1 coeff of combined is 0 (no t in V1_slack or V2_slack except t^2).
# Wait, V1_slack = (A+p)(C+r) - t^2, V2_slack = (A-p)(C-r) - t^2. These don't have t^1 terms!
# So the t^1 coeff of residual is just coeff_t1 (the original t^1 coefficient of G).

print(f"\ncoeff_t1 of G: {expand(coeff_t1)}")

# So the residual after subtracting a0*V1 + b0*V2 is:
# [coeff_t0 - a0*(A+p)(C+r) - b0*(A-p)(C-r)] + coeff_t1*t + [a0+b0 - 4A(1-A)]*t^2
# Setting a0+b0 = 4A(1-A) and introducing s = a0 - b0 (so a0 = 2A(1-A)+s/2, b0 = 2A(1-A)-s/2):
# residual = [coeff_t0 - (2A(1-A)+s/2)*(A+p)(C+r) - (2A(1-A)-s/2)*(A-p)(C-r)] + coeff_t1*t

# The key is that we still have a LINEAR function of t, and we need it to be nonneg.
# For a linear function of t to be nonneg on an interval, its value at the endpoints must be nonneg.

# Let's try a totally different approach: eliminate t entirely.

print("\n" + "="*60)
print("Approach 3: Direct quadratic analysis in t")
print("="*60)

# G is quadratic in t:
# G = ct2 * t^2 + ct1 * t + ct0
# where ct2 = -4A(1-A) < 0 (concave in t!)
# So G is MAXIMIZED at some t* and G >= 0 on some interval around t*.
# We need: for all t in the feasible set, G(t) >= 0.

# Since G is concave in t, the minimum of G on the feasible set [t_lo, t_hi]
# is at one of the endpoints.

# Feasible t: t^2 <= (A-p)(C-r) AND t^2 <= (A+p)(C+r) AND t >= -(p+r)/2 (from X >= 0)
# Since (A-p)(C-r) <= (A+p)(C+r) when p,r >= 0 (we're in the WLOG p >= 0 case),
# the binding constraint is V2: t^2 <= (A-p)(C-r).
# Also t >= -(p+r)/2.

# The feasible set for t is: -sqrt((A-p)(C-r)) <= t <= sqrt((A-p)(C-r))
# intersected with t >= -(p+r)/2.

# Since G is concave in t, we need G(t_lo) >= 0 and G(t_hi) >= 0.
# t_hi = sqrt((A-p)(C-r))
# t_lo = max(-sqrt((A-p)(C-r)), -(p+r)/2)

# Evaluating at t_hi: G(sqrt((A-p)(C-r))) = ct2*(A-p)(C-r) + ct1*sqrt((A-p)(C-r)) + ct0
# This involves sqrt, hard to work with algebraically.

# ALTERNATIVE: Use substitution t = u * sqrt((A-p)(C-r)) where -1 <= u <= 1.
# Then t^2 = u^2 * (A-p)(C-r) and the V2 constraint becomes u^2 <= 1.
# G = ct2 * u^2 * (A-p)(C-r) + ct1 * u * sqrt((A-p)(C-r)) + ct0

# Still has sqrt. Let's try parametric approach instead.

# APPROACH: G is a quadratic in X. Show discriminant is nonneg and roots contain the feasible X range.
# G = -ABX^2 + (B-C)pX + AC
# Discriminant: D_G = (B-C)^2*p^2 + 4*A^2*B*C
# Roots: X = [(B-C)p ± sqrt(D_G)] / (2AB)
# Since AB > 0, the parabola opens downward.
# G >= 0 for X in [X_-, X_+].
# X_- = [(B-C)p - sqrt(D_G)] / (2AB)
# X_+ = [(B-C)p + sqrt(D_G)] / (2AB)

# We need: 0 <= X <= X_+ (and X >= X_-, but X_- might be negative).
# So the question reduces to: is the maximum feasible X <= X_+?

# From V1 + AM-GM: X <= A + C (already proved in rvw_X_le_sum_sq)
# We need: A + C <= X_+, i.e., (B-C)p + sqrt(D_G) >= 2AB(A+C)

# Or more generally: show that for any feasible X, G(X) >= 0.

# Let me try yet another approach: directly show that the discriminant-based bound works.

print("\n" + "="*60)
print("Approach 4: Show G >= 0 by direct polynomial manipulation")
print("="*60)

# We want: A*C + (1-A-C)*p*X - A*(1-A)*X^2 >= 0
# Multiply by 4: 4AC + 4(1-A-C)pX - 4A(1-A)X^2 >= 0
# Complete the square in X:
# 4A(1-A)[... ] where ... = -(X^2 - (1-A-C)p/(A(1-A)) X) - AC/(A(1-A))
# Hmm, let's just complete the square.

# -4A(1-A) * [X - (1-A-C)p/(2A(1-A))]^2 + (1-A-C)^2 p^2 / (A(1-A)) + 4AC
# Wait let me redo this.
# f(X) = -4A(1-A)X^2 + 4(1-A-C)pX + 4AC
# = -4A(1-A)[X^2 - (1-A-C)p/(A(1-A)) X] + 4AC
# = -4A(1-A)[X - (1-A-C)p/(2A(1-A))]^2 + (1-A-C)^2p^2/(A(1-A)) + 4AC

# For f(X) >= 0 we need:
# (1-A-C)^2 p^2/(A(1-A)) + 4AC >= 4A(1-A)[X - (1-A-C)p/(2A(1-A))]^2

# This is equivalent to saying X is within the roots, which is what we want to show.

# The key question: can we show X <= [(B-C)p + sqrt((B-C)^2p^2 + 4A^2BC)] / (2AB)?
# Using the constraints?

# Let me try a totally different approach: weighted combination of V1 and V2.

# From V1: (X-p-r)^2/4 <= (A+p)(C+r)
# From V2: (X-p-r)^2/4 <= (A-p)(C-r)

# Take (A-p)*V1 + (A+p)*V2:
# (A-p)*[(A+p)(C+r) - q^2] + (A+p)*[(A-p)(C-r) - q^2] >= 0
# (A-p)(A+p)(C+r) + (A+p)(A-p)(C-r) - [(A-p)+(A+p)]q^2 >= 0
# (A^2-p^2)[(C+r)+(C-r)] - 2A*q^2 >= 0
# (A^2-p^2)*2C - 2A*q^2 >= 0
# A*q^2 <= C*(A^2-p^2)

weighted_ineq = sp.Symbol('weighted')  # A*q^2 <= C*(A^2 - p^2) ... q = t here

# Similarly, take (C-r)*V1 + (C+r)*V2:
# (C-r)(A+p)(C+r) + (C+r)(A-p)(C-r) - [(C-r)+(C+r)]*q^2 >= 0
# (C^2-r^2)[(A+p)+(A-p)] - 2C*q^2 >= 0
# (C^2-r^2)*2A - 2C*q^2 >= 0
# C*q^2 <= A*(C^2 - r^2)

# So we have:
# (I) A*t^2 <= C*(A^2 - p^2)
# (II) C*t^2 <= A*(C^2 - r^2)

# And: X = p + r + 2t, G = AC + (1-A-C)pX - A(1-A)X^2

# From (I): t^2 <= C(A^2-p^2)/A = C*A - C*p^2/A
# From V2: t^2 <= (A-p)(C-r) = AC - Ar - Cp + pr

# Let's try: substitute t in terms of the constraints and show G >= 0.

# G = AC + (1-A-C)*p*(p+r+2t) - A(1-A)*(p+r+2t)^2
# Let S = p+r, so X = S+2t
# G = AC + (1-A-C)*p*(S+2t) - A(1-A)*(S+2t)^2
# = AC + (1-A-C)*p*S + 2(1-A-C)*p*t - A(1-A)*S^2 - 4A(1-A)*S*t - 4A(1-A)*t^2

# Using constraint (I): t^2 <= C(A^2-p^2)/A
# G >= AC + (1-A-C)*p*S + 2(1-A-C)*p*t - A(1-A)*S^2 - 4A(1-A)*S*t - 4(1-A)*C*(A^2-p^2)
#    (replacing 4A(1-A)t^2 by 4(1-A)C(A^2-p^2), making G smaller since t^2 <= ...)
#    Wait, -4A(1-A)*t^2 >= -4A(1-A) * C(A^2-p^2)/A = -4(1-A)C(A^2-p^2)

G_lower = expand(A*C + (1-A-C)*p*(p+r) + 2*(1-A-C)*p*t
                  - A*(1-A)*(p+r)**2 - 4*A*(1-A)*(p+r)*t
                  - 4*(1-A)*C*(A**2-p**2))

print("G_lower (after using weighted ineq A*t^2 <= C(A^2-p^2)):")
print(f"= {expand(G_lower)}")
print()

# This still has t in it. We need to handle the linear-in-t part.
# G_lower = f(A,C,p,r) + [2(1-A-C)p - 4A(1-A)(p+r)] * t
# For this to be >= 0 for the relevant t values, we need the linear coefficient
# and the constant to work out.

linear_coeff_t = 2*(1-A-C)*p - 4*A*(1-A)*(p+r)
constant_part = expand(G_lower - linear_coeff_t * t)

print(f"Linear coeff of t: {expand(linear_coeff_t)}")
print(f"Constant part: {expand(constant_part)}")
print()

# Let's factor the constant part
print(f"Constant part factored: {factor(constant_part)}")
print()

# Hmm, this is getting complicated. Let me try a cleaner approach.
# Use the additive combination: q^2 <= AC + pr (from V1+V2/2).
# And the weighted: A*q^2 <= C(A^2-p^2).

# Express G in terms of these two constraints.

print("\n" + "="*60)
print("Approach 5: Use q^2 <= AC+pr and A*q^2 <= C(A^2-p^2)")
print("="*60)

# With q = t, X = p + r + 2t:
# 4q^2 = (X-p-r)^2
# So q^2 = (X-p-r)^2/4

# From q^2 <= AC + pr:
# (X-p-r)^2 <= 4(AC + pr)
# X^2 - 2X(p+r) + (p+r)^2 <= 4AC + 4pr
# X^2 - 2X(p+r) + p^2 + 2pr + r^2 <= 4AC + 4pr
# X^2 - 2X(p+r) + p^2 - 2pr + r^2 <= 4AC
# X^2 - 2X(p+r) + (p-r)^2 <= 4AC

# From A*q^2 <= C(A^2-p^2):
# A(X-p-r)^2/4 <= C(A^2-p^2)
# A(X-p-r)^2 <= 4C(A^2-p^2) = 4C(A-p)(A+p)

# Let me try to prove G >= 0 using these two constraints directly.
# G = AC + (B-C)pX - ABX^2 where B = 1-A

# Key idea from the status doc: at V1∩V2 intersection (r = -pC/A),
# the minimum of G is 0.

# Let's try parametric proof. Set r = -pC/A + epsilon and show G >= 0.
# Actually, let's try the approach of optimizing G over the feasible set.

# Actually, let me try a very different approach: multiply G by A (to clear denominators from
# the weighted constraint), and express A*G as a nonneg combination.

AG = expand(A * G_expanded.subs([(t, sp.Symbol('t'))]))  # A*G in terms of A,C,p,r,t
AG = expand(A * (A*C + (1-A-C)*p*(p+r+2*t) - A*(1-A)*(p+r+2*t)**2))
print(f"A*G = {AG}")
print()

# A*G is degree 5 in the variables. Hmm, this is getting higher degree.

# Let me try the cleanest possible formulation.
# Directly work with the original variables a, c, p, q, r.

print("\n" + "="*60)
print("Approach 6: Work with original a,c,p,q,r variables (no substitution)")
print("="*60)

a, c, q = symbols('a c q', real=True)

# Constraints:
# V1: q^2 <= (a^2+p)(c^2+r)
# V2: q^2 <= (a^2-p)(c^2-r)
# |p| <= a^2, |r| <= c^2 (WLOG p >= 0, r can be any sign with |r| <= c^2)
# a^2 + b^2 = 1, c <= b (so c^2 <= 1-a^2)
# X = p + 2q + r

# Goal: a^2*(1-a^2)*X^2 <= (1-a^2-c^2)*|p|*|X| + a^2*c^2
# WLOG p >= 0 and X >= 0:
# a^2*(1-a^2)*(p+2q+r)^2 <= (1-a^2-c^2)*p*(p+2q+r) + a^2*c^2

# Equivalently (clearing to G >= 0 form):
# G = a^2*c^2 + (1-a^2-c^2)*p*(p+2q+r) - a^2*(1-a^2)*(p+2q+r)^2 >= 0

# Let A = a^2, C = c^2, B = 1-A, X = p+2q+r
# G = AC + (B-C)pX - ABX^2

# I think the key insight is to use CAUCHY-SCHWARZ more cleverly.

# From the Cauchy-Schwarz structure:
# Let u = p, w = 2q, v = r. X = u + w + v.
# V1: (w/2)^2 <= (A+u)(C+v)
# V2: (w/2)^2 <= (A-u)(C-v)

# Now, G = AC + (B-C)*u*(u+w+v) - AB*(u+w+v)^2

# Try: use V1 and V2 to express w^2, then substitute.
# 4q^2 = w^2. V1: w^2 <= 4(A+u)(C+v). V2: w^2 <= 4(A-u)(C-v).
# Adding: w^2 <= 2(A+u)(C+v) + 2(A-u)(C-v) ... no, they're both upper bounds.
# Averaging: w^2 <= min(4(A+u)(C+v), 4(A-u)(C-v))

# Key: use the PRODUCT V1*V2:
# w^4/16 <= (A+u)(C+v)(A-u)(C-v) = (A^2-u^2)(C^2-v^2)
# So: w^2/4 <= sqrt((A^2-u^2)(C^2-v^2)) <= (A^2-u^2+C^2-v^2)/2 (AM-GM)
# i.e., w^2 <= 2(A^2-u^2+C^2-v^2) = 2(A^2+C^2-u^2-v^2)

# This gives: X = u+w+v, w^2 <= 2(A^2+C^2-u^2-v^2)

# Hmm, this is still not directly giving us what we need.

# Let me think about this more carefully.
# The problem has been shown to be infeasible for degree-4 Psatz.
# This means we need degree >= 6 or a DIFFERENT proof structure.

# The CORRECT approach (from the status doc) is:
# 1. G is concave in X (quadratic with negative leading coeff -AB)
# 2. G(0) = AC >= 0
# 3. Need an upper bound X_max on X such that G(X_max) >= 0
# 4. G(A+C) = AC + (B-C)p(A+C) - AB(A+C)^2
#    = AC + (B-C)(A+C)p - AB(A+C)^2
#    This is LINEAR in p (concave also, since there's no p^2 term).
#    At p=0: G(A+C) = AC - AB(A+C)^2. Is this >= 0?
#    AC >= AB(A+C)^2 iff C >= B(A+C)^2 iff C >= (1-A)(A+C)^2
#    For A=0.5, C=0.1: 0.1 >= 0.5*0.36 = 0.18. NO! G(A+C) < 0 at p=0.
# So X_max = A+C is TOO LARGE. We need a tighter bound.

# The tighter bound comes from the V2 constraint. When p > 0 and r can be negative,
# V2 gives a tighter bound: (X-p-r)^2/4 <= (A-p)(C-r), so X <= p+r+2*sqrt((A-p)(C-r)).

# For fixed p, we need to optimize over r to get the tightest X bound.
# V2 gives: X <= p + r + 2*sqrt((A-p)(C-r)) =: f(r)
# df/dr = 1 - 1/sqrt((A-p)(C-r)) * (A-p)/2 ... hmm not clean.
# Actually: let's set s = C-r (so s >= 0, and r = C-s, with |r| <= C so -C <= C-s, i.e., s <= 2C).
# X <= p + (C-s) + 2*sqrt((A-p)*s) = p + C - s + 2*sqrt((A-p)*s)
# Maximize over s: d/ds[-s + 2*sqrt((A-p)*s)] = -1 + (A-p)/sqrt((A-p)*s) = -1 + sqrt((A-p)/s)
# = 0 when s = A-p, i.e., s* = A-p.
# Then X <= p + C - (A-p) + 2*sqrt((A-p)^2) = p + C - A + p + 2(A-p) = 2p + C - A + 2A - 2p = A + C.
# So the maximum of X over r is indeed A+C. Hmm.

# But G(A+C) can be negative! So how does this work?

# The key is that we CAN'T achieve X = A+C simultaneously with arbitrary p.
# When X = A+C, we need r = C-(A-p), i.e., r = p+C-A.
# But |r| <= C requires p+C-A <= C, i.e., p <= A. OK.
# And r >= -C requires p+C-A >= -C, i.e., p >= A-2C. OK if C >= A/2 or p is large enough.

# At X = A+C with r = p+C-A:
# G(A+C) = AC + (1-A-C)p(A+C) - A(1-A)(A+C)^2
# From V2 at the maximum: s* = A-p, so (A-p)(C-r) = (A-p)^2.
# q^2 <= (A-p)^2, so q = ±(A-p).
# X = p+2q+r = p + 2(A-p) + (p+C-A) = p + 2A - 2p + p + C - A = A + C. Checks out.
# And q = A-p (taking positive root).

# At this point:
# G(A+C) = AC + (1-A-C)p(A+C) - A(1-A)(A+C)^2

# Can we show this is >= 0 for ALL 0 <= p <= A? Let's check:
# G(A+C) is linear in p: = AC - A(1-A)(A+C)^2 + (1-A-C)(A+C)*p
# At p=0: AC - A(1-A)(A+C)^2
# At p=A: AC + (1-A-C)A(A+C) - A(1-A)(A+C)^2
#        = AC + A(A+C)[(1-A-C) - (1-A)(A+C)]
#        = AC + A(A+C)[(1-A-C) - (A+C-A^2-AC)]
#        = AC + A(A+C)[1-A-C - A - C + A^2 + AC]
#        = AC + A(A+C)[1-2A-2C+A^2+AC]
#        = AC + A(A+C)[(1-A)(1-A) - C(2-A)] ... hmm getting messy.

# Let me just numerically check for a case where G(A+C) < 0.
import numpy as np
A_val = 0.5
C_val = 0.1
B_val = 0.5
p_val = 0.0
G_at_AC = A_val*C_val + (B_val-C_val)*p_val*(A_val+C_val) - A_val*B_val*(A_val+C_val)**2
print(f"G(A+C) at A={A_val}, C={C_val}, p={p_val}: {G_at_AC}")
# = 0.05 + 0 - 0.25*0.36 = 0.05 - 0.09 = -0.04. YES, G(A+C) < 0!

# But the inequality IS true because at p=0, the maximum X from V2 is NOT A+C.
# At p=0, V2 gives q^2 <= A*(C-r). For q to be maximized, set r = -C: q^2 <= 2AC.
# X = 0 + 2q + r = 2q + r. With r = -C: X = 2q - C. q = sqrt(2AC).
# X = 2*sqrt(2AC) - C. For A=0.5, C=0.1: X = 2*sqrt(0.1) - 0.1 ≈ 0.532.
# Compare A+C = 0.6. So X_max at p=0 is only 0.532, not 0.6.

# G(0.532) = 0.05 + 0 - 0.25*0.532^2 = 0.05 - 0.0707 ≈ -0.021. Still negative!

# Hmm. Let me check more carefully. With p=0, from V2: q^2 <= A*(C-r).
# X = 2q + r. Optimize X over r: X <= 2*sqrt(A(C-r)) + r.
# dX/dr = -A/sqrt(A(C-r)) + 1 = 0 => A(C-r) = A^2 => r = C-A.
# For A=0.5, C=0.1: r = 0.1-0.5 = -0.4. But |r| <= C = 0.1! So r = -0.4 violates |r| <= 0.1.
# So the constraint |r| <= C is binding: r = -C = -0.1.
# Then q^2 <= A*2C = 0.5*0.2 = 0.1. q = sqrt(0.1).
# X = 2*sqrt(0.1) - 0.1 ≈ 0.532.
# G(X) = 0.05 + 0 - 0.25*0.2832 ≈ 0.05 - 0.0708 ≈ -0.021.

# But wait, we also need V1 to hold! V1: q^2 <= (A+p)(C+r) = 0.5*(0.1-0.1) = 0.
# So q = 0! X = 0 + 0 - 0.1 = -0.1. Since X >= 0 is WLOG, X = 0.1 (take |X|).
# Actually, V1 requires q^2 <= (A+0)(C-0.1) = 0.5*0 = 0. So q = 0!

# The issue is that V1 is much more restrictive at r = -C.
# So the actual maximum X at p=0 is much smaller.

# Let me properly compute the max X at p=0.
# V1: q^2 <= A*(C+r)
# V2: q^2 <= A*(C-r)
# (since p=0)
# Both: q^2 <= A*min(C+r, C-r) = A*(C-|r|) (for |r| <= C)
# X = 2q + r. Maximize X = 2*sqrt(A*(C-|r|)) + r for r in [-C, C].
# For r >= 0: X = 2*sqrt(A*(C-r)) + r. dX/dr = -A/sqrt(A(C-r)) + 1 = 0 at C-r = A, r = C-A.
# For A=0.5, C=0.1: C-A = -0.4 < 0, so r = C-A is not in [0,C]. Max at boundary r=0.
# X(0) = 2*sqrt(AC) = 2*sqrt(0.05) ≈ 0.447.
# For r < 0: X = 2*sqrt(A*(C+r)) + r (since |r| = -r, C-|r| = C+r).
# Wait, for r < 0, |r| = -r, so C - |r| = C + r. V1 gives q^2 <= A(C+r).
# V2 gives q^2 <= A(C-r) = A(C+|r|).
# So min = A(C+r) (since C+r < C-r = C+|r| for r < 0).
# X = 2*sqrt(A(C+r)) + r. dX/dr = A/sqrt(A(C+r)) + 1.
# For r < 0, dX/dr = sqrt(A/(C+r)) + 1 > 0. So X increases as r increases from -C to 0.
# Max at r = 0: X = 2*sqrt(AC) ≈ 0.447.

# G(0.447) at p=0: AC - AB*X^2 = 0.05 - 0.25*0.2 = 0.05 - 0.05 = 0! Exactly zero!
# This is the tight case mentioned in the status doc: G = AC(1 - 4AB) = AC*(2A-1)^2.
# Wait, at p=0, r=0: q^2 <= AC, X = 2q, X^2 = 4q^2 <= 4AC.
# G = AC - ABX^2. Using X^2 <= 4AC: G >= AC - 4*A*B*A*C = AC(1-4AB) = AC(2A-1)^2 >= 0.
# So G >= 0 at p=0 follows from X^2 <= 4AC!

# For general p: from q^2 <= AC + pr:
# X = p + 2q + r, so 4q^2 = (X-p-r)^2.
# (X-p-r)^2 <= 4(AC+pr)
# X^2 - 2X(p+r) + (p+r)^2 <= 4AC + 4pr
# X^2 <= 2X(p+r) - (p+r)^2 + 4AC + 4pr
# X^2 <= 2X(p+r) - p^2 - r^2 - 2pr + 4AC + 4pr
# X^2 <= 2X(p+r) - p^2 - r^2 + 2pr + 4AC

# From A*q^2 <= C(A^2-p^2):
# A(X-p-r)^2/4 <= C(A^2-p^2)
# A*X^2 - 2AX(p+r) + A(p+r)^2 <= 4C(A^2-p^2)

# Maybe combine these two constraints with appropriate weights.

# Goal: G = AC + (B-C)pX - ABX^2 >= 0
# <=> ABX^2 - (B-C)pX <= AC
# <=> ABX^2 <= (B-C)pX + AC

# From q^2 <= AC+pr: (X-p-r)^2 <= 4(AC+pr)
# From Aq^2 <= C(A^2-p^2): A(X-p-r)^2 <= 4C(A^2-p^2)

# Take alpha*(first) + beta*(second):
# (alpha + A*beta)(X-p-r)^2 <= 4*alpha*(AC+pr) + 4*beta*C*(A^2-p^2)

# We want to show: ABX^2 - (B-C)pX - AC <= 0
# i.e., ABX^2 <= (B-C)pX + AC

# Key idea: express ABX^2 as a multiple of (X-p-r)^2 plus correction terms.
# ABX^2 = AB[(X-p-r) + (p+r)]^2
# = AB(X-p-r)^2 + 2AB(X-p-r)(p+r) + AB(p+r)^2
# = AB(X-p-r)^2 + 2AB(p+r)X - 2AB(p+r)^2 + AB(p+r)^2
# = AB(X-p-r)^2 + 2AB(p+r)X - AB(p+r)^2

# So: ABX^2 - (B-C)pX = AB(X-p-r)^2 + [2AB(p+r) - (B-C)p]X - AB(p+r)^2
# = AB(X-p-r)^2 + [(2AB-B+C)p + 2ABr]X - AB(p+r)^2
# = AB(X-p-r)^2 + [(2A-1)Bp + Cp + 2ABr]X - AB(p+r)^2

# Hmm. Let me just try the numeric/symbolic verification first.

print("\n" + "="*60)
print("Approach 7: Numeric search for certificate structure")
print("="*60)

# Try random instances to understand the tight manifold, then guess the certificate.

from scipy.optimize import minimize

def eval_G(params):
    """Evaluate G given (A, C, p, r, q) with all constraints checked."""
    A, C, p, r, q = params
    B = 1 - A
    X = p + 2*q + r
    if X < 0:
        X = abs(X)  # WLOG X >= 0
        p, r, q = -p, -r, -q  # reflect
    return A*C + (B-C)*p*X - A*B*X**2

def neg_G(params):
    return -eval_G(params)

def constraints_scipy(params):
    A, C, p, r, q = params
    B = 1 - A
    return [
        A - 0.001,          # A > 0
        B - 0.001,          # B > 0
        C,                  # C >= 0
        B - C,              # C <= B
        A - abs(p),         # |p| <= A
        C - abs(r),         # |r| <= C
        (A+p)*(C+r) - q**2,  # V1
        (A-p)*(C-r) - q**2,  # V2
    ]

# Search for minimum of G
best_min = float('inf')
best_params = None

for _ in range(10000):
    A0 = np.random.uniform(0.01, 0.99)
    C0 = np.random.uniform(0, 1-A0)
    p0 = np.random.uniform(-A0, A0)
    r0 = np.random.uniform(-C0, C0)
    q_max = min(np.sqrt(max(0,(A0+p0)*(C0+r0))), np.sqrt(max(0,(A0-p0)*(C0-r0))))
    q0 = np.random.uniform(-q_max, q_max)

    g = eval_G([A0, C0, p0, r0, q0])
    if g < best_min:
        best_min = g
        best_params = [A0, C0, p0, r0, q0]

print(f"Min G found: {best_min:.10f}")
print(f"At: A={best_params[0]:.6f}, C={best_params[1]:.6f}, p={best_params[2]:.6f}, r={best_params[3]:.6f}, q={best_params[4]:.6f}")

# Now, the key identity approach.
# From the tight cases analysis, the minimum G=0 is achieved when:
# q = (A-p)(C+r)/(2A) at the V1=V2 intersection (i.e., both V1 and V2 are tight).

# At V1=V2: (A+p)(C+r) = (A-p)(C-r) => AC+Ar+pC+pr = AC-Ar-pC+pr
# => 2Ar + 2pC = 0 => r = -pC/A

# With r = -pC/A:
# V1: q^2 = (A+p)(C - pC/A) = (A+p)*C*(A-p)/A = C(A^2-p^2)/A
# q = sqrt(C(A^2-p^2)/A)

# X = p + 2q + r = p + 2q - pC/A = p(1-C/A) + 2q = p(A-C)/A + 2q
# X = p(A-C)/A + 2*sqrt(C(A^2-p^2)/A)

# G at this point should be 0. Let me verify symbolically.
print("\n--- Verifying G=0 at V1=V2 intersection ---")

A_s, C_s, p_s = symbols('A_s C_s p_s', positive=True)
r_s = -p_s*C_s/A_s
q_s_sq = C_s*(A_s**2 - p_s**2)/A_s
# q_s = sqrt(q_s_sq)  # positive root
X_s = p_s + r_s + 2*sp.sqrt(q_s_sq)
X_s_simplified = simplify(X_s)
print(f"X at V1=V2 intersection: {X_s_simplified}")

G_s = A_s*C_s + (1-A_s-C_s)*p_s*X_s - A_s*(1-A_s)*X_s**2
G_s_simplified = simplify(expand(G_s))
print(f"G at V1=V2 intersection: {G_s_simplified}")

# If not zero, try harder
G_s_expanded = expand(G_s.subs(sp.sqrt(q_s_sq), sp.Symbol('Q')))
print(f"G (with Q = sqrt(...)): {G_s_expanded}")

# Substitute Q^2 = C*(A^2-p^2)/A
Q_sym = sp.Symbol('Q', positive=True)
G_Q = A_s*C_s + (1-A_s-C_s)*p_s*(p_s*(A_s-C_s)/A_s + 2*Q_sym) - A_s*(1-A_s)*(p_s*(A_s-C_s)/A_s + 2*Q_sym)**2
G_Q_expanded = expand(G_Q)
print(f"\nG in terms of Q: {G_Q_expanded}")

# Now replace Q^2 -> C(A^2-p^2)/A
G_Q_sub = G_Q_expanded.subs(Q_sym**2, C_s*(A_s**2-p_s**2)/A_s)
G_Q_sub = expand(G_Q_sub)
print(f"After Q^2 -> C(A^2-p^2)/A: {G_Q_sub}")

# Collect by Q
G_Q_collected = collect(G_Q_sub, Q_sym)
print(f"Collected by Q: {G_Q_collected}")

# The coefficient of Q should be zero for G=0 to hold for all Q satisfying Q^2 = ...
Q_coeff = G_Q_sub.coeff(Q_sym, 1)
Q_coeff = expand(Q_coeff)
print(f"\nCoefficient of Q: {Q_coeff}")
Q_const = expand(G_Q_sub - Q_coeff*Q_sym)
print(f"Constant (no Q): {Q_const}")

# Factor Q coefficient
print(f"Q coeff factored: {factor(Q_coeff)}")
print(f"Constant factored: {factor(Q_const)}")

# So G = Q_coeff * Q + Q_const, where Q = sqrt(C(A^2-p^2)/A)
# For this to be 0, we need Q = -Q_const/Q_coeff (if Q_coeff != 0).

# Let's check if Q_const = 0 independently:
print(f"\nQ_const simplified: {simplify(Q_const)}")

print("\n" + "="*60)
print("KEY INSIGHT: The proof should go through CASE ANALYSIS on the sign")
print("of the 'concavity slack'")
print("="*60)

# Since G is concave in X, G(X) >= min(G(0), G(X_max)) for X in [0, X_max].
# G(0) = AC >= 0 trivially.
# The real X_max depends on all constraints (V1, V2, |r| <= C, |p| <= A).

# KEY: Factor G differently.
# G = AC + (B-C)pX - ABX^2
# = AC - X[(AB)X - (B-C)p]
# = AC - X * [ABX - Bp + Cp]
# = AC - X * [B(AX-p) + CpX]  ... hmm
# = AC - ABX^2 + BpX - CpX + Cpp  ... nope

# G = AC + BpX - CpX - ABX^2
# = AC + pX(B-C) - ABX^2
# = A[C - BX^2] + pX(B-C)
# = A[C - (1-A)X^2] + pX(1-A-C)

# For the case p = 0: G = A[C - (1-A)X^2] = A[C - BX^2]
# Need: X^2 <= C/B. But from V2 (p=0): q^2 <= A(C-r).
# With r=0: q^2 <= AC, X = 2q, X^2 = 4q^2 <= 4AC.
# G = AC - B*4AC*A/A = AC - 4ABC = AC(1-4AB) = AC(1 - 4A(1-A)) = AC(2A-1)^2 >= 0.
# Wait, I need X^2 <= 4AC (not 4AC/A). Let me recompute.
# X = 2q, G = AC - ABX^2 = AC - AB*4q^2 <= AC - AB*4*0 = AC. That's an UPPER bound for G.
# We need LOWER bound. G = AC - AB*4q^2. Since q^2 <= AC (from V2 with p=r=0),
# G >= AC - 4*AB*AC = AC(1-4AB) = AC(2A-1)^2 >= 0. Yes!

# For general p != 0, the (B-C)pX term helps (if positive) or hurts.
# The question is whether the V constraints limit X enough.

# APPROACH: Express G as the sum of two terms:
# G = [something involving V2 slack] + [something involving other constraints]

# Let's try:
# G = alpha * V2_constraint + beta * V1_constraint + gamma * p_nonneg * something + ...

# Actually, let me try the following algebraic identity:
# G = AC + (B-C)pX - ABX^2
#   = AC + (B-C)p(p+r+2q) - AB(p+r+2q)^2

# Let u = p+r, S = 2q. Then X = u+S.
# G = AC + (B-C)p(u+S) - AB(u+S)^2
# = AC + (B-C)pu + (B-C)pS - AB*u^2 - 2AB*u*S - AB*S^2
# = [AC + (B-C)pu - AB*u^2] + [(B-C)p - 2AB*u]*S - AB*S^2

# The S^2 term: -AB*S^2 = -AB*4q^2. Using q^2 <= AC+pr:
# -4ABq^2 >= -4AB(AC+pr) = -4A^2BC - 4ABpr

# So: G >= [AC + (B-C)pu - ABu^2 - 4A^2BC - 4ABpr] + [(B-C)p - 2ABu]*S
# = [AC(1-4AB) + (B-C)p(p+r) - AB(p+r)^2 - 4ABpr] + [(B-C)p - 2AB(p+r)]*2q

# This is getting messy. Let me try a clean LP approach with degree 6.

print("\n" + "="*60)
print("Approach 8: Higher-degree Psatz (degree 6)")
print("="*60)

# Actually, let me think about what degree we need.
# The issue is that the proof fundamentally involves sqrt (from q = sqrt(...)).
# We can handle this by introducing q^2 as a proxy.

# Key identity: G can be expressed as:
# G = (something) * (V2 - V2_at_boundary) + (something_else)
# where V2_at_boundary = when V2 is tight.

# OR: use the SCHUR S-LEMMA approach.
# For quadratics in q (with q^2 <= bound), S-lemma says:
# f(q) >= 0 for all |q| <= sqrt(B) iff there exists tau >= 0 such that
# f(q) - tau*(B - q^2) is SOS in q.

# G is quadratic in q (since X = p+2q+r):
# G = AC + (B-C)*p*(p+2q+r) - AB*(p+2q+r)^2
# G = (terms without q) + (linear in q)*q + (quad in q)*q^2
# Actually G involves q linearly AND quadratically (through X = p+2q+r and X^2).

# G = AC + (B-C)p(p+r) + 2(B-C)pq - AB(p+r)^2 - 4AB(p+r)q - 4ABq^2
# quad_q = -4AB
# linear_q = 2(B-C)p - 4AB(p+r)
# const_q = AC + (B-C)p(p+r) - AB(p+r)^2

# S-lemma: G >= 0 for q^2 <= min((A+p)(C+r), (A-p)(C-r)) if there exist tau1, tau2 >= 0:
# G + tau1*(q^2 - (A+p)(C+r)) + tau2*(q^2 - (A-p)(C-r)) is SOS in q
# i.e., G - tau1*V1_slack - tau2*V2_slack is nonneg (as a function of q with NO constraint on q)
# i.e., (-4AB + tau1 + tau2)*q^2 + [2(B-C)p - 4AB(p+r)]*q + [const - tau1*(A+p)(C+r) - tau2*(A-p)(C-r)] >= 0 for ALL q
# For a quadratic aq^2 + bq + c >= 0 for all q: need a >= 0 AND 4ac - b^2 >= 0.

# From the first condition: tau1 + tau2 >= 4AB
# From the second condition (discriminant):
# 4*(-4AB + tau1 + tau2)*[const - tau1*(A+p)(C+r) - tau2*(A-p)(C-r)] >= [2(B-C)p - 4AB(p+r)]^2

# This is a FEASIBILITY problem in tau1, tau2 (which can depend on A,C,p,r).

# Let me set tau1 + tau2 = 4AB (minimum), so tau2 = 4AB - tau1.
# Then the quadratic coefficient is 0, and the S-lemma degenerates.
# We need: the discriminant condition becomes: 0 >= b^2, so b = 0.
# b = 2(B-C)p - 4AB(p+r). This is NOT always 0.

# So we need tau1 + tau2 > 4AB.
# Let tau1 = alpha*4AB, tau2 = beta*4AB with alpha + beta = 1 + epsilon.
# Actually this is getting complicated. Let me just parameterize and solve.

# tau1 and tau2 are functions of A,C,p,r. Try them as polynomials.
# For tau1, tau2 to be nonneg, they need to be SOS (or we can just try specific forms).

# Simplest: tau1 = tau2 = 2AB + delta for some delta >= 0.
# Then tau1+tau2 = 4AB + 2*delta.
# Quad coeff = 2*delta.
# Constant = const - (2AB+delta)*[(A+p)(C+r) + (A-p)(C-r)]
#           = const - (2AB+delta)*2AC (since (A+p)(C+r)+(A-p)(C-r) = 2AC + 2pr + 2AC - 2pr = no wait)
# (A+p)(C+r) + (A-p)(C-r) = AC+Ar+pC+pr + AC-Ar-pC+pr = 2AC+2pr
# So constant = AC + (B-C)p(p+r) - AB(p+r)^2 - (2AB+delta)*(2AC+2pr)
#             = AC + (B-C)p(p+r) - AB(p+r)^2 - 4ABC - 4ABpr - 2*delta*(AC+pr)

# Disc condition: 4*(2delta)*constant >= b^2
# where b = 2(B-C)p - 4AB(p+r)

# This is one equation in delta (which can depend on A,C,p,r).

# Let me just try numeric exploration to find the right tau1, tau2.

def find_slema_certificate(A_val, C_val, p_val, r_val):
    """Find S-lemma certificate numerically for given A,C,p,r."""
    B_val = 1 - A_val

    # Coefficients of the quadratic in q
    coeff_q2 = -4*A_val*B_val
    coeff_q1 = 2*(B_val-C_val)*p_val - 4*A_val*B_val*(p_val+r_val)
    coeff_q0 = A_val*C_val + (B_val-C_val)*p_val*(p_val+r_val) - A_val*B_val*(p_val+r_val)**2

    # S-lemma: G + tau1*(q^2 - V1) + tau2*(q^2 - V2) >= 0 for all q
    # = (coeff_q2+tau1+tau2)*q^2 + coeff_q1*q + (coeff_q0 - tau1*V1_bound - tau2*V2_bound)
    V1_bound = (A_val+p_val)*(C_val+r_val)
    V2_bound = (A_val-p_val)*(C_val-r_val)

    # Need: a = coeff_q2+tau1+tau2 > 0 (or =0 with b=0)
    #        c = coeff_q0 - tau1*V1_bound - tau2*V2_bound
    #        4ac >= b^2 (where b = coeff_q1)

    # With a = coeff_q2 + tau1 + tau2 and b = coeff_q1 (fixed):
    # c = coeff_q0 - tau1*V1_bound - tau2*V2_bound

    # If b = 0, just need a >= 0 and c >= 0.
    # If b != 0, need a > 0 and c >= b^2/(4a).

    # Minimize tau1+tau2 subject to: tau1,tau2 >= 0, a > 0, 4ac >= b^2
    # Try tau1 = tau2 = t:
    # a = -4AB + 2t, c = coeff_q0 - t*(V1+V2)
    # Need a > 0: t > 2AB
    # Need 4ac >= b^2: 4*(-4AB+2t)*(coeff_q0 - t*(V1+V2)) >= b^2

    b_sq = coeff_q1**2
    V_sum = V1_bound + V2_bound

    # Try: tau1 = alpha*AB, tau2 = (4-alpha)*AB for some alpha >= 0, 4-alpha >= 0
    # a = 0. Degenerate, need b = 0.

    # General: try different splits
    best = None
    for tau1_val in np.linspace(0, 10*A_val*B_val, 100):
        for tau2_val in np.linspace(0, 10*A_val*B_val, 100):
            a = coeff_q2 + tau1_val + tau2_val
            c = coeff_q0 - tau1_val*V1_bound - tau2_val*V2_bound
            if a > 1e-12 and c >= 0 and 4*a*c >= b_sq - 1e-12:
                if best is None or tau1_val + tau2_val < best[0]:
                    best = (tau1_val + tau2_val, tau1_val, tau2_val, a, c)

    return best

# Test at a few points
test_points = [
    (0.3, 0.2, 0.1, 0.05),
    (0.5, 0.1, 0.2, 0.05),
    (0.5, 0.3, 0.4, -0.1),
    (0.7, 0.1, 0.3, 0.05),
]

for A_v, C_v, p_v, r_v in test_points:
    result = find_slema_certificate(A_v, C_v, p_v, r_v)
    if result:
        print(f"A={A_v}, C={C_v}, p={p_v}, r={r_v}: tau1={result[1]:.4f}, tau2={result[2]:.4f}, a={result[3]:.4f}, c={result[4]:.4f}")
    else:
        print(f"A={A_v}, C={C_v}, p={p_v}, r={r_v}: No certificate found")

# Now try to find tau1, tau2 as FUNCTIONS of A,C,p,r that work everywhere.
# From the numeric experiments, try to fit tau1 = f1(A,C,p,r), tau2 = f2(A,C,p,r).

print("\n" + "="*60)
print("S-Lemma approach: find tau1(A,C,p,r), tau2(A,C,p,r)")
print("="*60)

# The S-lemma conditions (for all q):
# (I) tau1 + tau2 >= 4*A*B
# (II) 4*(tau1+tau2-4AB) * (coeff_q0 - tau1*V1_bound - tau2*V2_bound) >= coeff_q1^2
# (III) tau1 >= 0, tau2 >= 0
# (IV) coeff_q0 - tau1*V1_bound - tau2*V2_bound >= 0  (needed for (II) when tau1+tau2 > 4AB)

# coeff_q0 = AC + (B-C)p(p+r) - AB(p+r)^2
# V1_bound = (A+p)(C+r)
# V2_bound = (A-p)(C-r)
# coeff_q1 = 2(B-C)p - 4AB(p+r)

# Let tau1 = 2AB + s*(A+p), tau2 = 2AB + s*(A-p) for some s >= 0.
# Then tau1+tau2 = 4AB + 2sA. So (I) is satisfied if s >= 0.
# tau1 >= 0: always (since A,B,p,s >= 0 and p <= A).
# tau2 >= 0: 2AB + s(A-p) >= 0, yes since A-p >= 0.

# c = coeff_q0 - [2AB + s(A+p)]*(A+p)(C+r) - [2AB + s(A-p)]*(A-p)(C-r)
# = coeff_q0 - 2AB[(A+p)(C+r) + (A-p)(C-r)] - s[(A+p)^2(C+r) + (A-p)^2(C-r)]
# = coeff_q0 - 2AB[2AC+2pr] - s[(A+p)^2(C+r) + (A-p)^2(C-r)]
# = AC + (B-C)p(p+r) - AB(p+r)^2 - 4ABC - 4ABpr - s[(A+p)^2(C+r)+(A-p)^2(C-r)]

# Let me compute this symbolically
tau1_expr = 2*A*(1-A) + sp.Symbol('s')*(A+p)
tau2_expr = 2*A*(1-A) + sp.Symbol('s')*(A-p)
s_sym = sp.Symbol('s', nonneg=True)

print("Trying tau1 = 2AB + s(A+p), tau2 = 2AB + s(A-p)")

# Condition (II): 4*(2sA)*c >= b^2
# where c = coeff_q0 - tau1*(A+p)(C+r) - tau2*(A-p)(C-r)
# and b = 2(B-C)p - 4AB(p+r)

# For (II) to hold as an identity in A,C,p,r, we need s to depend on A,C,p,r.
# Try s = gamma * C for some constant gamma.

# Actually, let me just write the LP with parametric tau1, tau2.
# Express tau1, tau2 as polynomials in A,C,p,r of degree k, and use SOS/LP to find coefficients.

# But this is getting very complex. Let me try a MUCH simpler approach.

print("\n" + "="*60)
print("Approach 9: Direct algebraic identity")
print("="*60)

# The key insight from the status doc: use the REFLECTION structure.
# Sigma^2 = I means <Sigma v, v> = cos(2*theta) * ||v||^2 for some angle theta.
# But we're trying to avoid trig.

# Instead, let's use the factored form.
# Define: P = (I+Sigma)/2 and M = (I-Sigma)/2. These are projections (P+M=I, PM=0).
# u = Pu + Mu, w = Pw + Mw.
# p = <Sigma u, u> = ||Pu||^2 - ||Mu||^2 (since Sigma = P - M)
# So p = a_+^2 - a_-^2 where a_+ = ||Pu||, a_- = ||Mu||, a_+^2 + a_-^2 = a^2 = A.
# Similarly r = c_+^2 - c_-^2 with c_+^2 + c_-^2 = c^2 = C.
# And q = <Sigma u, w> = <Pu, Pw> - <Mu, Mw>.

# Cauchy-Schwarz: |<Pu, Pw>| <= ||Pu|| * ||Pw|| = a_+ * c_+
# |<Mu, Mw>| <= a_- * c_-
# So q = alpha - beta where |alpha| <= a_+ c_+ and |beta| <= a_- c_-
# where alpha = <Pu, Pw>, beta = <Mu, Mw>.

# X = p + 2q + r = (a_+^2 - a_-^2) + 2(alpha - beta) + (c_+^2 - c_-^2)
# = (a_+ + c_+)^2 + 2alpha - (a_- + c_-)^2 + 2beta - 2a_+c_+ + 2a_-c_-
# Hmm, that's not clean. Let me try:
# X = (a_+^2 + c_+^2 + 2alpha) - (a_-^2 + c_-^2 + 2beta)
# = ||Pu + Pw||^2 - ||Mu + Mw||^2   (using <u,w>=0 implies <Pu,Mw>+<Mu,Pw>=0)
# Wait, that's not right because ||Pu+Pw||^2 = a_+^2 + c_+^2 + 2<Pu,Pw> + 2<Pu,Pw'> where Pw' is... no.
# Actually ||Pu+Pw||^2 = ||Pu||^2 + ||Pw||^2 + 2<Pu,Pw> = a_+^2 + c_+^2 + 2alpha.
# So X = ||Pu+Pw||^2 - ||Mu+Mw||^2.

# Now, <Sigma(u+w), u+w> = ||P(u+w)||^2 - ||M(u+w)||^2.
# P(u+w) = Pu + Pw, M(u+w) = Mu + Mw.
# So X = ||Pu+Pw||^2 - ||Mu+Mw||^2.

# Let x = ||Pu+Pw||, y = ||Mu+Mw||. Then X = x^2 - y^2, and
# ||u+w||^2 = x^2 + y^2 (since P,M are complementary projections).
# ||u+w||^2 = ||u||^2 + ||w||^2 = A + C (using <u,w> = 0 and ||u||^2 = A, ||w||^2 = C).
# So x^2 + y^2 = A + C, X = x^2 - y^2.
# Therefore x^2 = (A+C+X)/2, y^2 = (A+C-X)/2.

# Also: a = ||u||, so ||Pu||^2 + ||Mu||^2 = A.
# c = ||w||, so ||Pw||^2 + ||Mw||^2 = C.
# p = ||Pu||^2 - ||Mu||^2 => ||Pu||^2 = (A+p)/2, ||Mu||^2 = (A-p)/2.
# r = ||Pw||^2 - ||Mw||^2 => ||Pw||^2 = (C+r)/2, ||Mw||^2 = (C-r)/2.

# x^2 = ||Pu+Pw||^2 = ||Pu||^2 + ||Pw||^2 + 2<Pu,Pw>
# = (A+p)/2 + (C+r)/2 + 2*alpha
# = (A+p+C+r)/2 + 2*alpha.
# Also x^2 = (A+C+X)/2.
# So: (A+C+X)/2 = (A+p+C+r)/2 + 2*alpha
# => X = p + r + 4*alpha. But X = p + 2q + r and q = alpha - beta.
# So X - p - r = 4*alpha - 2*beta... hmm, that gives 2q = 2alpha - 2beta = X-p-r,
# but also 4alpha = X + ... This is inconsistent unless I messed up.

# Let me redo: 2*alpha = 2*<Pu,Pw>, and in ||Pu+Pw||^2 the cross term is 2*<Pu,Pw> = 2*alpha.
# x^2 = (A+p)/2 + (C+r)/2 + 2*alpha. And x^2 = (A+C+X)/2.
# So (A+C+X)/2 = (A+p+C+r)/2 + 2*alpha => X - p - r = 4*alpha.
# Similarly y^2 = (A-p)/2 + (C-r)/2 + 2*beta. And y^2 = (A+C-X)/2.
# So (A+C-X)/2 = (A-p+C-r)/2 + 2*beta => -X+p+r = 4*beta => beta = (p+r-X)/4.
# Also q = alpha - beta = (X-p-r)/4 - (p+r-X)/4 = (X-p-r)/2. Consistent!

# So alpha = (X-p-r)/4, beta = (p+r-X)/4.
# V1: alpha^2 <= (A+p)(C+r)/4 (from |<Pu,Pw>| <= ||Pu||||Pw||)
# => (X-p-r)^2/16 <= (A+p)(C+r)/4 => (X-p-r)^2 <= 4(A+p)(C+r). OK, that's V1.

# Now: |X| = |x^2 - y^2|. With WLOG X >= 0: X = x^2 - y^2, x^2 + y^2 = A+C.
# G = AC + (B-C)pX - ABX^2.

# x^2 = (A+C+X)/2, y^2 = (A+C-X)/2.
# Also: ||Pu|| = sqrt((A+p)/2), ||Mu|| = sqrt((A-p)/2).
# By Cauchy-Schwarz: alpha <= sqrt((A+p)/2) * sqrt((C+r)/2)
# alpha = (X-p-r)/4, so (X-p-r)/4 <= sqrt((A+p)(C+r))/2 => (X-p-r) <= 2*sqrt((A+p)(C+r)).

# Now I want to use the structure x^2 + y^2 = A+C, X = x^2 - y^2.
# Also: x^2 >= (sqrt((A+p)/2) - sqrt((C+r)/2))^2 = ((A+p)+(C+r)-2sqrt((A+p)(C+r)))/2
# ... getting complicated. Let me try with the x,y parametrization.

# In terms of x, y, with x^2+y^2 = A+C, X = x^2-y^2:
# G = AC + (B-C)p(x^2-y^2) - AB(x^2-y^2)^2
# = AC + (B-C)pX - AB*X^2

# Also: p = ||Pu||^2 - ||Mu||^2.
# ||Pu|| <= ||P(u+w)|| + ||Pw|| = x + sqrt((C+r)/2)  ... hmm, too many unknowns.

# ALTERNATIVE: use the hat-block parametrization.
# p = <Sigma u, u> and |p| <= lambda_1 * ||u||^2 = lambda_1 * A.
# So p = lambda_1 * A * cos_theta for some |cos_theta| <= 1.
# But this is essentially what we already have.

# I think the cleanest approach is to go back to the LP/SOS approach but at higher degree.
# Since degree 4 is infeasible, try degree 6 or 8.

# But the key issue was: the STATUS DOC says scalar multiplier nlinarith (degree 4) is infeasible.
# The SOS approach with polynomial multipliers at degree 4 was also infeasible (our first script).
# We need polynomial multipliers of higher degree.

# The degree-4 Psatz had monomials up to degree 4 total.
# G has degree 4. The constraints have degree 1 or 2.
# For m^2 * h_i, if deg(h_i) = 2 and deg(m) = 1, we get degree 4. Done.
# For deg(h_i) = 1 and deg(m) = 1, we get degree 3. Product of two of these gives degree 6 > 4.

# What if we allow the TARGET G to be multiplied by a nonneg polynomial too?
# i.e., show sigma_0 * G = sigma_1 * h_1 + ... + SOS
# where sigma_0 > 0 on the feasible set.

# Or: show G = (some expression) that is manifestly nonneg using TWO LAYERS:
# Layer 1: reduce to simpler expression using V1,V2
# Layer 2: show simpler expression >= 0 using other constraints.

# Let's try the TWO-STEP proof:
# Step 1: Use V2 to replace (X-p-r)^2 by 4*(A-p)(C-r).
#   G = -4AB*q^2 + 2(B-C)p*q + [AC + (B-C)p(p+r) - AB(p+r)^2]
# Step 2: Use Aq^2 <= C(A^2-p^2) to bound the q^2 term.

# From step 1: G >= -4AB*[(A-p)(C-r)] + 2(B-C)p*q + [AC + (B-C)p(p+r) - AB(p+r)^2]
# Wait, that's WRONG. V2 says q^2 <= (A-p)(C-r), so -4AB*q^2 >= -4AB*(A-p)(C-r).
# Correctly: the q^2 term in G is -4AB*q^2, and since -4AB < 0 and q^2 <= V2_bound:
# -4AB*q^2 >= -4AB * (A-p)(C-r)

# But we also have a linear-in-q term: 2(B-C)p*q, which can be positive or negative.
# So: G = [-4AB*q^2 + 2(B-C)p*q] + const
# = -4AB*[q^2 - (B-C)p/(2AB)*q] + const
# = -4AB*[q - (B-C)p/(4AB)]^2 + (B-C)^2*p^2/(4AB) + const

# This is a downward-opening parabola in q, maximized at q* = (B-C)p/(4AB).
# The minimum of G over q is at the boundary of the feasible set for q.
# If (B-C)p > 0 (i.e., C < B and p > 0), G is maximized at positive q, so min is at q = -q_max or q = q_max
# depending on the shape.

# Since the parabola opens downward, the min on [q_min, q_max] is at whichever endpoint is farther from q*.

# For our WLOG (X >= 0), we need q >= -(p+r)/2. And q^2 <= V2_bound.
# So q ranges in [max(-(p+r)/2, -sqrt(V2)), sqrt(V2)] (approximately).

# The minimum of a downward parabola on [a,b] is min(f(a), f(b)).
# We need both f(q_min) >= 0 and f(q_max) >= 0.

# f(q_max) where q_max^2 = (A-p)(C-r):
# G = -4AB*(A-p)(C-r) + 2(B-C)p*sqrt((A-p)(C-r)) + const
# This involves sqrt again.

# f(q=0):
# G = const = AC + (B-C)p(p+r) - AB(p+r)^2

# Let me just verify: can we prove G(q=0) >= 0?
# G(q=0) = AC + (B-C)p(p+r) - AB(p+r)^2
# = AC + (B-C)(p^2+pr) - AB(p+r)^2
# Need: AC >= AB(p+r)^2 - (B-C)(p^2+pr)
# At p=A, r=C: AC >= AB(A+C)^2 - (B-C)(A^2+AC) = AB(A+C)^2 - (B-C)A(A+C)
# = A(A+C)[B(A+C) - (B-C)] = A(A+C)[BA+BC-B+C] = A(A+C)[B(A+C-1)+C]
# Since B = 1-A: = A(A+C)[(1-A)(A+C-1)+C] = A(A+C)[A+C-1-A^2-AC+A+C]
# = A(A+C)[2A+2C-1-A^2-AC]
# For A=0.5, C=0.4: A(A+C) = 0.5*0.9 = 0.45, [...] = 1+0.8-1-0.25-0.2 = 0.35
# AC = 0.2, G(q=0) >= 0? AC = 0.2 >= 0.45*0.35 = 0.1575? Yes but I'm not proving it right.

# I think we need to just CODE UP the approach more carefully with sympy.
# Let me try the clean two-step approach.

print("\nDirect substitution check:")
print("Step 1: G as quadratic in q")
B_sym = 1 - A
q_sym = symbols('q_sym', real=True)
G_q = A*C + (B_sym-C)*p*(p+2*q_sym+r) - A*B_sym*(p+2*q_sym+r)**2
G_q_expanded = expand(G_q)
G_q_collected = collect(G_q_expanded, q_sym)
print(f"G = {G_q_collected}")

a2 = G_q_expanded.coeff(q_sym, 2)
a1 = G_q_expanded.coeff(q_sym, 1)
a0 = expand(G_q_expanded - a2*q_sym**2 - a1*q_sym)
print(f"  a2 (coeff q^2) = {expand(a2)}")
print(f"  a1 (coeff q)   = {factor(expand(a1))}")
print(f"  a0 (constant)  = {factor(expand(a0))}")

# G = a2*q^2 + a1*q + a0
# a2 = -4A(1-A) < 0
# G is concave in q. For G >= 0 at the boundary points of q's domain,
# we need to evaluate G at q = sqrt(V2_bound) and q satisfying other constraints.

# The MINIMUM of G (concave in q) on a convex domain is at a vertex.
# The vertices of the q-domain are where V1 or V2 are tight.

# When V2 is tight: q^2 = (A-p)(C-r), q = ±sqrt((A-p)(C-r))
# When V1 is tight: q^2 = (A+p)(C+r), q = ±sqrt((A+p)(C+r))
# But also q is constrained by both V1 AND V2 simultaneously.

# At a vertex where BOTH V1 and V2 are tight:
# (A+p)(C+r) = (A-p)(C-r) => Ar + pC = -Ar - pC => 2Ar + 2pC = 0 => r = -pC/A.
# Then q^2 = (A+p)(C-pC/A) = (A+p)*C(A-p)/A = C(A^2-p^2)/A.
# X = p + 2q + r = p + 2q - pC/A = p(A-C)/A + 2q.

# G at this vertex (V1=V2 tight) should be 0 (as we checked numerically).
# This is the KEY IDENTITY.

# So the proof structure should be:
# 1. At V1=V2 intersection: G = 0 (identity)
# 2. Moving away from V1=V2 intersection: G increases (because we're inside the feasible set,
#    i.e., we have MORE slack in V1 and V2).

# Let's verify step 1 algebraically.
print("\n--- Checking G = 0 at V1=V2 intersection ---")
r_star = -p*C/A
q_sq_star = C*(A**2 - p**2)/A

# Two cases: q_star = +sqrt(...) and q_star = -sqrt(...)
# For X >= 0 WLOG, we want p + 2q + r >= 0.
# p + r_star = p - pC/A = p(A-C)/A.
# X = p(A-C)/A + 2q. For X >= 0 with q > 0, this is fine.

# G at V1=V2 with q = Q (symbolic):
Q = symbols('Q', positive=True)
G_star = A*C + (1-A-C)*p*(p*(A-C)/A + 2*Q) - A*(1-A)*(p*(A-C)/A + 2*Q)**2
G_star_expanded = expand(G_star)
# Replace Q^2 by C(A^2-p^2)/A
G_star_sub = G_star_expanded.subs(Q**2, C*(A**2-p**2)/A)
G_star_sub = expand(G_star_sub)
print(f"G at V1=V2 (after Q^2 sub): {G_star_sub}")
G_star_collected = collect(G_star_sub, Q)
print(f"Collected by Q: {G_star_collected}")

Q_coeff_final = G_star_sub.coeff(Q, 1)
Q_const_final = expand(G_star_sub - Q_coeff_final*Q)
print(f"Q coefficient: {expand(Q_coeff_final)}")
print(f"Q=0 part: {expand(Q_const_final)}")
print(f"Q coefficient factored: {factor(Q_coeff_final)}")
print(f"Q=0 part factored: {factor(Q_const_final)}")

# Check if Q_const = 0 and Q_coeff = 0 independently
# If not, check if Q_coeff * Q + Q_const = 0 given Q^2 = C(A^2-p^2)/A.
# i.e., Q = sqrt(C(A^2-p^2)/A), so Q_coeff * sqrt(C(A^2-p^2)/A) + Q_const = 0.
# This means Q_const^2 = Q_coeff^2 * C(A^2-p^2)/A (with appropriate sign).

Q_c_sq = expand(Q_coeff_final**2 * C*(A**2-p**2)/A)
Q_0_sq = expand(Q_const_final**2)
print(f"\nQ_coeff^2 * C(A^2-p^2)/A = {Q_c_sq}")
print(f"Q_const^2 = {Q_0_sq}")
diff_sq = expand(Q_c_sq - Q_0_sq)
print(f"Difference: {factor(diff_sq)}")

# If diff_sq = 0 and signs match, then G = 0 at V1=V2 intersection.
