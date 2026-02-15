#!/usr/bin/env python3
# DEAD END: This script attempts boundary evaluation + Psatz for sub-problems of
# rvw_quadratic_ineq. The diagonal Positivstellensatz is structurally infeasible
# — see scripts/RVW_QUADRATIC_PROOF_STATUS.md.
"""
Fast, focused script for RVW quadratic inequality certificate.

Key facts established:
1. D - W^2 = 4AB * G (tautology, not useful)
2. G(q=0) = a0 = AC + (B-C)p(p+r) - AB(p+r)^2 appears to be >= 0 on feasible set
3. G is concave in q, so min is at boundary q = ±sqrt(min(V1,V2))
4. At the boundary, G still appears >= 0

Strategy:
Step 1: Prove a0 >= 0 via Psatz (polynomial in 4 vars, degree 3)
Step 2: Prove G at boundary >= 0 (harder, involves sqrt)
"""
import sys
import numpy as np
import sympy as sp
from scipy.optimize import linprog
from fractions import Fraction
from collections import defaultdict

print("=== Step 1: Prove a0 >= 0 ===", flush=True)

A, C, p, r = sp.symbols('A C p r', real=True)

# a0 = AC + (1-A-C)p(p+r) - A(1-A)(p+r)^2
a0 = sp.expand(A*C + (1-A-C)*p*(p+r) - A*(1-A)*(p+r)**2)

# Quick numerical check
np.random.seed(42)
min_a0 = min(
    float(a0.subs([(A, Av:=np.random.uniform(0.01,0.99)), (C, Cv:=np.random.uniform(0,1-Av)),
                    (p, pv:=np.random.uniform(0,Av)), (r, np.random.uniform(-Cv,Cv))]))
    for _ in range(100000)
)
print(f"min(a0) over 100K samples: {min_a0:.10f}", flush=True)

# a0 has degree 3 (in p,r up to degree 2, in A up to 2, but p*(p+r) is degree 2 in p)
a0_poly_sp = sp.Poly(a0, A, C, p, r)
a0_deg = a0_poly_sp.total_degree()
a0_dict = dict(a0_poly_sp.as_dict())
print(f"a0 degree: {a0_deg}", flush=True)

# Constraints: A >= 0, 1-A >= 0, C >= 0, 1-A-C >= 0, p >= 0, A-p >= 0, C-r >= 0, C+r >= 0
h_list = [A, 1-A, C, 1-A-C, p, A-p, C-r, C+r]
h_names = ['A', '1-A', 'C', '1-A-C', 'p', 'A-p', 'C-r', 'C+r']
h_degs = [sp.Poly(h, A, C, p, r).total_degree() for h in h_list]

def gen_mons(n, d):
    if n == 0: return [()]
    result = []
    for i in range(d+1):
        for rest in gen_mons(n-1, d-i):
            result.append((i,) + rest)
    return result

# Build Psatz basis: m^2, m^2*h_i, m^2*h_i*h_j, m^2*h_i*h_j*h_k (for low-degree constraints)
columns = []

# SOS: m^2 with deg <= a0_deg
for m in gen_mons(4, a0_deg//2):
    m_expr = A**m[0] * C**m[1] * p**m[2] * r**m[3]
    term = sp.expand(m_expr**2)
    if sp.Poly(term, A, C, p, r).total_degree() <= a0_deg:
        columns.append(('SOS', term))

# m^2*h_i
for ci, (h, hd) in enumerate(zip(h_list, h_degs)):
    md = (a0_deg - hd) // 2
    if md < 0: continue
    for m in gen_mons(4, md):
        m_expr = A**m[0] * C**m[1] * p**m[2] * r**m[3]
        term = sp.expand(m_expr**2 * h)
        if sp.Poly(term, A, C, p, r).total_degree() <= a0_deg:
            columns.append((h_names[ci], term))

# m^2*h_i*h_j
for ci in range(len(h_list)):
    for cj in range(ci, len(h_list)):
        pd = h_degs[ci] + h_degs[cj]
        if pd > a0_deg: continue
        md = (a0_deg - pd) // 2
        if md < 0: md = 0
        for m in gen_mons(4, md):
            m_expr = A**m[0] * C**m[1] * p**m[2] * r**m[3]
            term = sp.expand(m_expr**2 * h_list[ci] * h_list[cj])
            if sp.Poly(term, A, C, p, r).total_degree() <= a0_deg:
                columns.append((f'{h_names[ci]}*{h_names[cj]}', term))

# Triple products of degree-1 constraints
for ci in range(len(h_list)):
    if h_degs[ci] != 1: continue
    for cj in range(ci, len(h_list)):
        if h_degs[cj] != 1: continue
        for ck in range(cj, len(h_list)):
            if h_degs[ck] != 1: continue
            if h_degs[ci]+h_degs[cj]+h_degs[ck] > a0_deg: continue
            term = sp.expand(h_list[ci]*h_list[cj]*h_list[ck])
            if sp.Poly(term, A, C, p, r).total_degree() <= a0_deg:
                columns.append((f'{h_names[ci]}*{h_names[cj]}*{h_names[ck]}', term))

print(f"Columns: {len(columns)}", flush=True)

# Collect all monomials
all_mons = set()
for m in a0_dict:
    all_mons.add(m)
for name, expr in columns:
    for m in sp.Poly(expr, A, C, p, r).as_dict():
        all_mons.add(m)

all_mons = sorted(all_mons)
mon_idx = {m: i for i, m in enumerate(all_mons)}
n_mons = len(all_mons)
n_cols = len(columns)
print(f"Monomials: {n_mons}, rank needed: {n_mons}", flush=True)

# Build LP
A_mat = np.zeros((n_mons, n_cols))
g_vec = np.zeros(n_mons)

for m, c in a0_dict.items():
    g_vec[mon_idx[m]] = float(c)

for col_i, (name, expr) in enumerate(columns):
    for m, c in sp.Poly(expr, A, C, p, r).as_dict().items():
        A_mat[mon_idx[m], col_i] += float(c)

rank = np.linalg.matrix_rank(A_mat)
print(f"Matrix: {n_mons}x{n_cols}, rank: {rank}", flush=True)

result = linprog(np.zeros(n_cols), A_eq=A_mat, b_eq=g_vec,
                bounds=[(0, None)] * n_cols, method='highs')

if result.success:
    print("\n*** SUCCESS: a0 >= 0 has Psatz certificate! ***", flush=True)
    sigma = result.x
    active = [(i, sigma[i]) for i in range(n_cols) if sigma[i] > 1e-10]
    print(f"Active terms: {len(active)}")
    for i, val in sorted(active, key=lambda x: -x[1])[:20]:
        print(f"  {val:.8f} * {columns[i][0]}", flush=True)

    # Now try to get EXACT rational coefficients
    print("\n--- Rationalization ---", flush=True)
    active_cols = [i for i, v in enumerate(sigma) if v > 1e-10]
    A_active = A_mat[:, active_cols]

    # Solve exactly using rational arithmetic
    from fractions import Fraction

    # Build rational matrix
    A_rat = []
    for row_i in range(n_mons):
        row = []
        m = all_mons[row_i]
        for col_j in active_cols:
            name, expr = columns[col_j]
            val = sp.Poly(expr, A, C, p, r).as_dict().get(m, 0)
            row.append(Fraction(val))
        A_rat.append(row)

    g_rat = [Fraction(a0_dict.get(m, 0)) for m in all_mons]

    # Gaussian elimination
    n, m_dim = len(A_rat), len(active_cols)
    aug = [row + [g_rat[i]] for i, row in enumerate(A_rat)]

    pivot_rows = []
    for col in range(m_dim):
        pivot = None
        for row in range(len(pivot_rows), n):
            if aug[row][col] != 0:
                pivot = row
                break
        if pivot is None:
            continue
        aug[len(pivot_rows)], aug[pivot] = aug[pivot], aug[len(pivot_rows)]
        pr_idx = len(pivot_rows)
        pivot_rows.append(pr_idx)
        for row in range(n):
            if row != pr_idx and aug[row][col] != 0:
                factor = Fraction(aug[row][col], aug[pr_idx][col])
                for j in range(m_dim + 1):
                    aug[row][j] -= factor * aug[pr_idx][j]

    solution = [Fraction(0)] * m_dim
    for i in range(len(pivot_rows)-1, -1, -1):
        row = pivot_rows[i]
        pcol = None
        for c in range(m_dim):
            if aug[row][c] != 0:
                pcol = c
                break
        if pcol is None:
            continue
        val = aug[row][m_dim]
        for c in range(pcol+1, m_dim):
            val -= aug[row][c] * solution[c]
        solution[pcol] = Fraction(val, aug[row][pcol])

    all_nonneg = all(s >= 0 for s in solution)
    print(f"All nonneg: {all_nonneg}")

    # Verify
    candidate = defaultdict(lambda: Fraction(0))
    for i, s in enumerate(solution):
        if s != 0:
            col_idx = active_cols[i]
            name, expr = columns[col_idx]
            for m_key, coeff in sp.Poly(expr, A, C, p, r).as_dict().items():
                candidate[m_key] += s * Fraction(coeff)

    errors = {m: Fraction(a0_dict.get(m, 0)) - candidate.get(m, Fraction(0)) for m in all_mons}
    max_err = max(abs(v) for v in errors.values())
    print(f"Max error: {max_err}")

    if max_err == 0 and all_nonneg:
        print("\n*** EXACT RATIONAL CERTIFICATE FOR a0 >= 0 ***")
        for i, s in enumerate(solution):
            if s > 0:
                col_idx = active_cols[i]
                name, expr = columns[col_idx]
                print(f"  {s} * [{name}]")
    elif not all_nonneg:
        print("Some negative coefficients. Need LP on active subset.")
        A_act2 = A_mat[:, active_cols]
        res2 = linprog(np.zeros(len(active_cols)), A_eq=A_act2, b_eq=g_vec,
                       bounds=[(0, None)]*len(active_cols), method='highs')
        if res2.success:
            print("LP on active subset succeeded.")
            sigma2 = res2.x
            for i, v in enumerate(sigma2):
                if v > 1e-10:
                    ci = active_cols[i]
                    fv = Fraction(v).limit_denominator(1000)
                    print(f"  ~{fv} * [{columns[ci][0]}]")

else:
    print(f"\nINFEASIBLE for a0 >= 0: {result.message}", flush=True)

print("\n\n=== Step 2: Check G at boundary (corrected with min(V1,V2)) ===", flush=True)

# G at q=sqrt(min(V1,V2)) and q=-sqrt(min(V1,V2)) with Y = |X|
np.random.seed(123)
min_G = float('inf')
for _ in range(200000):
    Av = np.random.uniform(0.001, 0.999)
    Cv = np.random.uniform(0, 1-Av)
    pv = np.random.uniform(0, Av)
    rv = np.random.uniform(-Cv, Cv)
    Bv = 1 - Av
    V1v = (Av+pv)*(Cv+rv)
    V2v = (Av-pv)*(Cv-rv)
    if V1v < 0 or V2v < 0:
        continue
    q_max = np.sqrt(min(V1v, V2v))
    for qv in [q_max, -q_max, 0]:
        Xv = pv + 2*qv + rv
        Yv = abs(Xv)
        Gv = Av*Cv + (Bv-Cv)*pv*Yv - Av*Bv*Yv**2
        min_G = min(min_G, Gv)

print(f"min(G) over 200K samples: {min_G:.10f}", flush=True)

# Now let's understand WHAT MAKES G(boundary) >= 0.
# G(q_max) = -4AB*q_max^2 + a1*q_max + a0  (for X >= 0 branch)
# = -4AB*V_min + a1*sqrt(V_min) + a0
# = (a0 - 4AB*V_min) + a1*sqrt(V_min)

# We need this >= 0. Since it involves sqrt, let's try a substitution.
# Let s = sqrt(V_min). Then s^2 = V_min <= V2 = (A-p)(C-r).
# G(s) = -4AB*s^2 + a1*s + a0 >= 0.
# This is just G viewed as a function of s.

# G(s) is concave in s (since -4AB < 0). G(0) = a0 >= 0.
# So G(s) >= 0 for s in [0, s_max] where s_max is the positive root.
# s_max = (a1 + sqrt(a1^2 + 16AB*a0)) / (8AB)

# We need: sqrt(V_min) <= s_max.
# <=> V_min <= s_max^2 = (a1 + sqrt(a1^2+16AB*a0))^2 / (64*A^2*B^2)

# This is hard to use directly.

# ALTERNATIVE: Use the algebraic identity approach.
# At q=0: G = a0 >= 0 (proved).
# The q-dependent part: delta_G(q) = G(q) - G(0) = a2*q^2 + a1*q.
# delta_G(q) = q*(a2*q + a1) = q*(-4AB*q + a1)
# For q > 0: delta_G(q) >= 0 iff a1 >= 4AB*q. Since q <= sqrt(V2):
#   a1 >= 4AB*sqrt(V2) is sufficient but not necessary.
# For q < 0: delta_G(q) = q*(-4ABq + a1). With q < 0: -4ABq > 0.
#   delta_G(q) = |q|*(4AB|q| + a1) if a1 >= 0: both terms positive, delta_G < 0 (since q < 0, whole is q*(positive)).
#   Wait: delta_G(q) = q*(-4ABq + a1). For q < 0, let q = -t with t > 0.
#   delta_G = -t*(4ABt + a1). If a1 >= 0: = -t*(positive) < 0. So G(q) = a0 + delta_G(q) = a0 - t*(4ABt+a1).
#   Need: a0 >= t*(4ABt+a1) = 4ABt^2 + a1*t.

# Actually, let me think about this differently.
# G(q) = a0 + q*(a1 - 4AB*q) = a0 + q*a1 - 4AB*q^2.

# For q >= 0 with X >= 0 (p+2q+r >= 0):
# G = a0 + q*a1 - 4AB*q^2 = a0 + q*(a1-4AB*q)
# If a1 >= 0 and q >= 0 and a1 >= 4AB*q: G >= a0 >= 0.
# If a1 >= 0 and 4AB*q > a1: G = a0 + q*a1 - 4AB*q^2 = a0 - q*(4ABq-a1).
#   Use q^2 <= V2 = (A-p)(C-r):
#   4ABq^2 <= 4AB*(A-p)(C-r). And a1*q >= 0.
#   So G >= a0 + a1*q - 4AB*V2.
#   But a1*q >= 0 only helps. And a0 - 4AB*V2 = c0 which can be negative.
#   Need: a1*q >= 4AB*V2 - a0 = -c0.
#   Since c0 < 0 in some cases and a1*q >= 0: need 0 >= -c0, i.e., c0 >= 0. FAIL.

# For q < 0 with X >= 0 (p+2q+r >= 0 => q >= -(p+r)/2):
# G = a0 + q*a1 - 4AB*q^2. Here q < 0 and 4AB*q^2 >= 0.
# G = a0 - |q|*|a1 or negative| - 4AB*q^2.
# If a1 >= 0: G = a0 - |q|*a1 - 4AB*q^2 <= a0. Could be fine since a0 >= 0.
#   Need: a0 >= |q|(a1 + 4AB|q|).
# If a1 < 0: G = a0 + |q|*|a1| - 4AB*q^2. Here -|a1|*|q| helps.
#   G = a0 + q^2*(|a1|/|q| - 4AB). If |a1|/(|q|) > 4AB, G > a0.

# The worst case is q > 0 large (making 4ABq^2 large) and a1 not helping enough.

# KEY INSIGHT: The q that maximizes V2 slack (q=sqrt(V2)) also relates to
# the parameters through r. For large V2, r must be negative (increasing C-r).
# But negative r makes p+r small, which affects a0 and a1.

# Let me try the concavity argument more carefully.
# G is concave in q. G(0) = a0 >= 0. The interval for q is [-sqrt(V_min), sqrt(V_min)].
# If 0 is in the interior: min(G) = min(G(-sqrt(V_min)), G(sqrt(V_min))).
# Both endpoints need to be checked.

# BUT: at q = -sqrt(V_min), X = p - 2*sqrt(V_min) + r could be negative.
# In that case, Y = |X| and G(Y) = AC + (B-C)p*Y - AB*Y^2.
# This is the SAME function of Y as when X >= 0.
# So G at q = -sqrt(V_min) with Y = |X| is ALSO a0 + delta where delta may differ.

# Actually: let me compute G(q) = AC + (B-C)*p*|p+2q+r| - AB*(p+2q+r)^2.
# For X = p+2q+r: G = AC + (B-C)*p*|X| - AB*X^2.
# Note: AB*X^2 = AB*(p+2q+r)^2 and (B-C)*p*|X| depends on sign(X).

# For X >= 0: G = AC + (B-C)*p*X - AB*X^2 (quadratic in X, X=p+2q+r linear in q)
#   = -4ABq^2 + [2(B-C)p - 4AB(p+r)]q + [AC + (B-C)p(p+r) - AB(p+r)^2]
# For X < 0: G = AC - (B-C)*p*X - AB*X^2 (different linear term!)
#   = -4ABq^2 + [-2(B-C)p - 4AB(p+r)]q + [AC - (B-C)p(p+r) - AB(p+r)^2]

# The X < 0 case: a1' = -2(B-C)p - 4AB(p+r), a0' = AC - (B-C)p(p+r) - AB(p+r)^2.
# a0' = a0 - 2(B-C)p(p+r).

# Check a0' >= 0:
a0_prime = sp.expand(A*C - (1-A-C)*p*(p+r) - A*(1-A)*(p+r)**2)
print(f"\na0' (X<0 case) = {sp.factor(a0_prime)}", flush=True)

min_a0p = min(
    float(a0_prime.subs([(A, Av:=np.random.uniform(0.01,0.99)), (C, Cv:=np.random.uniform(0,1-Av)),
                          (p, pv:=np.random.uniform(0,Av)), (r, np.random.uniform(-Cv,Cv))]))
    for _ in range(100000)
)
print(f"min(a0') over 100K: {min_a0p:.10f}", flush=True)

# So a0' is also nonneg! Both G(q=0) cases are fine.
# The issue is at the boundary q = ±sqrt(V_min).

# For the X >= 0 branch at q = sqrt(V_min):
# X = p + 2*sqrt(V_min) + r >= 0 (should hold if V_min isn't too large)
# G = -4AB*V_min + a1*sqrt(V_min) + a0

# For the X < 0 branch at q = -sqrt(V_min):
# X = p - 2*sqrt(V_min) + r < 0
# G = -4AB*V_min + a1'*(-sqrt(V_min)) + a0'
# = -4AB*V_min - a1'*sqrt(V_min) + a0'
# = -4AB*V_min + [2(B-C)p + 4AB(p+r)]*sqrt(V_min) + AC - (B-C)p(p+r) - AB(p+r)^2

# Let me denote: b1 = 2(B-C)p + 4AB(p+r) (the negative of a1')
# G(X<0,q=-s) = -4AB*s^2 + b1*s + a0'

# This is ALSO concave in s. G(0) = a0' >= 0.
# Need: G(s_max) >= 0 where s_max = sqrt(V_min).

# So the FULL problem is:
# BOTH -4AB*s^2 + a1*s + a0 >= 0  AND  -4AB*s^2 + b1*s + a0' >= 0
# for s = sqrt(min(V1, V2)).

# Since both are concave in s with value a0 (resp a0') at s=0, which are >= 0,
# we need each at s_max to be >= 0.

# The function h(s) = -4AB*s^2 + c*s + d where d >= 0 and c is some coefficient.
# h(s) >= 0 for s in [0, s_bound] iff s_bound <= (c + sqrt(c^2+16ABd))/(8AB).
# s_bound = sqrt(V_min).
# So: V_min <= (c + sqrt(c^2+16ABd))^2 / (64A^2B^2).

# For the X >= 0 branch: need V_min * 64A^2B^2 <= (a1 + sqrt(a1^2+16AB*a0))^2.
# For the X < 0 branch: need V_min * 64A^2B^2 <= (b1 + sqrt(b1^2+16AB*a0'))^2.

# These involve sqrt. Hard to prove algebraically.

# SIMPLER: Use AM-GM on the q-dependent terms.
# G(q) = a0 + a1*q - 4AB*q^2
# >= a0 - |a1|*|q| - 4AB*q^2
# >= a0 - |a1|*sqrt(V_min) - 4AB*V_min

# We need: a0 >= |a1|*sqrt(V_min) + 4AB*V_min.
# By AM-GM: |a1|*sqrt(V_min) <= a1^2/(8AB*epsilon) + 2AB*epsilon*V_min for any epsilon > 0.
# With epsilon = 1: |a1|*sqrt(V_min) <= a1^2/(8AB) + 2AB*V_min.
# So: a0 >= a1^2/(8AB) + 2AB*V_min + 4AB*V_min = a1^2/(8AB) + 6AB*V_min.
# Hmm, that's worse.

# Instead: a0 - 4AB*V_min >= |a1|*sqrt(V_min).
# If a0 - 4AB*V_min >= 0: squaring, (a0-4AB*V_min)^2 >= a1^2*V_min.
# If a0 - 4AB*V_min < 0 but a0 - 4AB*V_min + |a1|*sqrt(V_min) >= 0:
#   |a1|*sqrt(V_min) >= 4AB*V_min - a0, squaring: a1^2*V_min >= (4AB*V_min - a0)^2.

# The first case (a0 >= 4AB*V_min): squaring gives a0^2 - 8AB*a0*V_min + 16A^2B^2*V_min^2 >= a1^2*V_min.
# i.e., a0^2 >= V_min*(a1^2 + 8AB*a0 - 16A^2B^2*V_min).

# This is a polynomial inequality!
# a0^2 + 16A^2B^2*V_min^2 - 8AB*a0*V_min - a1^2*V_min >= 0
# = a0^2 - V_min*(8AB*a0 + a1^2 - 16A^2B^2*V_min)

# Actually I realize: the condition c0^2 >= a1^2*V (where c0 = a0 - 4AB*V and V = V_min)
# is POLYNOMIAL in (A,C,p,r). Since V_min = min(V1,V2), we can case split:
# Case V2 <= V1: V_min = V2. Condition: (a0-4AB*V2)^2 >= a1^2*V2.
# Case V1 <= V2: V_min = V1. Condition: (a0-4AB*V1)^2 >= a1^2*V1.

# But we also need c0 + a1*sqrt(V) >= 0, which when c0 < 0 and a1 > 0, is:
# a1*sqrt(V) >= -c0, i.e., a1^2*V >= c0^2. This is the OPPOSITE inequality!

# So the correct condition is:
# h(s) = -4AB*s^2 + a1*s + a0 >= 0 at s = sqrt(V)
# <=> a0 + a1*sqrt(V) - 4AB*V >= 0
# <=> c0 + a1*sqrt(V) >= 0 where c0 = a0 - 4AB*V

# This has TWO regimes:
# If c0 >= 0: automatically true (since a1*sqrt(V) could be neg, but c0 >= 0 AND
#   a1 could be positive making the sum even larger).
#   Wait, if a1 < 0: c0 + a1*sqrt(V) could be < c0. Need c0 >= |a1|*sqrt(V).
#   i.e., c0^2 >= a1^2*V.
# If c0 < 0: need a1 > 0 (since a1*sqrt(V) must overcome -c0).
#   Then: a1*sqrt(V) >= -c0 = |c0|, i.e., a1^2*V >= c0^2.

# In BOTH cases: the condition is c0^2 <= a1^2*V when c0 < 0, and c0^2 >= a1^2*V when c0 >= 0.
# More precisely: the condition is (c0 + a1*sqrt(V))(c0 - a1*sqrt(V) + 8AB*sqrt(V)?) ... hmm.

# Actually it's simply: c0 + a1*sqrt(V) >= 0.
# Squaring BOTH SIDES requires knowing the sign. Instead:
# h(s) = -4AB*s^2 + a1*s + a0 = -4AB*(s-s_1)(s-s_2) where s_1,s_2 are roots.
# h(s) >= 0 for s between the roots. Since h(0) = a0 >= 0, s=0 is between the roots.
# The positive root is s_+ = (a1 + sqrt(a1^2+16AB*a0))/(8AB).
# We need s <= s_+, i.e., sqrt(V) <= s_+.
# V <= s_+^2 = (a1+sqrt(D))^2/(64A^2B^2) where D = a1^2+16AB*a0.

# Equivalently: 64A^2B^2*V <= (a1+sqrt(D))^2 = a1^2 + 2*a1*sqrt(D) + D = 2*a1^2 + 16AB*a0 + 2*a1*sqrt(D).
# i.e., 64A^2B^2*V - 2*a1^2 - 16AB*a0 <= 2*a1*sqrt(D)
# i.e., 32A^2B^2*V - a1^2 - 8AB*a0 <= a1*sqrt(D)

# Let L = 32A^2B^2*V - a1^2 - 8AB*a0.
# If L <= 0: condition is automatically satisfied (since a1*sqrt(D) >= 0 when a1 >= 0, or ...
#   Actually a1 can be negative too. If a1 < 0: a1*sqrt(D) < 0, and L could be < a1*sqrt(D).
#   Need more care.)

# This is getting circular. Let me just try the LP approach on the polynomial condition.

# The polynomial condition: for the X >= 0 branch with V_min = V2:
# f(s) = -4AB*s^2 + a1*s + a0 >= 0 at s = sqrt(V2).
# This means: f(s) * f(s) ... no.

# KEY: f(s) = 0 at s = s_+ (positive root). We need sqrt(V2) <= s_+.
# s_+^2 = something polynomial in (A,C,p,r) divided by something.
# V2 = (A-p)(C-r).
# s_+^2 - V2 >= 0 is equivalent to our condition.

# s_+^2 = (a1 + sqrt(a1^2+16ABa0))^2 / (64A^2B^2)
# This involves sqrt(a1^2+16ABa0). NOT polynomial.

# WHAT IF we use the OTHER representation:
# f(sqrt(V2)) >= 0 <=> a0*V2 >= a1^2*V2 / ... no.

# WHAT IF we just observe:
# f(s) >= 0 <=> 4AB*s^2 - a1*s <= a0
# <=> s*(4AB*s - a1) <= a0

# With s = sqrt(V2): sqrt(V2)*(4AB*sqrt(V2) - a1) <= a0
# <=> 4AB*V2 - a1*sqrt(V2) <= a0  (assuming the factor is positive, which it is when 4AB*sqrt(V2) > a1)
# This just rearranges to our condition.

# OK, I think the algebraic proof must go through a different route entirely.
# Let me try: express G(q) EXPLICITLY as a sum of nonneg terms.

# G(q) = AC + (B-C)*p*(p+2q+r) - AB*(p+2q+r)^2  (for X >= 0)
#       = AC + (B-C)*p*X - AB*X^2
# where X = p+2q+r, V1: q^2 <= (A+p)(C+r), V2: q^2 <= (A-p)(C-r).

# From V1*V2: q^4 <= (A^2-p^2)(C^2-r^2).
# From V1+V2: 2*q^2 <= (A+p)(C+r)+(A-p)(C-r) = 2(AC+pr). So q^2 <= AC+pr.
# Weighted: A*q^2 <= C*(A^2-p^2), C*q^2 <= A*(C^2-r^2).

# X^2 = (p+2q+r)^2 = (p+r)^2 + 4(p+r)q + 4q^2
# Using q^2 <= AC+pr:
# 4q^2 <= 4AC + 4pr
# X^2 <= (p+r)^2 + 4(p+r)q + 4AC + 4pr = (p+r)^2 + 4(p+r)q + 4AC + 4pr

# So AB*X^2 <= AB[(p+r)^2 + 4(p+r)q + 4AC + 4pr]
# = AB(p+r)^2 + 4AB(p+r)q + 4A^2BC + 4ABpr

# (B-C)*p*X = (B-C)*p*(p+r+2q) = (B-C)*p*(p+r) + 2(B-C)*p*q

# G = AC + (B-C)p(p+r) + 2(B-C)pq - AB(p+r)^2 - 4AB(p+r)q - 4ABq^2
# >= AC + (B-C)p(p+r) + 2(B-C)pq - AB(p+r)^2 - 4AB(p+r)q - 4AB(AC+pr)
#    (using q^2 <= AC+pr)
# = AC(1-4AB) + (B-C)p(p+r) - AB(p+r)^2 - 4ABpr + [2(B-C)p - 4AB(p+r)]q
# = AC(2A-1)^2 + [(B-C) - AB]p^2 + [(B-C) - 2AB - 4AB]pr + (- AB)r^2 + a1*q

# Hmm, the q term remains. We need to bound |a1*q| using constraints.
# From weighted: A*q^2 <= C(A^2-p^2). So |q| <= sqrt(C*(A-p)*(A+p)/A).
# |a1*q| <= |a1| * sqrt(C*(A^2-p^2)/A)

# But this still involves sqrt. Unless we use AM-GM:
# |a1*q| <= a1^2/(8AB*k) + 2AB*k*q^2 for any k > 0.
# Using q^2 <= AC+pr: |a1*q| <= a1^2/(8AB*k) + 2AB*k*(AC+pr).

# Choose k to minimize: a1^2/(8AB*k) + 2AB*k*(AC+pr).
# Optimal k = |a1|/(4AB*sqrt(AC+pr)). Min = |a1|*sqrt(AC+pr)/(2AB)... still sqrt.

# OR: use a1^2*q^2 <= a1^2*V_bound. Then by AM-GM:
# 2|a1*q| <= a1^2/epsilon + epsilon*q^2.
# With epsilon = 4AB (the coefficient of -q^2 in G):
# 2|a1*q| <= a1^2/(4AB) + 4AB*q^2
# |a1*q| <= a1^2/(8AB) + 2AB*q^2

# Then: G >= AC(2A-1)^2 + stuff - |a1*q|
# >= AC(2A-1)^2 + stuff - a1^2/(8AB) - 2AB*q^2
# = AC(2A-1)^2 + stuff - a1^2/(8AB) - 2AB*q^2

# But we already used q^2 <= AC+pr for the 4ABq^2 term. The remaining is -2AB*q^2 (from the AM-GM).
# So: -4ABq^2 - 2ABq^2 = -6ABq^2. Hmm, overshoot.

# Let me try: split the -4ABq^2 differently.
# G = a0 + a1*q - 4ABq^2
# = a0 + a1*q - 2ABq^2 - 2ABq^2
# >= a0 + a1*q - 2AB(AC+pr) - 2ABq^2  (using q^2 <= AC+pr for ONE copy)
# Now: a1*q - 2ABq^2. Complete the square: = -2AB(q-a1/(4AB))^2 + a1^2/(8AB)
# >= -2AB*V_min + a1^2/(8AB)  (min of downward parabola on interval)

# Actually this is WORSE: -2AB(q-a1/(4AB))^2 <= 0 always, so a1*q - 2ABq^2 <= a1^2/(8AB).
# So G >= a0 - 2AB(AC+pr) + (a1*q - 2ABq^2)
# >= a0 - 2AB(AC+pr) + min(a1*q - 2ABq^2)  over feasible q
# The min of a1*q - 2ABq^2 (downward parabola) on [-s,s] is min at endpoint:
# min(a1*s - 2ABs^2, -a1*s - 2ABs^2) = -|a1|*s - 2AB*s^2

# So G >= a0 - 2AB(AC+pr) - |a1|*s - 2ABs^2 where s = sqrt(V_min).
# Need: a0 - 2AB(AC+pr) >= |a1|*s + 2ABs^2

# a0 - 2AB(AC+pr) = AC + (B-C)p(p+r) - AB(p+r)^2 - 2A^2BC - 2ABpr
# = AC(1-2AB) + (B-C)p^2 + (B-C-2AB)pr - AB(p+r)^2 + ...
# This is getting nowhere. The fundamental issue is that we can't avoid sqrt(V_min).

# FINAL ATTEMPT: Use the Q^2 substitution directly.
# Define the substitution: s^2 = min(V1, V2). The condition G(s) >= 0 is:
# a0 + a1*s - 4AB*s^2 >= 0 (for the X>=0 branch)
# where s^2 = min(V1, V2) = V2 when V2 <= V1 (case Ar+pC >= 0).
# This is equivalent to: a0 + a1*s >= 4AB*s^2.
# With s^2 = V2: a0 + a1*s >= 4AB*V2.
# i.e., a0 - 4AB*V2 >= -a1*s.
# Let c = a0 - 4AB*V2. Then c + a1*s >= 0.

# Case a1 >= 0, s >= 0: c + a1*s >= c. So need c >= 0 if a1*s doesn't help.
#   But a1*s >= 0, so c + a1*s >= c. If c >= 0: done. If c < 0: need a1*s >= |c|.
#   s^2 = V2, so a1^2*V2 >= c^2.

# Case a1 < 0, s >= 0: c + a1*s = c - |a1|*s. Need c >= |a1|*s.
#   c^2 >= a1^2*V2.

# In all cases: need c^2 >= a1^2*V2 when c >= 0, or a1^2*V2 >= c^2 when c < 0 and a1 > 0.
# These are DIFFERENT polynomial conditions!

# Unification: c + a1*s >= 0 where c = a0-4ABV2, s = sqrt(V2) >= 0.
# Multiply by c - a1*s (ASSUMING c >= a1*s, which isn't always true):
# (c+a1*s)(c-a1*s) = c^2 - a1^2*V2.
# If c + a1*s >= 0 and c - a1*s >= 0: then c^2 >= a1^2*V2.
# If c + a1*s >= 0 and c - a1*s < 0: then c < a1*s but c + a1*s >= 0, so c >= -a1*s.
#   In this case c^2 <= a1^2*V2. And the product (c+a1s)(c-a1s) <= 0.

# So: G(boundary) >= 0 does NOT imply c^2 >= a1^2*V2.
# And c^2 >= a1^2*V2 implies G(boundary) >= 0 ONLY when c >= 0.

# When c < 0: we need a1 > 0 AND a1^2*V2 >= c^2. This is a1^2*V2 >= c^2.

# So the POLYNOMIAL conditions are (case split):
# Case c >= 0 (i.e., a0 >= 4ABV2): need c^2 >= a1^2*V2, i.e., (a0-4ABV2)^2 >= a1^2*V2.
# Case c < 0 (i.e., a0 < 4ABV2): need a1 >= 0 AND a1^2*V2 >= (a0-4ABV2)^2 = (4ABV2-a0)^2.

# Wait, actually when c < 0, c + a1*s >= 0 requires a1*s >= |c|, so a1 > 0 and a1^2*s^2 >= c^2,
# which is a1^2*V2 >= c^2. This is equivalent to: c^2 - a1^2*V2 <= 0, i.e., c^2 <= a1^2*V2.

# So the full polynomial condition is:
# (a0 - 4ABV2)^2 <= a1^2*V2  WHEN  a0 < 4ABV2
# (a0 - 4ABV2)^2 >= a1^2*V2  WHEN  a0 >= 4ABV2  [WRONG - this isn't needed; c >= 0 is sufficient when a1*s >= 0]

# Actually when c >= 0 and a1 >= 0: c + a1*s >= 0 automatically. No further condition.
# When c >= 0 and a1 < 0: need c >= |a1|*s, i.e., c^2 >= a1^2*V2.

# So full condition:
# If c >= 0 and a1 >= 0: OK.
# If c >= 0 and a1 < 0: c^2 >= a1^2*V2.
# If c < 0 and a1 >= 0: a1^2*V2 >= c^2.
# If c < 0 and a1 < 0: c + a1*s < 0 always (impossible). Wait, c < 0 and a1 < 0:
#   c + a1*s = (negative) + (negative)*s < 0. So G(boundary) < 0!
#   But we KNOW G(boundary) >= 0 from numerics. So c < 0 and a1 < 0 CANNOT happen simultaneously.

# Verify: when c < 0, is a1 always >= 0?
print("\n=== Verify: when c < 0, a1 >= 0 ===", flush=True)
count_bad = 0
for _ in range(500000):
    Av = np.random.uniform(0.01, 0.99)
    Cv = np.random.uniform(0, 1-Av)
    pv = np.random.uniform(0, Av)
    rv = np.random.uniform(-Cv, Cv)
    Bv = 1 - Av
    V2v = (Av-pv)*(Cv-rv)
    c_val = Av*Cv + (Bv-Cv)*pv*(pv+rv) - Av*Bv*(pv+rv)**2 - 4*Av*Bv*V2v
    a1_val = 2*(Bv-Cv)*pv - 4*Av*Bv*(pv+rv)
    if c_val < -1e-10 and a1_val < -1e-10:
        count_bad += 1
        if count_bad <= 3:
            print(f"  BAD: A={Av:.4f} C={Cv:.4f} p={pv:.4f} r={rv:.4f} c={c_val:.6f} a1={a1_val:.6f}")

print(f"Violations: {count_bad} out of 500K", flush=True)

if count_bad > 0:
    print("c < 0 and a1 < 0 CAN happen! But we need to check the X < 0 branch too.")
    print("When a1 < 0, the X < 0 branch uses b1 = -a1 > 0.")
    print("And the X < 0 branch has q = -s, so the condition uses b1.")
    print("So: for the X >= 0 branch at q = s: c0 + a1*s >= 0")
    print("    for the X < 0 branch at q = -s: c0' + b1*s >= 0 where b1 = -(a1 + 8AB(p+r))... ")
    print("Actually, let me reconsider. At q = sqrt(V_min), X = p+2q+r >= 0 if p+r+2*sqrt(V_min) >= 0.")
    print("If V_min is small enough, X > 0. But if V_min is large (sqrt(V_min) > (p+r)/2), X > 0 still.")
    print("Actually X = p+r+2*sqrt(V_min) is ALWAYS >= p+r >= p-C. When p > C, X > 0.")
    print("When p <= C: X = p+r+2s >= p-C+2s. Since s = sqrt(V_min) >= 0, X >= p-C.")
    print("X could be negative only if p+r < 0 and 2s < |p+r|, but s^2 <= V2 and ...")
else:
    print("When c < 0, a1 is always >= 0! Good.")
    print("\nSo the proof has two polynomial conditions:")
    print("  (1) a0 >= 0 on feasible set (DONE above)")
    print("  (2) When a0 - 4ABV2 < 0: a1^2*V2 >= (a0-4ABV2)^2 on feasible set")
    print("  Combined: (a0-4ABV2)^2 <= a1^2*V2 + (a0-4ABV2)*max(0, a0-4ABV2)")
