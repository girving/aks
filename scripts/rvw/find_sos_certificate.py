"""
Find nonneg linear combination certificate for the RVW quadratic inequality.
G = (b^2-c^2)*p*X + a^2*c^2 - a^2*b^2*X^2 >= 0
"""
import numpy as np
from scipy.optimize import linprog
from fractions import Fraction
from collections import defaultdict

np.random.seed(42)

def generate_feasible_point():
    a2 = np.random.uniform(0.01, 0.99)
    b2 = 1.0 - a2
    c2 = np.random.uniform(0.0, b2)
    p = np.random.uniform(0.0, a2)
    r = np.random.uniform(-c2, c2)
    max_q2 = min((a2 + p)*(c2 + r), (a2 - p)*(c2 - r))
    if max_q2 < 0:
        return None
    max_q = np.sqrt(max_q2)
    q = np.random.uniform(-max_q, max_q)
    X = p + 2*q + r
    if X < -1e-12:
        return None
    return a2, c2, p, q, r

# Polynomial arithmetic: monomial = (a2_exp, c2_exp, p_exp, q_exp, r_exp)
def pc(c):
    return {(0,0,0,0,0): c}

def pv(idx):
    m = [0,0,0,0,0]; m[idx] = 1
    return {tuple(m): 1.0}

def padd(p1, p2, s1=1.0, s2=1.0):
    result = defaultdict(float)
    for m, c in p1.items(): result[m] += s1 * c
    for m, c in p2.items(): result[m] += s2 * c
    return {m: c for m, c in result.items() if abs(c) > 1e-15}

def pmul(p1, p2):
    result = defaultdict(float)
    for m1, c1 in p1.items():
        for m2, c2_ in p2.items():
            m = tuple(a + b for a, b in zip(m1, m2))
            result[m] += c1 * c2_
    return {m: c for m, c in result.items() if abs(c) > 1e-15}

def psub(p1, p2): return padd(p1, p2, 1.0, -1.0)

def mono_str(m):
    names = ["a2", "c2", "p", "q", "r"]
    parts = []
    for i, e in enumerate(m):
        if e == 1: parts.append(names[i])
        elif e > 1: parts.append(f"{names[i]}^{e}")
    return "*".join(parts) if parts else "1"

# Basic polynomials
A2 = pv(0); C2 = pv(1); P = pv(2); Q = pv(3); R = pv(4)
ONE = pc(1.0); Q2 = {(0,0,0,2,0): 1.0}

B2 = psub(ONE, A2)
Xp = padd(padd(P, Q, 1.0, 2.0), R)
BmC = psub(B2, C2)

V1 = psub(pmul(padd(A2, P), padd(C2, R)), Q2)
V2 = psub(pmul(psub(A2, P), psub(C2, R)), Q2)

X2 = pmul(Xp, Xp)
G_poly = psub(padd(pmul(pmul(BmC, P), Xp), pmul(A2, C2)), pmul(pmul(A2, B2), X2))

sum_cs = psub(padd(pmul(A2, C2), pmul(P, R)), Q2)
weighted_cs = psub(pmul(C2, psub(pmul(A2, A2), pmul(P, P))), pmul(A2, Q2))

# Build nonneg terms dictionary
terms = {}
terms["(a2-p)*V1"] = pmul(psub(A2, P), V1)
terms["(a2+p)*V2"] = pmul(padd(A2, P), V2)
terms["p*V2"] = pmul(P, V2)
terms["X*V1"] = pmul(Xp, V1)
terms["X*V2"] = pmul(Xp, V2)
terms["(c2-r)*V1"] = pmul(psub(C2, R), V1)
terms["(c2+r)*V2"] = pmul(padd(C2, R), V2)
terms["p*X"] = pmul(P, Xp)
terms["(b2-c2)*p*X"] = pmul(pmul(BmC, P), Xp)
terms["sum_cs"] = sum_cs
terms["weighted_cs"] = weighted_cs
terms["q^2"] = Q2
terms["p^2"] = {(0,0,2,0,0): 1.0}
terms["r^2"] = {(0,0,0,0,2): 1.0}
terms["c2^2"] = {(0,2,0,0,0): 1.0}
terms["(p-r)^2"] = pmul(psub(P, R), psub(P, R))
terms["(b2-c2)*q^2"] = pmul(BmC, Q2)
terms["a2*q^2"] = pmul(A2, Q2)
terms["p*q^2"] = pmul(P, Q2)
terms["X*q^2"] = pmul(Xp, Q2)
terms["a2*p*X"] = pmul(pmul(A2, P), Xp)
terms["c2*p*X"] = pmul(pmul(C2, P), Xp)
terms["a2*c2*X"] = pmul(pmul(A2, C2), Xp)
terms["a2*c2*p"] = pmul(pmul(A2, C2), P)
terms["a2*(b2-c2)"] = pmul(A2, BmC)
terms["c2*(b2-c2)"] = pmul(C2, BmC)
terms["a2*V1"] = pmul(A2, V1)
terms["a2*V2"] = pmul(A2, V2)
terms["c2*V1"] = pmul(C2, V1)
terms["c2*V2"] = pmul(C2, V2)
terms["(a2-p)*(c2-r)"] = pmul(psub(A2, P), psub(C2, R))
terms["(a2+p)*(c2+r)"] = pmul(padd(A2, P), padd(C2, R))
terms["(a2-p)*(c2+r)"] = pmul(psub(A2, P), padd(C2, R))
terms["(a2+p)*(c2-r)"] = pmul(padd(A2, P), psub(C2, R))
terms["(b2-c2)*p"] = pmul(BmC, P)
terms["(b2-c2)*X"] = pmul(BmC, Xp)
terms["p*(c2+r)"] = pmul(P, padd(C2, R))
terms["p*(c2-r)"] = pmul(P, psub(C2, R))
terms["X*(a2-p)"] = pmul(Xp, psub(A2, P))
terms["X*(c2-r)"] = pmul(Xp, psub(C2, R))
terms["X*(c2+r)"] = pmul(Xp, padd(C2, R))
terms["X*(b2-c2)"] = pmul(Xp, BmC)
terms["a2*X^2"] = pmul(A2, X2)
terms["c2*X^2"] = pmul(C2, X2)
terms["p*X^2"] = pmul(P, X2)
terms["(b2-c2)*X^2"] = pmul(BmC, X2)
terms["a2*p^2"] = pmul(A2, pmul(P, P))
terms["a2*r^2"] = pmul(A2, pmul(R, R))
terms["c2*p^2"] = pmul(C2, pmul(P, P))
terms["p*sum_cs"] = pmul(P, sum_cs)
terms["X*sum_cs"] = pmul(Xp, sum_cs)
terms["a2*sum_cs"] = pmul(A2, sum_cs)
terms["(b2-c2)*sum_cs"] = pmul(BmC, sum_cs)
terms["p*V1"] = pmul(P, V1)
terms["(b2-c2)*V1"] = pmul(BmC, V1)
terms["(b2-c2)*V2"] = pmul(BmC, V2)
terms["a2*c2"] = pmul(A2, C2)
terms["a2*p"] = pmul(A2, P)
terms["a2*X"] = pmul(A2, Xp)
terms["c2*p"] = pmul(C2, P)
terms["c2*X"] = pmul(C2, Xp)
terms["a2*c2*q^2"] = pmul(pmul(A2, C2), Q2)
terms["(b2-c2)*p*q^2"] = pmul(pmul(BmC, P), Q2)
terms["a2*p*q^2"] = pmul(pmul(A2, P), Q2)
terms["a2*(b2-c2)*p"] = pmul(pmul(A2, BmC), P)
terms["a2*(b2-c2)*X"] = pmul(pmul(A2, BmC), Xp)
terms["c2*(b2-c2)*p"] = pmul(pmul(C2, BmC), P)
terms["c2*(b2-c2)*X"] = pmul(pmul(C2, BmC), Xp)
terms["a2*c2*(b2-c2)"] = pmul(pmul(A2, C2), BmC)
terms["a2^2*c2"] = pmul(pmul(A2, A2), C2)
terms["a2*c2^2"] = pmul(A2, pmul(C2, C2))
terms["a2^2*p*X"] = pmul(pmul(A2, A2), pmul(P, Xp))
terms["c2*p*r"] = pmul(pmul(C2, P), R)
terms["a2*p*r"] = pmul(pmul(A2, P), R)
terms["a2^2*X^2"] = pmul(pmul(A2, A2), X2)
terms["a2^2*q^2"] = pmul(pmul(A2, A2), Q2)
terms["c2^2*p*X"] = pmul(pmul(C2, C2), pmul(P, Xp))
terms["(b2-c2)^2"] = pmul(BmC, BmC)
terms["a2^2*(b2-c2)"] = pmul(pmul(A2, A2), BmC)
terms["p*weighted_cs"] = pmul(P, weighted_cs)
terms["X*weighted_cs"] = pmul(Xp, weighted_cs)
terms["(a2-p)*sum_cs"] = pmul(psub(A2, P), sum_cs)
terms["(c2-r)*sum_cs"] = pmul(psub(C2, R), sum_cs)
terms["(c2+r)*sum_cs"] = pmul(padd(C2, R), sum_cs)
terms["X*(a2-p)*(c2-r)"] = pmul(Xp, pmul(psub(A2, P), psub(C2, R)))
terms["p*(a2-p)*(c2-r)"] = pmul(P, pmul(psub(A2, P), psub(C2, R)))
terms["(b2-c2)*(a2-p)"] = pmul(BmC, psub(A2, P))
terms["(b2-c2)*(c2-r)"] = pmul(BmC, psub(C2, R))
terms["(b2-c2)*(c2+r)"] = pmul(BmC, padd(C2, R))
terms["(b2-c2)*a2*c2"] = pmul(BmC, pmul(A2, C2))

# Collect monomials and build matrix
all_monomials = set()
for m in G_poly: all_monomials.add(m)
for name, poly in terms.items():
    for m in poly: all_monomials.add(m)

monomials = sorted(all_monomials)
mono_idx = {m: i for i, m in enumerate(monomials)}
n_mono = len(monomials)
term_names = list(terms.keys())
n_terms = len(term_names)

print(f"Number of monomials: {n_mono}")
print(f"Number of nonneg terms: {n_terms}")

g_vec = np.zeros(n_mono)
for m, c in G_poly.items():
    g_vec[mono_idx[m]] = c

A_mat = np.zeros((n_mono, n_terms))
for j, name in enumerate(term_names):
    for m, c in terms[name].items():
        if m in mono_idx:
            A_mat[mono_idx[m], j] += c

print(f"\nG polynomial:")
for i, m in enumerate(monomials):
    if abs(g_vec[i]) > 1e-15:
        print(f"  {g_vec[i]:+10.4f} * {mono_str(m)}")

# Verify nonnegativity
print("\nVerifying nonnegativity of terms...")
neg_terms = set()
for _ in range(20000):
    pt = generate_feasible_point()
    if pt is None: continue
    a2, c2, p, q, r = pt
    for j, name in enumerate(term_names):
        val = 0.0
        for m, c in terms[name].items():
            mv = c
            for k, e in enumerate(m):
                if e > 0: mv *= [a2, c2, p, q, r][k] ** e
            val += mv
        if val < -1e-10:
            neg_terms.add(name)

if neg_terms:
    print(f"  WARNING: {len(neg_terms)} terms NOT always nonneg:")
    for name in sorted(neg_terms): print(f"    {name}")
    for name in list(neg_terms):
        idx = term_names.index(name)
        term_names.pop(idx)
        A_mat = np.delete(A_mat, idx, axis=1)
        del terms[name]
    n_terms = len(term_names)
    print(f"  After removal: {n_terms} terms remain")
else:
    print(f"  All {n_terms} terms verified nonneg")

# Phase 1: Exact monomial matching
print("\n" + "=" * 60)
print("Phase 1: Exact monomial matching (A lam = g, lam >= 0)")
print("=" * 60)

c_obj = np.ones(n_terms)
result = linprog(c_obj, A_eq=A_mat, b_eq=g_vec,
                 bounds=[(0, None)]*n_terms, method="highs")

if result.success:
    lam = result.x
    residual = A_mat @ lam - g_vec
    print(f"  SOLVED! Objective = {result.fun:.6f}")
    print(f"  Max residual: {np.max(np.abs(residual)):.2e}")
    active = [(term_names[i], lam[i]) for i in range(n_terms) if lam[i] > 1e-12]
    active.sort(key=lambda x: -x[1])
    print(f"\n  Certificate ({len(active)} terms):")
    print("  " + "-" * 55)
    for name, val in active:
        frac = Fraction(val).limit_denominator(10000)
        err = abs(val - float(frac))
        marker = " <--" if err > 1e-6 else ""
        print(f"  {val:16.12f} * {name:30s}  ~ {str(frac):>10s}{marker}")
else:
    print(f"  Failed: {result.message}")

# Phase 2: Inequality
print("\n" + "=" * 60)
print("Phase 2: Inequality (A lam >= g, lam >= 0)")
print("=" * 60)

result2 = linprog(c_obj, A_ub=-A_mat, b_ub=-g_vec,
                  bounds=[(0, None)]*n_terms, method="highs")

if result2.success:
    lam2 = result2.x
    slack = A_mat @ lam2 - g_vec
    print(f"  SOLVED! Objective = {result2.fun:.6f}")
    print(f"  Slack range: [{slack.min():.6e}, {slack.max():.6e}]")
    active2 = [(term_names[i], lam2[i]) for i in range(n_terms) if lam2[i] > 1e-12]
    active2.sort(key=lambda x: -x[1])
    print(f"\n  Certificate ({len(active2)} terms):")
    print("  " + "-" * 55)
    for name, val in active2:
        frac = Fraction(val).limit_denominator(10000)
        err = abs(val - float(frac))
        marker = " <--" if err > 1e-6 else ""
        print(f"  {val:16.12f} * {name:30s}  ~ {str(frac):>10s}{marker}")
    slack_nonzero = [(monomials[i], slack[i]) for i in range(n_mono) if abs(slack[i]) > 1e-10]
    if slack_nonzero:
        print(f"\n  Slack polynomial:")
        for m, s in sorted(slack_nonzero, key=lambda x: -abs(x[1])):
            print(f"    {s:+12.8f} * {mono_str(m)}")
else:
    print(f"  Failed: {result2.message}")

# Phase 3: Numerical verification
print("\n" + "=" * 60)
print("Phase 3: Numerical verification")
print("=" * 60)

best_lam = None
if result.success:
    best_lam = result.x
    print("  Using exact solution")
elif result2.success:
    best_lam = result2.x
    print("  Using inequality solution")

if best_lam is not None:
    print("  Verifying at 100000 random points...")
    max_err = 0; max_viol = 0; n_checked = 0; attempts = 0
    while n_checked < 100000 and attempts < 300000:
        pt = generate_feasible_point()
        if pt is None: attempts += 1; continue
        n_checked += 1; attempts += 1
        a2, c2, p, q, r = pt
        b2 = 1.0 - a2; Xv = p + 2*q + r
        G_val = (b2 - c2)*p*Xv + a2*c2 - a2*b2*Xv**2
        approx = 0.0
        for j in range(n_terms):
            if best_lam[j] < 1e-12: continue
            val = 0.0
            for m, c in terms[term_names[j]].items():
                mv = c
                for k, e in enumerate(m):
                    if e > 0: mv *= [a2, c2, p, q, r][k] ** e
                val += mv
            approx += best_lam[j] * val
        err = abs(G_val - approx)
        max_err = max(max_err, err)
        if G_val > approx + 1e-8:
            max_viol = max(max_viol, G_val - approx)
    print(f"  Checked {n_checked} points")
    print(f"  Max |G - approx|: {max_err:.2e}")
    print(f"  Max violation (G > approx): {max_viol:.2e}")

# Phase 4: Rational certificate
if best_lam is not None:
    print("\n" + "=" * 60)
    print("Phase 4: Rational certificate")
    print("=" * 60)
    active_data = [(i, term_names[i], best_lam[i]) for i in range(n_terms) if best_lam[i] > 1e-12]
    active_idx_list = [d[0] for d in active_data]
    active_names_list = [d[1] for d in active_data]
    active_vals = [d[2] for d in active_data]
    A_active = A_mat[:, active_idx_list]

    for denom_limit in [10, 100, 1000, 10000]:
        fracs = [Fraction(v).limit_denominator(denom_limit) for v in active_vals]
        frac_vec = np.array([float(f) for f in fracs])
        residual_frac = A_active @ frac_vec - g_vec
        max_res = np.max(np.abs(residual_frac))
        all_nonneg = all(f >= 0 for f in fracs)
        print(f"  Denom limit {denom_limit:5d}: max_res = {max_res:.2e}, all_nonneg = {all_nonneg}")
        if max_res < 1e-10 and all_nonneg:
            print(f"\n  *** EXACT RATIONAL CERTIFICATE (denom <= {denom_limit}) ***")
            print(f"  G =")
            for name, frac in zip(active_names_list, fracs):
                if frac > 0:
                    print(f"    + ({frac}) * {name}")
            break
        elif max_res < 1e-6:
            print(f"  Close! Fracs: {list(zip(active_names_list, fracs))}")

print("\nDone.")
