#!/usr/bin/env python3
"""Find SOS certificate for RVW quadratic inequality.

Goal (case p>=0, X>=0):
  G = (b2-c2)*p*X + a2*c2 - a2*b2*X^2 >= 0

where X = p+2q+r, b2 = 1-a2, and:
  V1 = (a2+p)(c2+r) - q^2 >= 0
  V2 = (a2-p)(c2-r) - q^2 >= 0
  sum_CS: q^2 <= a2*c2 + p*r
  weighted_CS: a2*q^2 <= c2*(a2^2 - p^2)
  p >= 0, X >= 0, a2-p >= 0, a2+p >= 0, c2-r >= 0, c2+r >= 0, b2-c2 >= 0

Strategy: Express G = sum of lambda_i * nonneg_term_i where each nonneg_term_i is
a product of constraints, signs, and squares.
"""
import numpy as np
from scipy.optimize import linprog
from fractions import Fraction
from collections import defaultdict

# Variables: a2, c2, p, q, r  (indices 0,1,2,3,4)
# X = p + 2q + r (derived)
# b2 = 1-a2 (derived)

def poly_zero():
    return defaultdict(float)

def poly_var(i):
    """Variable i as polynomial."""
    p = poly_zero()
    p[(0,0,0,0,0)] = 0  # ensure zero exists
    tup = [0,0,0,0,0]
    tup[i] = 1
    p[tuple(tup)] = 1.0
    return p

def poly_const(c):
    p = poly_zero()
    p[(0,0,0,0,0)] = c
    return p

def padd(a, b):
    r = poly_zero()
    for m, c in a.items(): r[m] += c
    for m, c in b.items(): r[m] += c
    return r

def psub(a, b):
    r = poly_zero()
    for m, c in a.items(): r[m] += c
    for m, c in b.items(): r[m] -= c
    return r

def pmul(a, b):
    r = poly_zero()
    for ma, ca in a.items():
        for mb, cb in b.items():
            m = tuple(ma[i]+mb[i] for i in range(5))
            r[m] += ca * cb
    return r

def pscale(a, s):
    r = poly_zero()
    for m, c in a.items(): r[m] = c * s
    return r

def psq(a):
    return pmul(a, a)

def clean(p, tol=1e-15):
    return {m: c for m, c in p.items() if abs(c) > tol}

# Define variables
A2 = poly_var(0)  # a^2
C2 = poly_var(1)  # c^2
P = poly_var(2)   # p
Q = poly_var(3)   # q
R = poly_var(4)   # r
ONE = poly_const(1.0)
B2 = psub(ONE, A2)  # b^2 = 1 - a^2
X = padd(P, padd(pscale(Q, 2.0), R))  # X = p + 2q + r

# Goal: G = (b2-c2)*p*X + a2*c2 - a2*b2*X^2
G = padd(pmul(psub(B2, C2), pmul(P, X)),
         psub(pmul(A2, C2), pmul(A2, pmul(B2, psq(X)))))
G = clean(G)

# Constraint polynomials (all >= 0)
V1 = psub(pmul(padd(A2, P), padd(C2, R)), psq(Q))  # (a2+p)(c2+r) - q^2
V2 = psub(pmul(psub(A2, P), psub(C2, R)), psq(Q))  # (a2-p)(c2-r) - q^2
sum_CS = psub(padd(pmul(A2, C2), pmul(P, R)), psq(Q))  # a2*c2 + p*r - q^2
weighted_CS = psub(pmul(C2, psub(psq(A2), psq(P))), pmul(A2, psq(Q)))  # c2*(a2^2-p^2) - a2*q^2

# Sign constraints (all >= 0)
sgn_p = P  # p >= 0
sgn_X = X  # X >= 0
sgn_ap = padd(A2, P)  # a2+p >= 0
sgn_am = psub(A2, P)  # a2-p >= 0
sgn_cr = padd(C2, R)  # c2+r >= 0
sgn_cm = psub(C2, R)  # c2-r >= 0
sgn_bc = psub(B2, C2)  # b2-c2 >= 0

# Build nonneg terms: products of constraints × sign constraints × squares
# Level 0: basic constraints and squares
# Level 1: constraint × sign
# Level 2: constraint × constraint, constraint × sign × sign

terms = {}

# Basic constraints
terms["V1"] = V1
terms["V2"] = V2
terms["sum_CS"] = sum_CS
terms["weighted_CS"] = weighted_CS

# Squares of simple expressions
for name, expr in [("p", P), ("q", Q), ("r", R), ("X", X),
                   ("p-r", psub(P, R)), ("p+r", padd(P, R)),
                   ("2a2-1", psub(pscale(A2, 2), ONE)),
                   ("a2-p", psub(A2, P)), ("c2-r", psub(C2, R)),
                   ("a2*q", pmul(A2, Q)), ("c2*q", pmul(C2, Q)),
                   ("p*q", pmul(P, Q)), ("a2*r", pmul(A2, R)),
                   ("a2*c2", pmul(A2, C2))]:
    terms[f"sq({name})"] = psq(expr)

# Constraint × sign products (degree increases)
sign_terms = [("p", sgn_p), ("X", sgn_X), ("a2-p", sgn_am), ("a2+p", sgn_ap),
              ("c2-r", sgn_cm), ("c2+r", sgn_cr), ("b2-c2", sgn_bc)]
constraint_terms = [("V1", V1), ("V2", V2), ("sum_CS", sum_CS), ("w_CS", weighted_CS)]

for sn, sv in sign_terms:
    for cn, cv in constraint_terms:
        terms[f"{sn}*{cn}"] = pmul(sv, cv)

# sign × sign products
for i, (sn1, sv1) in enumerate(sign_terms):
    for sn2, sv2 in sign_terms[i:]:
        terms[f"{sn1}*{sn2}"] = pmul(sv1, sv2)

# Nonneg scaled terms: a2 * constraint, c2 * constraint, etc.
for cn, cv in constraint_terms:
    terms[f"a2*{cn}"] = pmul(A2, cv)
    terms[f"c2*{cn}"] = pmul(C2, cv)
    terms[f"a2^2*{cn}"] = pmul(psq(A2), cv)

# Sign × sign × constraint
for sn1, sv1 in sign_terms[:4]:  # p, X, a2-p, a2+p
    for sn2, sv2 in sign_terms[:4]:
        for cn, cv in constraint_terms[:2]:  # V1, V2
            key = f"{sn1}*{sn2}*{cn}"
            if key not in terms:
                terms[key] = pmul(sv1, pmul(sv2, cv))

# Collect all monomials
all_monomials = set()
for m in G: all_monomials.add(m)
for name, poly in terms.items():
    for m in poly: all_monomials.add(m)

monomials = sorted(all_monomials)
mono_idx = {m: i for i, m in enumerate(monomials)}
n_mono = len(monomials)

def mono_str(m):
    names = ["a2", "c2", "p", "q", "r"]
    parts = []
    for i, e in enumerate(m):
        if e == 1: parts.append(names[i])
        elif e > 1: parts.append(f"{names[i]}^{e}")
    return "*".join(parts) if parts else "1"

# Verify nonnegativity of all terms numerically
print("Verifying nonnegativity of terms...")
np.random.seed(42)
neg_terms = set()
for _ in range(50000):
    a2 = np.random.uniform(0.01, 0.99)
    b2 = 1 - a2
    c2 = np.random.uniform(0, b2)
    p_val = np.random.uniform(0, a2)
    r_val = np.random.uniform(-c2, c2)

    # Satisfy CS constraints AND p>=0, X>=0
    q_max_p = np.sqrt(max(0, (a2+p_val)*(c2+r_val)))
    q_max_m = np.sqrt(max(0, (a2-p_val)*(c2-r_val)))
    q_max = min(q_max_p, q_max_m)
    if q_max < 1e-12: continue
    # Ensure X = p+2q+r >= 0: q >= -(p+r)/2
    q_lo = max(-q_max, -(p_val + r_val)/2)
    q_hi = q_max
    if q_lo > q_hi: continue
    q_val = np.random.uniform(q_lo, q_hi)

    vals = [a2, c2, p_val, q_val, r_val]

    for name, poly in terms.items():
        if name in neg_terms: continue
        v = 0.0
        for m, c in poly.items():
            mv = c
            for k, e in enumerate(m):
                if e > 0: mv *= vals[k] ** e
            v += mv
        if v < -1e-8:
            neg_terms.add(name)

if neg_terms:
    print(f"  Removing {len(neg_terms)} non-nonneg terms: {sorted(neg_terms)[:10]}...")
    for name in neg_terms:
        del terms[name]

term_names = list(terms.keys())
n_terms = len(term_names)
print(f"  {n_terms} nonneg terms, {n_mono} monomials")

# Build matrix
g_vec = np.zeros(n_mono)
for m, c in G.items():
    if m in mono_idx:
        g_vec[mono_idx[m]] = c

A_mat = np.zeros((n_mono, n_terms))
for j, name in enumerate(term_names):
    for m, c in terms[name].items():
        if m in mono_idx:
            A_mat[mono_idx[m], j] += c

# Phase 1: Exact match (A lam = g, lam >= 0)
print("\nPhase 1: Exact monomial matching...")
c_obj = np.ones(n_terms)
result = linprog(c_obj, A_eq=A_mat, b_eq=g_vec,
                 bounds=[(0, None)]*n_terms, method="highs")

if result.success:
    lam = result.x
    residual = A_mat @ lam - g_vec
    print(f"  SOLVED! Max residual: {np.max(np.abs(residual)):.2e}")
    active = [(term_names[i], lam[i]) for i in range(n_terms) if lam[i] > 1e-12]
    active.sort(key=lambda x: -x[1])
    print(f"\n  Certificate ({len(active)} terms):")
    for name, val in active:
        frac = Fraction(val).limit_denominator(1000)
        err = abs(val - float(frac))
        marker = " <-- inexact" if err > 1e-8 else ""
        print(f"    {val:16.12f} * {name:40s}  ~ {str(frac):>10s}{marker}")

    # Verify
    print("\n  Verifying at random points...")
    max_err = 0
    for _ in range(100000):
        a2 = np.random.uniform(0.01, 0.99)
        b2 = 1 - a2
        c2 = np.random.uniform(0, b2)
        p_val = np.random.uniform(0, a2)
        r_val = np.random.uniform(-c2, c2)
        q_max_p = np.sqrt(max(0, (a2+p_val)*(c2+r_val)))
        q_max_m = np.sqrt(max(0, (a2-p_val)*(c2-r_val)))
        q_max = min(q_max_p, q_max_m)
        if q_max < 1e-12: continue
        q_val = np.random.uniform(-q_max, q_max)
        vals = [a2, c2, p_val, q_val, r_val]

        g_val = 0.0
        for m, c in G.items():
            mv = c
            for k, e in enumerate(m):
                if e > 0: mv *= vals[k] ** e
            g_val += mv

        approx = 0.0
        for i, (name, val) in enumerate(active):
            j = term_names.index(name)
            t_val = 0.0
            for m, c in terms[name].items():
                mv = c
                for k, e in enumerate(m):
                    if e > 0: mv *= vals[k] ** e
                t_val += mv
            approx += val * t_val

        max_err = max(max_err, abs(g_val - approx))

    print(f"  Max |G - cert|: {max_err:.2e}")
else:
    print(f"  Failed: {result.message}")

    # Phase 2: Inequality (overestimate)
    print("\nPhase 2: Inequality (A lam >= g)...")
    result2 = linprog(c_obj, A_ub=-A_mat, b_ub=-g_vec,
                      bounds=[(0, None)]*n_terms, method="highs")
    if result2.success:
        lam2 = result2.x
        slack = A_mat @ lam2 - g_vec
        print(f"  SOLVED! Slack range: [{slack.min():.6e}, {slack.max():.6e}]")
        active2 = [(term_names[i], lam2[i]) for i in range(n_terms) if lam2[i] > 1e-12]
        active2.sort(key=lambda x: -x[1])
        print(f"\n  Overestimate ({len(active2)} terms):")
        for name, val in active2[:20]:
            print(f"    {val:16.12f} * {name}")

        # Show which monomials have slack
        slack_mono = [(monomials[i], slack[i]) for i in range(n_mono) if abs(slack[i]) > 1e-10]
        if slack_mono:
            print(f"\n  Slack monomials:")
            for m, s in sorted(slack_mono, key=lambda x: -abs(x[1])):
                print(f"    {s:+12.8f} * {mono_str(m)}")
    else:
        print(f"  Failed: {result2.message}")

print("\nDone.")
