"""Compute vertex inequalities for rvw_quadratic_ineq and find nlinarith hints.

After concavity reduction in (q,r), the proof reduces to checking
G ≥ 0 at four vertices of the (q,r) feasible set.

Variables: A = a², B = 1-A, C = c², p with 0 ≤ p ≤ A, 0 ≤ C ≤ B.

Vertex 1: q=0, r=C   → X = p+C, |X| = p+C (since p,C ≥ 0)
Vertex 2: q=0, r=-C  → X = p-C, |X| = |p-C|
  Case 2a: p ≥ C  → |X| = p-C
  Case 2b: p < C  → |X| = C-p
Vertex 3±: both CS tight → r = -pC/A, q = ±√(C(A²-p²)/A)
"""

import sympy as sp
import numpy as np
from scipy.optimize import linprog

A, B, C, p = sp.symbols('A B C p', nonneg=True)
B_val = 1 - A  # B = 1-A

def expand_sub_B(expr):
    return sp.expand(expr.subs(B, B_val))

# =====================================================
# Vertex 1: q=0, r=C, X=p+C
# G = AC + (B-C)*p*(p+C) - AB*(p+C)²
# =====================================================
G1 = expand_sub_B(A*C + (B-C)*p*(p+C) - A*B*(p+C)**2)
print("=== Vertex 1: q=0, r=C, X=p+C ===")
print(f"G1 = {G1}")
print(f"G1 simplified = {sp.collect(G1, [A, C, p])}")

# =====================================================
# Vertex 2a: q=0, r=-C, p≥C, X=p-C, |X|=p-C
# G = AC + (B-C)*p*(p-C) - AB*(p-C)²
# =====================================================
G2a = expand_sub_B(A*C + (B-C)*p*(p-C) - A*B*(p-C)**2)
print("\n=== Vertex 2a: q=0, r=-C, p≥C ===")
print(f"G2a = {G2a}")

# =====================================================
# Vertex 2b: q=0, r=-C, p<C, X=C-p, |X|=C-p
# G = AC + (B-C)*p*(C-p) - AB*(C-p)²
# =====================================================
G2b = expand_sub_B(A*C + (B-C)*p*(C-p) - A*B*(C-p)**2)
print("\n=== Vertex 2b: q=0, r=-C, p<C ===")
print(f"G2b = {G2b}")

# =====================================================
# Vertex 3: both CS tight
# r = -pC/A, q² = C(A²-p²)/A
# X = p + 2q + r = p(A-C)/A + 2q
# G = AC + (B-C)*p*|X| - AB*X²
#
# Let's compute G at this vertex. Set u = p(A-C)/A (center X value).
# X = u + 2q.  G(q) = AC + (B-C)*p*|u+2q| - AB*(u+2q)²
#
# When X ≥ 0: G = AC + (B-C)*p*(u+2q) - AB*(u+2q)² = R + S*q
# where R = AC + (B-C)*p*u - AB*u² - 4*AB*q²  (using q² = C(A²-p²)/A)
#   and S = 2*(B-C)*p - 4*AB*u
#
# More precisely, expanding X = u + 2q, X² = u² + 4uq + 4q²:
# G = AC + (B-C)*p*u + 2*(B-C)*p*q - AB*u² - 4*AB*u*q - 4*AB*q²
#   = [AC + (B-C)*p*u - AB*u² - 4*AB*q²] + [2*(B-C)*p - 4*AB*u]*q
#   = R + S*q
# =====================================================

# Compute R and S symbolically
u = p*(A-C)/A  # Center X when q=0 at the CS vertex
Q2 = C*(A**2 - p**2)/A  # q² at both CS tight

# R = AC + (B-C)*p*u - AB*u² - 4*AB*Q2
R_raw = A*C + (B-C)*p*u - A*B*u**2 - 4*A*B*Q2

# S = 2*(B-C)*p - 4*AB*u
S_raw = 2*(B-C)*p - 4*A*B*u

# Multiply through by A to clear denominators
# A*R = A²C + (B-C)*p²*(A-C) - B*p²*(A-C)² - 4A²B*C*(A²-p²)/A
# Actually let's multiply R by A² to fully clear:
# A²*R = A²*[AC + (B-C)*p*(p(A-C)/A) - AB*(p(A-C)/A)² - 4AB*C*(A²-p²)/A]
#       = A³C + A*(B-C)*p²*(A-C) - B*p²*(A-C)² - 4A²BC*(A-p)*(A+p)/A
# Hmm still messy. Let's just expand symbolically.

R_sub = expand_sub_B(R_raw)
S_sub = expand_sub_B(S_raw)
print("\n=== Vertex 3: both CS tight ===")
print(f"R (with 1/A) = {R_sub}")
print(f"S = {S_sub}")

# Clear denominators: multiply R by A
AR = sp.expand(R_sub * A)
print(f"\nA*R = {AR}")
poly_AR = sp.Poly(AR, A, C, p)
print(f"  Degree: {poly_AR.total_degree()}, Terms: {len(poly_AR.as_dict())}")

# Check: S is already polynomial
print(f"\nS = {S_sub}")
poly_S = sp.Poly(S_sub, A, C, p)
print(f"  Degree: {poly_S.total_degree()}, Terms: {len(poly_S.as_dict())}")

# For vertex 3, G = R + S*q where q = ±√Q2
# G ≥ 0 iff R ≥ |S|*√Q2 (when R ≥ 0)
# Equivalently: A*R ≥ 0 AND (A*R)² ≥ S²*A*Q2 = S²*C*(A²-p²)

# Check A*R ≥ 0
print("\n--- Checking A*R ≥ 0 ---")
for (a, c, pp) in [(0.5, 0.5, 0.5), (0.5, 0.2, 0.3), (0.9, 0.05, 0.1),
                    (0.3, 0.1, 0.2), (0.1, 0.05, 0.05), (0.8, 0.1, 0.7),
                    (0.01, 0.001, 0.005), (0.99, 0.005, 0.5)]:
    if pp <= a and c <= 1 - a:
        val = float(AR.subs([(A, a), (C, c), (p, pp)]))
        print(f"  A={a}, C={c}, p={pp}: A*R = {val:.8f}")

# Compute (A*R)² - S²*C*(A²-p²) = A²*R² - S²*C*(A²-p²)
# This should be ≥ 0
D = sp.expand(AR**2 - S_sub**2 * C * (A**2 - p**2))
print(f"\n(AR)² - S²C(A²-p²) = {D}")
poly_D = sp.Poly(D, A, C, p)
print(f"  Degree: {poly_D.total_degree()}, Terms: {len(poly_D.as_dict())}")

print("\n--- Checking D ≥ 0 ---")
for (a, c, pp) in [(0.5, 0.5, 0.5), (0.5, 0.2, 0.3), (0.9, 0.05, 0.1),
                    (0.3, 0.1, 0.2), (0.1, 0.05, 0.05), (0.8, 0.1, 0.7),
                    (0.01, 0.001, 0.005), (0.99, 0.005, 0.5)]:
    if pp <= a and c <= 1 - a:
        val = float(D.subs([(A, a), (C, c), (p, pp)]))
        print(f"  A={a}, C={c}, p={pp}: D = {val:.8f}")

print("\n\n========================================")
print("Now test LP feasibility for each vertex")
print("========================================")

def partitions(n, k):
    if k == 1:
        yield (n,)
        return
    for i in range(n + 1):
        for rest in partitions(n - i, k - 1):
            yield (i,) + rest

def test_lp_feasibility(G_sym, variables, constraints, max_deg, label):
    """Test if G = sum c_i * g_i * m_i² has a diagonal Positivstellensatz certificate."""
    from scipy.optimize import linprog

    G_poly = sp.Poly(sp.expand(G_sym), *variables)
    G_dict = {m: float(c) for m, c in G_poly.as_dict().items()}
    nvars = len(variables)

    all_monos = []
    for total in range(max_deg + 1):
        all_monos.extend(partitions(total, nvars))

    all_exps = set(G_dict.keys())
    lp_columns = []
    column_names = []

    for cname, cpoly_sym in constraints.items():
        c_poly = sp.Poly(sp.expand(cpoly_sym), *variables)
        c_dict = {m: float(c) for m, c in c_poly.as_dict().items()}
        c_deg = max(sum(e) for e in c_dict) if c_dict else 0

        for mono_exp in all_monos:
            mono_deg = sum(mono_exp)
            if c_deg + 2 * mono_deg > max_deg:
                continue
            mono_sq_exp = tuple(2 * a for a in mono_exp)
            prod = {}
            for ce, cc in c_dict.items():
                pe = tuple(a + b for a, b in zip(ce, mono_sq_exp))
                prod[pe] = prod.get(pe, 0) + cc
            all_exps.update(prod.keys())
            lp_columns.append(prod)
            column_names.append((cname, mono_exp))

    # Free SOS terms
    for mono_exp in all_monos:
        if 2 * sum(mono_exp) > max_deg:
            continue
        mono_sq_exp = tuple(2 * a for a in mono_exp)
        all_exps.add(mono_sq_exp)
        lp_columns.append({mono_sq_exp: 1.0})
        column_names.append(('1', mono_exp))

    all_exps = sorted(all_exps)
    exp_idx = {e: i for i, e in enumerate(all_exps)}
    n_cols = len(lp_columns)
    n_rows = len(all_exps)

    A_eq = np.zeros((n_rows, n_cols))
    b_eq = np.zeros(n_rows)

    for j, prod in enumerate(lp_columns):
        for e, c in prod.items():
            A_eq[exp_idx[e], j] += c

    for e, c in G_dict.items():
        b_eq[exp_idx[e]] = c

    result = linprog(
        c=np.zeros(n_cols),
        A_eq=A_eq, b_eq=b_eq,
        bounds=[(0, None)] * n_cols,
        method='highs',
        options={'presolve': True, 'dual_feasibility_tolerance': 1e-9}
    )

    if result.success and result.status == 0:
        print(f"  {label}: FEASIBLE at degree {max_deg}! ({n_cols} vars, {n_rows} eqs)")
        used = [(column_names[j], result.x[j])
                for j in range(n_cols) if result.x[j] > 1e-8]
        print(f"    {len(used)} nonzero terms:")
        for (cname, mono), coeff in sorted(used, key=lambda x: -x[1])[:15]:
            vnames = ['A', 'C', 'p']
            mono_str = '*'.join(f"{vnames[i]}^{e}" for i, e in enumerate(mono) if e > 0) or '1'
            print(f"      c={coeff:.10f}  g={cname:<15s}  m²=({mono_str})²")
        return True, result
    else:
        print(f"  {label}: INFEASIBLE at degree {max_deg} ({n_cols} vars, {n_rows} eqs)")
        return False, result


# Constraints for the 3-variable (A, C, p) problem
# A ∈ (0,1), B = 1-A > 0, C ∈ [0, B], p ∈ [0, A]
constraints_3var = {
    'A': A,
    'C': C,
    'p': p,
    '1-A': 1 - A,
    '1-A-C': 1 - A - C,  # B - C ≥ 0
    'A-p': A - p,
}

print("\n--- Vertex 1: G1 ≥ 0 ---")
for deg in [4, 6]:
    test_lp_feasibility(G1, [A, C, p], constraints_3var, deg, "G1")

print("\n--- Vertex 2a: G2a ≥ 0 (with p≥C) ---")
constraints_2a = {**constraints_3var, 'p-C': p - C}
for deg in [4, 6]:
    test_lp_feasibility(G2a, [A, C, p], constraints_2a, deg, "G2a")

print("\n--- Vertex 2b: G2b ≥ 0 (with C≥p) ---")
constraints_2b = {**constraints_3var, 'C-p': C - p}
for deg in [4, 6]:
    test_lp_feasibility(G2b, [A, C, p], constraints_2b, deg, "G2b")

print("\n--- Vertex 3: A*R ≥ 0 ---")
for deg in [4, 6]:
    test_lp_feasibility(AR, [A, C, p], constraints_3var, deg, "AR")

print("\n--- Vertex 3: D = (AR)² - S²C(A²-p²) ≥ 0 ---")
for deg in [6, 8, 10]:
    test_lp_feasibility(D, [A, C, p], constraints_3var, deg, "D")

# Also try factoring the vertex polynomials
print("\n\n========================================")
print("Attempting to factor vertex polynomials")
print("========================================")

print("\n--- G1 factored ---")
print(f"G1 = {sp.factor(G1)}")

print("\n--- G2a factored ---")
print(f"G2a = {sp.factor(G2a)}")

print("\n--- G2b factored ---")
print(f"G2b = {sp.factor(G2b)}")

print("\n--- AR factored ---")
print(f"AR = {sp.factor(AR)}")

print("\n--- D factored ---")
# D might be too complex for sympy.factor
try:
    print(f"D = {sp.factor(D)}")
except:
    print("(factoring failed)")

# Try to express G1 as combination of squares and constraint products
print("\n\n========================================")
print("Manual SOS decomposition attempts")
print("========================================")

# G1 = AC + (1-A-C)*p*(p+C) - A*(1-A)*(p+C)²
# Let's expand and group
print("\n--- G1 expansion ---")
G1_collected = sp.collect(sp.expand(G1), p)
print(f"G1 (collected in p) = {G1_collected}")

# Check: G1 at p=0
G1_p0 = G1.subs(p, 0)
print(f"G1(p=0) = {sp.expand(G1_p0)} = {sp.factor(G1_p0)}")

# Check: G1 at p=A
G1_pA = sp.expand(G1.subs(p, A))
print(f"G1(p=A) = {G1_pA} = {sp.factor(G1_pA)}")

# Check: G1 at C=0
G1_C0 = sp.expand(G1.subs(C, 0))
print(f"G1(C=0) = {G1_C0} = {sp.factor(G1_C0)}")

# Check: G1 at C=1-A
G1_CB = sp.expand(G1.subs(C, 1-A))
print(f"G1(C=B) = {G1_CB} = {sp.factor(G1_CB)}")
