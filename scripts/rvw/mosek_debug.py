"""Debug the degree-8 universal SOS - run with verbose to see MOSEK error."""
import cvxpy as cp
import numpy as np
import time


def monomial_list_5(max_deg):
    monos = []
    for d in range(max_deg + 1):
        for a in range(d + 1):
            for c in range(d - a + 1):
                for i in range(d - a - c + 1):
                    for j in range(d - a - c - i + 1):
                        k = d - a - c - i - j
                        monos.append((a, c, i, j, k))
    return monos


def mul_p(p1, p2):
    r = {}
    for m1, c1 in p1.items():
        for m2, c2 in p2.items():
            m = tuple(x + y for x, y in zip(m1, m2))
            r[m] = r.get(m, 0) + c1 * c2
    return r


sos_deg = 4
total_deg = 2 * sos_deg
monos = monomial_list_5(total_deg)
n_mono = len(monos)
mono_idx = {m: i for i, m in enumerate(monos)}

print(f"Monomials: {n_mono}, SOS basis: {len(monomial_list_5(sos_deg))}")

Z = (0,0,0,0,0)
A_p = {(1,0,0,0,0): 1}
C_p = {(0,1,0,0,0): 1}
p_p = {(0,0,1,0,0): 1}
r_p = {(0,0,0,0,1): 1}
B_p = {Z: 1, (1,0,0,0,0): -1}
X_p = {(0,0,1,0,0): 1, (0,0,0,1,0): 2, (0,0,0,0,1): 1}
BmC_p = {Z: 1, (1,0,0,0,0): -1, (0,1,0,0,0): -1}

G_poly = {}
for m, c in mul_p(A_p, C_p).items():
    G_poly[m] = G_poly.get(m, 0) + c
for m, c in mul_p(BmC_p, mul_p(p_p, X_p)).items():
    G_poly[m] = G_poly.get(m, 0) + c
for m, c in mul_p(mul_p(A_p, B_p), mul_p(X_p, X_p)).items():
    G_poly[m] = G_poly.get(m, 0) - c

G_vec = np.zeros(n_mono)
for m, c in G_poly.items():
    if m in mono_idx:
        G_vec[mono_idx[m]] = c

# Fewer constraints - just the essential ones
constraints = {
    'p': {(0,0,1,0,0): 1},
    'A-p': {(1,0,0,0,0): 1, (0,0,1,0,0): -1},
    'C+r': {(0,1,0,0,0): 1, (0,0,0,0,1): 1},
    'C-r': {(0,1,0,0,0): 1, (0,0,0,0,1): -1},
    'X': dict(X_p),
    'A': {(1,0,0,0,0): 1},
    '1-A': dict(B_p),
    '1-A-C': dict(BmC_p),
    'C': {(0,1,0,0,0): 1},
}

cs_plus = mul_p({(1,0,0,0,0): 1, (0,0,1,0,0): 1},
                {(0,1,0,0,0): 1, (0,0,0,0,1): 1})
cs_plus[(0,0,0,2,0)] = cs_plus.get((0,0,0,2,0), 0) - 1
constraints['CS+'] = cs_plus

cs_minus = mul_p({(1,0,0,0,0): 1, (0,0,1,0,0): -1},
                 {(0,1,0,0,0): 1, (0,0,0,0,1): -1})
cs_minus[(0,0,0,2,0)] = cs_minus.get((0,0,0,2,0), 0) - 1
constraints['CS-'] = cs_minus

constraint_degs = {name: max(sum(m) for m in poly.keys())
                   for name, poly in constraints.items()}

basis_0 = monomial_list_5(sos_deg)
n_basis_0 = len(basis_0)
Q0 = cp.Variable((n_basis_0, n_basis_0), symmetric=True)

sos_mults = {}
for name, poly in constraints.items():
    cdeg = constraint_degs[name]
    mult_deg = (total_deg - cdeg) // 2
    if mult_deg < 0:
        continue
    basis_i = monomial_list_5(mult_deg)
    n_basis_i = len(basis_i)
    Qi = cp.Variable((n_basis_i, n_basis_i), symmetric=True)
    sos_mults[name] = (Qi, basis_i, poly)

print(f"Building certificate ({len(sos_mults)} constraint multipliers)...")

cert_expr = {}
for bi, bm1 in enumerate(basis_0):
    for bj in range(bi, n_basis_0):
        bm2 = basis_0[bj]
        m = tuple(a + b for a, b in zip(bm1, bm2))
        if m in mono_idx:
            if m not in cert_expr:
                cert_expr[m] = 0
            w = 1 if bi == bj else 2
            cert_expr[m] = cert_expr[m] + w * Q0[bi, bj]

for name, (Qi, basis_i, gpoly) in sos_mults.items():
    n_bi = len(basis_i)
    for bi, bm1 in enumerate(basis_i):
        for bj in range(bi, n_bi):
            bm2 = basis_i[bj]
            mm = tuple(a + b for a, b in zip(bm1, bm2))
            for gm, gc in gpoly.items():
                m = tuple(a + b for a, b in zip(mm, gm))
                if m in mono_idx:
                    if m not in cert_expr:
                        cert_expr[m] = 0
                    w = 1 if bi == bj else 2
                    cert_expr[m] = cert_expr[m] + w * Qi[bi, bj] * gc

eq_constraints = [Q0 >> 0]
for name, (Qi, _, _) in sos_mults.items():
    eq_constraints.append(Qi >> 0)

for m_idx in range(n_mono):
    m = monos[m_idx]
    lhs = cert_expr.get(m, 0)
    rhs = G_vec[m_idx]
    eq_constraints.append(lhs == rhs)

prob = cp.Problem(cp.Minimize(0), eq_constraints)

print("Solving with MOSEK (verbose)...")
t0 = time.time()
try:
    prob.solve(solver=cp.MOSEK, verbose=True,
               mosek_params={
                   'MSK_DPAR_INTPNT_CO_TOL_PFEAS': 1e-7,
                   'MSK_DPAR_INTPNT_CO_TOL_DFEAS': 1e-7,
                   'MSK_DPAR_INTPNT_CO_TOL_REL_GAP': 1e-7,
                   'MSK_IPAR_INTPNT_MAX_ITERATIONS': 400,
               })
    print(f"\nStatus: {prob.status} ({time.time()-t0:.1f}s)")
except cp.SolverError as e:
    print(f"\nSolver error: {e}")
    print(f"Time: {time.time()-t0:.1f}s")
except Exception as e:
    print(f"\nOther error: {type(e).__name__}: {e}")
    print(f"Time: {time.time()-t0:.1f}s")
