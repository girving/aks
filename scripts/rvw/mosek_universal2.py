"""
Universal SOS certificate for RVW inequality via MOSEK — higher degrees.

5 variables: A, C, p, q, r (where B = 1-A).
Tries sos_deg = 4 (degree 8), 5 (degree 10).
"""
import cvxpy as cp
import numpy as np
import sys
import time


def monomial_list_5(max_deg):
    """Monomials (a, c, i, j, k) for A^a C^c p^i q^j r^k, total deg <= max_deg."""
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


def find_universal_certificate(sos_deg=4, verbose=False):
    total_deg = 2 * sos_deg
    monos = monomial_list_5(total_deg)
    n_mono = len(monos)
    mono_idx = {m: i for i, m in enumerate(monos)}

    print(f"Total monomials (degree {total_deg}, 5 vars): {n_mono}")

    Z = (0, 0, 0, 0, 0)

    A_p = {(1,0,0,0,0): 1}
    C_p = {(0,1,0,0,0): 1}
    p_p = {(0,0,1,0,0): 1}
    q_p = {(0,0,0,1,0): 1}
    r_p = {(0,0,0,0,1): 1}
    B_p = {Z: 1, (1,0,0,0,0): -1}
    X_p = {(0,0,1,0,0): 1, (0,0,0,1,0): 2, (0,0,0,0,1): 1}
    BmC_p = {Z: 1, (1,0,0,0,0): -1, (0,1,0,0,0): -1}

    AC = mul_p(A_p, C_p)
    pX = mul_p(p_p, X_p)
    BmC_pX = mul_p(BmC_p, pX)
    AB = mul_p(A_p, B_p)
    X2 = mul_p(X_p, X_p)
    AB_X2 = mul_p(AB, X2)

    G_poly = {}
    for d in [AC, BmC_pX]:
        for m, c in d.items():
            G_poly[m] = G_poly.get(m, 0) + c
    for m, c in AB_X2.items():
        G_poly[m] = G_poly.get(m, 0) - c

    G_vec = np.zeros(n_mono)
    for m, c in G_poly.items():
        if m in mono_idx:
            G_vec[mono_idx[m]] = c

    # Constraints
    constraints = {}
    constraints['p'] = dict(p_p)
    constraints['A-p'] = {(1,0,0,0,0): 1, (0,0,1,0,0): -1}
    constraints['C+r'] = {(0,1,0,0,0): 1, (0,0,0,0,1): 1}
    constraints['C-r'] = {(0,1,0,0,0): 1, (0,0,0,0,1): -1}
    constraints['X'] = dict(X_p)
    constraints['A'] = dict(A_p)
    constraints['1-A'] = dict(B_p)
    constraints['1-A-C'] = dict(BmC_p)
    constraints['C'] = dict(C_p)

    cs_plus = mul_p({(1,0,0,0,0): 1, (0,0,1,0,0): 1},
                    {(0,1,0,0,0): 1, (0,0,0,0,1): 1})
    cs_plus[(0,0,0,2,0)] = cs_plus.get((0,0,0,2,0), 0) - 1
    constraints['CS+'] = cs_plus

    cs_minus = mul_p({(1,0,0,0,0): 1, (0,0,1,0,0): -1},
                     {(0,1,0,0,0): 1, (0,0,0,0,1): -1})
    cs_minus[(0,0,0,2,0)] = cs_minus.get((0,0,0,2,0), 0) - 1
    constraints['CS-'] = cs_minus

    # Also add derived constraints that might help
    # q^2 <= AC + pr (sum of CS)
    sum_cs = mul_p(A_p, C_p)
    sum_cs_pr = mul_p(p_p, r_p)
    for m, c in sum_cs_pr.items():
        sum_cs[m] = sum_cs.get(m, 0) + c
    sum_cs[(0,0,0,2,0)] = sum_cs.get((0,0,0,2,0), 0) - 1
    constraints['sumCS'] = sum_cs  # AC + pr - q^2 >= 0

    constraint_degs = {name: max(sum(m) for m in poly.keys()) if poly else 0
                       for name, poly in constraints.items()}

    print(f"Constraints: {len(constraints)}")
    for name in constraints:
        print(f"  {name}: degree {constraint_degs[name]}")

    basis_0 = monomial_list_5(sos_deg)
    n_basis_0 = len(basis_0)
    print(f"\nSOS basis sigma_0: {n_basis_0} monomials (degree {sos_deg})")
    Q0 = cp.Variable((n_basis_0, n_basis_0), symmetric=True)

    sos_mults = {}
    total_psd_vars = n_basis_0 * (n_basis_0 + 1) // 2
    for name, poly in constraints.items():
        cdeg = constraint_degs[name]
        mult_deg = (total_deg - cdeg) // 2
        if mult_deg < 0:
            continue
        basis_i = monomial_list_5(mult_deg)
        n_basis_i = len(basis_i)
        Qi = cp.Variable((n_basis_i, n_basis_i), symmetric=True)
        sos_mults[name] = (Qi, basis_i, poly)
        total_psd_vars += n_basis_i * (n_basis_i + 1) // 2
        print(f"  sigma_{name}: {n_basis_i}x{n_basis_i} (mult degree {mult_deg})")

    print(f"\nTotal PSD variables: {total_psd_vars}")
    print(f"Equality constraints: {n_mono}")

    # Build certificate
    cert_expr = {}

    print("Building sigma_0 terms...", end="", flush=True)
    t0 = time.time()
    for bi, bm1 in enumerate(basis_0):
        for bj in range(bi, n_basis_0):
            bm2 = basis_0[bj]
            m = tuple(a + b for a, b in zip(bm1, bm2))
            if m in mono_idx:
                if m not in cert_expr:
                    cert_expr[m] = 0
                if bi == bj:
                    cert_expr[m] = cert_expr[m] + Q0[bi, bj]
                else:
                    cert_expr[m] = cert_expr[m] + 2 * Q0[bi, bj]
    print(f" {time.time()-t0:.1f}s")

    print("Building constraint terms...", end="", flush=True)
    t0 = time.time()
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
                        if bi == bj:
                            cert_expr[m] = cert_expr[m] + Qi[bi, bj] * gc
                        else:
                            cert_expr[m] = cert_expr[m] + 2 * Qi[bi, bj] * gc
    print(f" {time.time()-t0:.1f}s")

    eq_constraints = [Q0 >> 0]
    for name, (Qi, _, _) in sos_mults.items():
        eq_constraints.append(Qi >> 0)

    for m_idx in range(n_mono):
        m = monos[m_idx]
        lhs = cert_expr.get(m, 0)
        rhs = G_vec[m_idx]
        eq_constraints.append(lhs == rhs)

    prob = cp.Problem(cp.Minimize(0), eq_constraints)

    print(f"\nSolving with MOSEK...")
    t0 = time.time()
    try:
        prob.solve(solver=cp.MOSEK, verbose=verbose,
                   mosek_params={
                       'MSK_DPAR_INTPNT_CO_TOL_PFEAS': 1e-8,
                       'MSK_DPAR_INTPNT_CO_TOL_DFEAS': 1e-8,
                       'MSK_DPAR_INTPNT_CO_TOL_REL_GAP': 1e-8,
                       'MSK_IPAR_INTPNT_MAX_ITERATIONS': 400,
                   })
    except Exception as e:
        print(f"Solver error: {e}")
        return None
    elapsed = time.time() - t0
    print(f"Status: {prob.status} ({elapsed:.1f}s)")

    if prob.status in ['optimal', 'optimal_inaccurate']:
        result = {'Q0': Q0.value, 'basis_0': basis_0}
        for name, (Qi, basis_i, _) in sos_mults.items():
            result[f'Q_{name}'] = Qi.value
            result[f'basis_{name}'] = basis_i
        return result
    return None


def analyze_result(result):
    Q0 = result['Q0']
    eigs = np.linalg.eigvalsh(Q0)
    print(f"\nQ0: {Q0.shape[0]}x{Q0.shape[0]}, min_eig={eigs[0]:.6e}, "
          f"rank={np.sum(eigs > 1e-8)}, max_eig={eigs[-1]:.6e}")

    for key in sorted(result.keys()):
        if key.startswith('Q_'):
            Qi = result[key]
            eigs_i = np.linalg.eigvalsh(Qi)
            r = np.sum(eigs_i > 1e-8)
            print(f"{key}: {Qi.shape[0]}x{Qi.shape[0]}, min_eig={eigs_i[0]:.6e}, "
                  f"rank={r}, trace={np.trace(Qi):.6e}")


# Main
print("Universal RVW SOS Certificate (higher degrees)")
print("=" * 60)

for sos_deg in [4]:
    print(f"\n{'='*60}")
    print(f"SOS degree = {sos_deg} (certificate degree = {2*sos_deg})")
    print(f"{'='*60}")

    result = find_universal_certificate(sos_deg=sos_deg, verbose=False)
    if result is not None:
        print("\n*** FEASIBLE ***")
        analyze_result(result)
    else:
        print("\n*** INFEASIBLE ***")
