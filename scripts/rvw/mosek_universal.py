"""
Universal SOS certificate for RVW inequality via MOSEK.

5 variables: A, C, p, q, r (where B = 1-A).
Case: p >= 0, X = p+2q+r >= 0 (WLOG by symmetry).

G = AC + (B-C)*p*X - A*B*X^2  where B = 1-A, X = p+2q+r.

Constraints (all >= 0):
  g1:  p                          (degree 1)
  g2:  A - p                      (degree 1)
  g3:  C + r                      (degree 1)
  g4:  C - r                      (degree 1)
  g5:  X = p + 2q + r             (degree 1)
  g6:  A                          (degree 1)
  g7:  1 - A                      (degree 1)
  g8:  1 - A - C   (B >= C)       (degree 1)
  g9:  C                          (degree 1)
  g10: (A+p)(C+r) - q^2   [CS+]  (degree 2)
  g11: (A-p)(C-r) - q^2   [CS-]  (degree 2)

Putinar certificate: G = sigma_0 + sum_i sigma_i * g_i
where sigma_j are SOS polynomials (v^T Q_j v with Q_j >= 0).
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
    """Multiply two polynomial dicts {exponent_tuple: coeff}."""
    r = {}
    for m1, c1 in p1.items():
        for m2, c2 in p2.items():
            m = tuple(x + y for x, y in zip(m1, m2))
            r[m] = r.get(m, 0) + c1 * c2
    return r


def find_universal_certificate(sos_deg=3, verbose=False):
    """Find universal SOS certificate for G >= 0 in 5 variables."""
    total_deg = 2 * sos_deg
    monos = monomial_list_5(total_deg)
    n_mono = len(monos)
    mono_idx = {m: i for i, m in enumerate(monos)}

    print(f"Total monomials (degree {total_deg}, 5 vars): {n_mono}")

    # Polynomial building blocks
    Z = (0, 0, 0, 0, 0)  # zero exponent

    # G = AC + (1-A-C)*p*(p+2q+r) - A*(1-A)*(p+2q+r)^2
    # Build symbolically
    def var(idx, coeff=1):
        e = [0, 0, 0, 0, 0]
        e[idx] = 1
        return {tuple(e): coeff}

    A_p = var(0)       # A
    C_p = var(1)       # C
    p_p = var(2)       # p
    q_p = var(3)       # q
    r_p = var(4)       # r
    one_p = {Z: 1}

    # B = 1 - A
    B_p = {Z: 1, (1,0,0,0,0): -1}
    # X = p + 2q + r
    X_p = {(0,0,1,0,0): 1, (0,0,0,1,0): 2, (0,0,0,0,1): 1}
    # B - C = 1 - A - C
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
        elif abs(c) > 1e-15:
            print(f"WARNING: G has monomial {m} (degree {sum(m)}) outside range!")

    # Constraint polynomials
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

    # CS+: (A+p)(C+r) - q^2
    cs_plus = mul_p({(1,0,0,0,0): 1, (0,0,1,0,0): 1},
                    {(0,1,0,0,0): 1, (0,0,0,0,1): 1})
    cs_plus[(0,0,0,2,0)] = cs_plus.get((0,0,0,2,0), 0) - 1
    constraints['CS+'] = cs_plus

    # CS-: (A-p)(C-r) - q^2
    cs_minus = mul_p({(1,0,0,0,0): 1, (0,0,1,0,0): -1},
                     {(0,1,0,0,0): 1, (0,0,0,0,1): -1})
    cs_minus[(0,0,0,2,0)] = cs_minus.get((0,0,0,2,0), 0) - 1
    constraints['CS-'] = cs_minus

    constraint_degs = {name: max(sum(m) for m in poly.keys()) if poly else 0
                       for name, poly in constraints.items()}

    print(f"Constraints: {len(constraints)}")
    for name in constraints:
        print(f"  {name}: degree {constraint_degs[name]}")

    # SOS basis for sigma_0
    basis_0 = monomial_list_5(sos_deg)
    n_basis_0 = len(basis_0)
    print(f"\nSOS basis sigma_0: {n_basis_0} monomials (degree {sos_deg})")
    Q0 = cp.Variable((n_basis_0, n_basis_0), symmetric=True)

    # SOS multipliers
    sos_mults = {}
    total_psd_vars = n_basis_0 * (n_basis_0 + 1) // 2
    for name, poly in constraints.items():
        cdeg = constraint_degs[name]
        mult_deg = (total_deg - cdeg) // 2
        if mult_deg < 0:
            print(f"  SKIP {name}: mult_deg would be {mult_deg}")
            continue
        basis_i = monomial_list_5(mult_deg)
        n_basis_i = len(basis_i)
        Qi = cp.Variable((n_basis_i, n_basis_i), symmetric=True)
        sos_mults[name] = (Qi, basis_i, poly)
        total_psd_vars += n_basis_i * (n_basis_i + 1) // 2
        print(f"  sigma_{name}: {n_basis_i}x{n_basis_i} (mult degree {mult_deg})")

    print(f"\nTotal PSD variables: {total_psd_vars}")
    print(f"Equality constraints: {n_mono}")

    # Build certificate expression for each monomial
    cert_expr = {}

    # sigma_0: v0^T Q0 v0
    print("Building sigma_0 terms...", end="", flush=True)
    t0 = time.time()
    for bi, bm1 in enumerate(basis_0):
        for bj, bm2 in enumerate(basis_0):
            if bj < bi:
                continue  # use symmetry: Q[i,j] = Q[j,i]
            m = tuple(a + b for a, b in zip(bm1, bm2))
            if m in mono_idx:
                if m not in cert_expr:
                    cert_expr[m] = 0
                if bi == bj:
                    cert_expr[m] = cert_expr[m] + Q0[bi, bj]
                else:
                    cert_expr[m] = cert_expr[m] + 2 * Q0[bi, bj]
    print(f" {time.time()-t0:.1f}s")

    # sigma_i * g_i
    print("Building constraint terms...", end="", flush=True)
    t0 = time.time()
    for name, (Qi, basis_i, gpoly) in sos_mults.items():
        for bi, bm1 in enumerate(basis_i):
            for bj, bm2 in enumerate(basis_i):
                if bj < bi:
                    continue
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

    # Equality constraints + PSD
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
                       'MSK_DPAR_INTPNT_CO_TOL_PFEAS': 1e-9,
                       'MSK_DPAR_INTPNT_CO_TOL_DFEAS': 1e-9,
                       'MSK_DPAR_INTPNT_CO_TOL_REL_GAP': 1e-9,
                       'MSK_IPAR_INTPNT_MAX_ITERATIONS': 200,
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
    """Analyze and display certificate structure."""
    Q0 = result['Q0']
    eigs = np.linalg.eigvalsh(Q0)
    print(f"\nQ0: {Q0.shape[0]}x{Q0.shape[0]}, min_eig={eigs[0]:.6e}, "
          f"rank={np.sum(eigs > 1e-8)}, max_eig={eigs[-1]:.6e}")

    for key in sorted(result.keys()):
        if key.startswith('Q_'):
            name = key[2:]
            Qi = result[key]
            eigs_i = np.linalg.eigvalsh(Qi)
            r = np.sum(eigs_i > 1e-8)
            print(f"Q_{name}: {Qi.shape[0]}x{Qi.shape[0]}, min_eig={eigs_i[0]:.6e}, "
                  f"rank={r}, trace={np.trace(Qi):.6e}")


def verify_universal(result, n_test=500000):
    """Verify numerically at random (A,C,p,q,r) points."""
    import random
    random.seed(42)
    np.random.seed(42)

    basis_0 = result['basis_0']
    Q0 = result['Q0']

    max_err = 0
    max_neg = 0
    n_tested = 0

    for trial in range(n_test):
        Av = random.uniform(0.01, 0.99)
        Bv = 1 - Av
        Cv = random.uniform(0.01, Bv - 0.001)
        pv = random.uniform(0, Av)
        rv = random.uniform(-Cv, Cv)

        q_max_p = np.sqrt(max(0, (Av + pv) * (Cv + rv)))
        q_max_m = np.sqrt(max(0, (Av - pv) * (Cv - rv)))
        q_max = min(q_max_p, q_max_m)
        if q_max <= 0:
            continue
        qv = random.uniform(-q_max, q_max)
        Xv = pv + 2 * qv + rv
        if Xv < 0:
            continue

        n_tested += 1
        Gv = Av * Cv + (Bv - Cv) * pv * Xv - Av * Bv * Xv ** 2

        # Evaluate monomial vector for sigma_0
        def mono_val(m):
            return Av**m[0] * Cv**m[1] * pv**m[2] * qv**m[3] * rv**m[4]

        v0 = np.array([mono_val(m) for m in basis_0])
        cert_val = v0 @ Q0 @ v0

        for key in sorted(result.keys()):
            if not key.startswith('Q_'):
                continue
            name = key[2:]
            Qi = result[key]
            basis_i = result[f'basis_{name}']
            vi = np.array([mono_val(m) for m in basis_i])
            sigma_val = vi @ Qi @ vi

            if name == 'p':
                gval = pv
            elif name == 'A-p':
                gval = Av - pv
            elif name == 'C+r':
                gval = Cv + rv
            elif name == 'C-r':
                gval = Cv - rv
            elif name == 'X':
                gval = Xv
            elif name == 'A':
                gval = Av
            elif name == '1-A':
                gval = Bv
            elif name == '1-A-C':
                gval = Bv - Cv
            elif name == 'C':
                gval = Cv
            elif name == 'CS+':
                gval = (Av + pv) * (Cv + rv) - qv ** 2
            elif name == 'CS-':
                gval = (Av - pv) * (Cv - rv) - qv ** 2
            else:
                gval = 0

            cert_val += sigma_val * gval

        err = abs(cert_val - Gv)
        max_err = max(max_err, err)
        if Gv < 0:
            max_neg = min(max_neg, Gv)

    print(f"\nVerification ({n_tested} points tested):")
    print(f"  Max reconstruction error: {max_err:.6e}")
    print(f"  Most negative G value: {max_neg:.6e}")
    return max_err < 1e-3


# Main
print("Universal RVW SOS Certificate (5 variables: A, C, p, q, r)")
print("Case: p >= 0, X = p+2q+r >= 0")
print("=" * 60)

for sos_deg in [2, 3]:
    print(f"\n{'='*60}")
    print(f"SOS degree = {sos_deg} (certificate degree = {2*sos_deg})")
    print(f"{'='*60}")

    result = find_universal_certificate(sos_deg=sos_deg, verbose=False)
    if result is not None:
        print("\n*** FEASIBLE ***")
        analyze_result(result)
        verify_universal(result)
    else:
        print("\n*** INFEASIBLE ***")
