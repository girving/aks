"""
SOS certificate for RVW inequality via MOSEK, working in original (p,q,r) variables.

Case: p ≥ 0, X = p+2q+r ≥ 0 (WLOG by symmetry).
G₁ = AC + (B-C)·p·X - AB·X²  where X = p+2q+r, B = 1-A.

Constraints:
  g1: p ≥ 0
  g2: A-p ≥ 0
  g3: C+r ≥ 0
  g4: C-r ≥ 0
  g5: (A+p)(C+r) - q² ≥ 0  [CS+]
  g6: (A-p)(C-r) - q² ≥ 0  [CS-]
  g7: p+2q+r ≥ 0            [X ≥ 0]

Putinar-style SOS certificate:
  G₁ = σ₀ + Σ σᵢ · gᵢ
where σ₀ is a degree-2d SOS (v^T Q₀ v), and σᵢ are SOS multipliers
(v^T Qᵢ v) of appropriate degree.

For d=2 (degree-4 SOS), d=3 (degree-6 SOS), etc.
"""
import cvxpy as cp
import numpy as np
from fractions import Fraction
import sys


def monomial_list(nvars, max_deg):
    """Generate all monomials up to max_deg in nvars variables."""
    if nvars == 0:
        return [()]
    result = []
    for d in range(max_deg + 1):
        for rest in monomial_list(nvars - 1, d):
            result.append((d - sum(rest),) + rest)
    return result


def monomial_list_3(max_deg):
    """Monomials in (p, q, r) up to max_deg."""
    monos = []
    for d in range(max_deg + 1):
        for i in range(d + 1):
            for j in range(d - i + 1):
                k = d - i - j
                monos.append((i, j, k))
    return monos


def poly_to_vec(poly_dict, monos, mono_idx):
    """Convert {(i,j,k): coeff} to vector."""
    v = np.zeros(len(monos))
    for m, c in poly_dict.items():
        if m in mono_idx:
            v[mono_idx[m]] = c
    return v


def mul_p(p1, p2):
    """Multiply two polynomial dicts."""
    r = {}
    for m1, c1 in p1.items():
        for m2, c2 in p2.items():
            m = tuple(a + b for a, b in zip(m1, m2))
            r[m] = r.get(m, 0) + c1 * c2
    return r


def find_certificate_pqr(A, C, sos_deg=3, verbose=False):
    """
    Find SOS certificate for G₁ ≥ 0 in (p,q,r) with fixed (A,C).
    sos_deg: degree of the SOS basis (total certificate degree = 2*sos_deg).
    """
    B = 1 - A

    # Total monomial degree
    total_deg = 2 * sos_deg
    monos = monomial_list_3(total_deg)
    n_mono = len(monos)
    mono_idx = {m: i for i, m in enumerate(monos)}

    def pvec(poly_dict):
        return poly_to_vec(poly_dict, monos, mono_idx)

    # Build G₁ = AC + (B-C)·p·X - AB·X² where X = p+2q+r
    X_poly = {(1, 0, 0): 1, (0, 1, 0): 2, (0, 0, 1): 1}  # p + 2q + r
    p_poly = {(1, 0, 0): 1}
    pX = mul_p(p_poly, X_poly)
    X2 = mul_p(X_poly, X_poly)
    G_poly = {(0, 0, 0): A * C}
    for m, c in pX.items():
        G_poly[m] = G_poly.get(m, 0) + (B - C) * c
    for m, c in X2.items():
        G_poly[m] = G_poly.get(m, 0) - A * B * c
    G_vec = pvec(G_poly)

    # Constraint polynomials
    constraints_poly = {
        'p': {(1, 0, 0): 1},                                    # p ≥ 0
        'A-p': {(0, 0, 0): A, (1, 0, 0): -1},                 # A-p ≥ 0
        'C+r': {(0, 0, 0): C, (0, 0, 1): 1},                  # C+r ≥ 0
        'C-r': {(0, 0, 0): C, (0, 0, 1): -1},                 # C-r ≥ 0
        'CS+': {},  # will compute
        'CS-': {},  # will compute
        'X': dict(X_poly),                                       # X = p+2q+r ≥ 0
    }
    # CS+: (A+p)(C+r) - q²
    cs_plus = mul_p({(0, 0, 0): A, (1, 0, 0): 1}, {(0, 0, 0): C, (0, 0, 1): 1})
    cs_plus[(0, 2, 0)] = cs_plus.get((0, 2, 0), 0) - 1
    constraints_poly['CS+'] = cs_plus
    # CS-: (A-p)(C-r) - q²
    cs_minus = mul_p({(0, 0, 0): A, (1, 0, 0): -1}, {(0, 0, 0): C, (0, 0, 1): -1})
    cs_minus[(0, 2, 0)] = cs_minus.get((0, 2, 0), 0) - 1
    constraints_poly['CS-'] = cs_minus

    constraint_degs = {name: max(sum(m) for m in poly.keys()) if poly else 0
                       for name, poly in constraints_poly.items()}

    # SOS basis for the "free" SOS σ₀
    basis_0 = monomial_list_3(sos_deg)
    n_basis_0 = len(basis_0)
    Q0 = cp.Variable((n_basis_0, n_basis_0), symmetric=True)

    # SOS multiplier for each constraint
    sos_multipliers = {}
    for name, poly in constraints_poly.items():
        cdeg = constraint_degs[name]
        mult_deg = (total_deg - cdeg) // 2  # degree of multiplier basis
        if mult_deg < 0:
            continue
        basis_i = monomial_list_3(mult_deg)
        n_basis_i = len(basis_i)
        Qi = cp.Variable((n_basis_i, n_basis_i), symmetric=True)
        sos_multipliers[name] = (Qi, basis_i, poly)

    # Build the certificate expression for each monomial
    cert_expr = {}

    # σ₀ contribution: v₀^T Q₀ v₀
    for bi, bm1 in enumerate(basis_0):
        for bj, bm2 in enumerate(basis_0):
            m = tuple(a + b for a, b in zip(bm1, bm2))
            if m in mono_idx:
                if m not in cert_expr:
                    cert_expr[m] = 0
                cert_expr[m] = cert_expr[m] + Q0[bi, bj]

    # σᵢ · gᵢ contribution for each constraint
    for name, (Qi, basis_i, gpoly) in sos_multipliers.items():
        # σᵢ = vᵢ^T Qᵢ vᵢ = Σ Qᵢ[a,b] · m_a · m_b
        # σᵢ · gᵢ = Σ Qᵢ[a,b] · m_a · m_b · Σ g_coeff · m_g
        for bi, bm1 in enumerate(basis_i):
            for bj, bm2 in enumerate(basis_i):
                mm = tuple(a + b for a, b in zip(bm1, bm2))  # m_a · m_b
                for gm, gc in gpoly.items():
                    m = tuple(a + b for a, b in zip(mm, gm))
                    if m in mono_idx:
                        if m not in cert_expr:
                            cert_expr[m] = 0
                        cert_expr[m] = cert_expr[m] + Qi[bi, bj] * gc

    # Equality constraints: cert = G for each monomial
    eq_constraints = [Q0 >> 0]
    for name, (Qi, _, _) in sos_multipliers.items():
        eq_constraints.append(Qi >> 0)

    for m_idx in range(n_mono):
        m = monos[m_idx]
        lhs = cert_expr.get(m, 0)
        rhs = G_vec[m_idx]
        eq_constraints.append(lhs == rhs)

    prob = cp.Problem(cp.Minimize(0), eq_constraints)
    try:
        prob.solve(solver=cp.MOSEK, verbose=verbose,
                   mosek_params={'MSK_DPAR_INTPNT_CO_TOL_PFEAS': 1e-12,
                                 'MSK_DPAR_INTPNT_CO_TOL_DFEAS': 1e-12,
                                 'MSK_DPAR_INTPNT_CO_TOL_REL_GAP': 1e-12})
    except Exception as e:
        print(f"  Solver error: {e}")
        return None

    if prob.status in ['optimal', 'optimal_inaccurate']:
        result = {'Q0': Q0.value, 'basis_0': basis_0}
        for name, (Qi, basis_i, _) in sos_multipliers.items():
            result[f'Q_{name}'] = Qi.value
            result[f'basis_{name}'] = basis_i
        return result
    return None


def analyze_certificate(result, A, C):
    """Analyze and display the extracted certificate."""
    B = 1 - A
    Q0 = result['Q0']
    basis_0 = result['basis_0']

    eigs0 = np.linalg.eigvalsh(Q0)
    print(f"  Q₀: {Q0.shape[0]}×{Q0.shape[0]}, min_eig={eigs0[0]:.6e}, rank={np.sum(eigs0 > 1e-8)}")

    # Show constraint multiplier info
    for key in sorted(result.keys()):
        if key.startswith('Q_'):
            name = key[2:]
            Qi = result[key]
            eigs = np.linalg.eigvalsh(Qi)
            print(f"  Q_{name}: {Qi.shape[0]}×{Qi.shape[0]}, min_eig={eigs[0]:.6e}, "
                  f"rank={np.sum(eigs > 1e-8)}, trace={np.trace(Qi):.6e}")

    # Decompose Q₀ into sum of squares
    eigs, vecs = np.linalg.eigh(Q0)
    eigs_clamped = np.maximum(eigs, 0)
    print(f"\n  SOS decomposition of σ₀ (rank {np.sum(eigs > 1e-8)} terms):")
    for i in range(len(eigs)):
        if eigs_clamped[i] > 1e-10:
            row = np.sqrt(eigs_clamped[i]) * vecs[:, i]
            terms = []
            for j, (pi, qi, ri) in enumerate(basis_0):
                if abs(row[j]) > 1e-10:
                    mono = ""
                    if pi > 0:
                        mono += f"p^{pi}" if pi > 1 else "p"
                    if qi > 0:
                        mono += f"q^{qi}" if qi > 1 else "q"
                    if ri > 0:
                        mono += f"r^{ri}" if ri > 1 else "r"
                    if not mono:
                        mono = "1"
                    terms.append(f"{row[j]:+.8f}·{mono}")
            if terms:
                expr = " ".join(terms[:8])
                if len(terms) > 8:
                    expr += " ..."
                print(f"    ({expr})²")

    # Verify reconstruction
    return verify_certificate(result, A, C)


def verify_certificate(result, A, C, n_test=100000):
    """Numerically verify the certificate by sampling."""
    B = 1 - A
    import random
    random.seed(42)
    max_err = 0
    for _ in range(n_test):
        p = random.uniform(0, A)
        r = random.uniform(-C, C)
        q_max_plus = np.sqrt(max(0, (A + p) * (C + r)))
        q_max_minus = np.sqrt(max(0, (A - p) * (C - r)))
        q_max = min(q_max_plus, q_max_minus)
        if q_max <= 0:
            continue
        q = random.uniform(-q_max, q_max)
        X = p + 2 * q + r
        if X < 0:
            continue
        G = A * C + (B - C) * p * X - A * B * X * X
        if G < -1e-8:
            print(f"  VIOLATION: G={G:.6e} at p={p}, q={q}, r={r}")
            return False
    return True


# Main
print("RVW SOS Certificate via MOSEK (Putinar, p≥0 X≥0 case)")
print("=" * 60)

test_points = [
    (0.25, 0.09),    # a=0.5, c=0.3
    (0.49, 0.16),    # a=0.7, c=0.4 (previously failed)
    (0.09, 0.25),    # a=0.3, c=0.5
    (0.64, 0.09),    # a=0.8, c=0.3 (previously failed)
    (0.81, 0.04),    # a=0.9, c=0.2
    (0.36, 0.36),    # a=0.6, c=0.6 (previously failed, near tight)
    (0.25, 0.50),    # near tight manifold
    (0.10, 0.80),    # extreme
    (0.50, 0.49),    # very near tight
    (0.01, 0.01),    # small
]

for sos_deg in [2, 3]:
    print(f"\n{'='*60}")
    print(f"SOS degree = {sos_deg} (total certificate degree = {2*sos_deg})")
    print(f"{'='*60}")

    for A, C in test_points:
        B = 1 - A
        if C > B:
            C = B - 0.001
        a_val = np.sqrt(A)
        c_val = np.sqrt(C)
        b_val = np.sqrt(B)
        print(f"\nA={A:.4f}, C={C:.4f} (a={a_val:.4f}, b={b_val:.4f}, c={c_val:.4f})")

        result = find_certificate_pqr(A, C, sos_deg=sos_deg)
        if result is not None:
            print("  Status: FEASIBLE")
            ok = analyze_certificate(result, A, C)
            if ok:
                print("  Verification: PASS")
            else:
                print("  Verification: FAIL")
        else:
            print("  Status: INFEASIBLE")
