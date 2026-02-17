"""
High-precision SOS certificate for RVW inequality via MOSEK.

At CS- boundary with q = st, s = √(A-p), t = √(C-r), p ≥ 0:
  G₊(s,t) = AC + (B-C)(A-s²)·X - AB·X²  where X = A+C-(s-t)²
with constraints s ≥ 0, t ≥ 0, A-s² ≥ 0, C-t² ≥ 0,
  (2A-s²)(2C-t²) - s²t² ≥ 0  [CS+ at CS- boundary].

G₊ is degree 4 in (s,t). We seek a Putinar-style certificate:
  G₊ = v^T Q v + Σ λ_k · g_k(s,t)
where v is a monomial vector, Q ≥ 0 (PSD), g_k are nonneg constraint products,
and λ_k ≥ 0.

Strategy: solve with MOSEK (interior-point, ~1e-12 precision), extract Q,
attempt rational reconstruction.
"""
import cvxpy as cp
import numpy as np
from fractions import Fraction
import sys


def find_certificate(a_val, c_val, verbose=False):
    A = a_val**2
    B = 1 - A
    b_val = np.sqrt(B)
    C = c_val**2

    # Degree-6 monomials in (s,t): s^i t^j with i+j ≤ 6
    # (degree-6 because SOS from degree-3 basis gives degree 6)
    max_deg = 6
    monos = []
    for d in range(max_deg + 1):
        for j in range(d + 1):
            i = d - j
            monos.append((i, j))
    n_mono = len(monos)  # 28 for degree 6
    mono_idx = {m: i for i, m in enumerate(monos)}

    def poly_vec(poly_dict):
        v = np.zeros(n_mono)
        for (i, j), c in poly_dict.items():
            if (i, j) in mono_idx:
                v[mono_idx[(i, j)]] = c
        return v

    def mul_p(p1, p2):
        r = {}
        for m1, c1 in p1.items():
            for m2, c2 in p2.items():
                m = (m1[0] + m2[0], m1[1] + m2[1])
                r[m] = r.get(m, 0) + c1 * c2
        return r

    # Build G₊(s,t) = AC + (B-C)(A-s²)·X - AB·X²
    # where X = A+C - s² + 2st - t²
    X_poly = {(0, 0): A + C, (2, 0): -1, (1, 1): 2, (0, 2): -1}
    Ams2 = {(0, 0): A, (2, 0): -1}

    term1 = {k: (B - C) * v for k, v in mul_p(Ams2, X_poly).items()}
    X2 = mul_p(X_poly, X_poly)
    term2 = {k: -A * B * v for k, v in X2.items()}
    G_poly = {(0, 0): A * C}
    for p in [term1, term2]:
        for k, v in p.items():
            G_poly[k] = G_poly.get(k, 0) + v

    # Verify G_poly degree is ≤ 4
    for (i, j) in G_poly:
        assert i + j <= 4, f"G has degree {i+j} term"

    G_vec = poly_vec(G_poly)

    # SOS basis: degree-3 monomials → 10×10 PSD matrix
    # Basis: {1, s, t, s², st, t², s³, s²t, st², t³}
    basis = []
    for d in range(4):  # degree 0..3
        for j in range(d + 1):
            i = d - j
            basis.append((i, j))
    n_basis = len(basis)  # 10

    Q = cp.Variable((n_basis, n_basis), symmetric=True)

    # SOS coefficients from Q
    sos_expr = {}
    for bi, bm1 in enumerate(basis):
        for bj, bm2 in enumerate(basis):
            m = (bm1[0] + bm2[0], bm1[1] + bm2[1])
            if m not in sos_expr:
                sos_expr[m] = 0
            sos_expr[m] = sos_expr[m] + Q[bi, bj]

    # Nonneg terms (constraint products with nonneg multipliers)
    nonneg_terms = []
    nonneg_names = []

    def add_nonneg(name, poly_dict):
        # Filter to monomials within our degree bound
        filtered = {k: v for k, v in poly_dict.items() if k[0] + k[1] <= max_deg}
        v = poly_vec(filtered)
        nonneg_terms.append(v)
        nonneg_names.append(name)

    # Basic constraint polynomials (all nonneg in feasible region)
    g_As2 = {(0, 0): A, (2, 0): -1}  # A - s² ≥ 0
    g_Ct2 = {(0, 0): C, (0, 2): -1}  # C - t² ≥ 0
    g_X = dict(X_poly)  # X = A+C-(s-t)² ≥ 0
    g_cs = mul_p({(0, 0): 2 * A, (2, 0): -1}, {(0, 0): 2 * C, (0, 2): -1})
    g_cs[(2, 2)] = g_cs.get((2, 2), 0) - 1  # CS+: (2A-s²)(2C-t²)-s²t²

    # Degree-1 nonneg: s, t
    # Degree-2 nonneg: s², st, t², A-s², C-t², X, CS+
    # Products up to degree 6

    # --- Scalar nonneg terms (degree 0-4) ---
    # Basic constraints
    add_nonneg('A-s²', g_As2)
    add_nonneg('C-t²', g_Ct2)
    add_nonneg('X', g_X)
    add_nonneg('CS+', g_cs)
    add_nonneg('s', {(1, 0): 1})
    add_nonneg('t', {(0, 1): 1})

    # Squares of monomials (trivially nonneg)
    for i in range(5):
        for j in range(5 - i):
            if i + j >= 1 and 2 * (i + j) <= max_deg:
                add_nonneg(f's^{2*i}t^{2*j}', {(2 * i, 2 * j): 1})

    # Products of degree-1 × constraints (degree 3-5)
    for sname, spoly in [('s', {(1, 0): 1}), ('t', {(0, 1): 1})]:
        for cname, cpoly in [('A-s²', g_As2), ('C-t²', g_Ct2), ('X', g_X)]:
            p = mul_p(spoly, cpoly)
            if all(i + j <= max_deg for (i, j) in p):
                add_nonneg(f'{sname}·{cname}', p)

    # Products of two degree-2 constraints (degree 4)
    for cn1, cp1 in [('A-s²', g_As2), ('C-t²', g_Ct2), ('X', g_X)]:
        for cn2, cp2 in [('A-s²', g_As2), ('C-t²', g_Ct2), ('X', g_X)]:
            p = mul_p(cp1, cp2)
            if all(i + j <= max_deg for (i, j) in p):
                add_nonneg(f'{cn1}·{cn2}', p)

    # Constraint × monomial² (degree up to 6)
    for cname, cpoly in [('A-s²', g_As2), ('C-t²', g_Ct2), ('X', g_X), ('CS+', g_cs)]:
        for mi in range(3):
            for mj in range(3 - mi):
                if mi + mj >= 1:
                    mono = {(2 * mi, 2 * mj): 1}
                    p = mul_p(cpoly, mono)
                    if all(i + j <= max_deg for (i, j) in p):
                        add_nonneg(f'{cname}·s^{2*mi}t^{2*mj}', p)

    # Triple products and higher (degree 5-6)
    for sname, spoly in [('s', {(1, 0): 1}), ('t', {(0, 1): 1})]:
        for cn1, cp1 in [('A-s²', g_As2), ('C-t²', g_Ct2), ('X', g_X)]:
            for cn2, cp2 in [('A-s²', g_As2), ('C-t²', g_Ct2), ('X', g_X)]:
                p = mul_p(spoly, mul_p(cp1, cp2))
                if all(i + j <= max_deg for (i, j) in p):
                    add_nonneg(f'{sname}·{cn1}·{cn2}', p)

    # CS+ × monomials
    for mi in range(2):
        for mj in range(2 - mi):
            mono = {(2 * mi, 2 * mj): 1} if mi + mj >= 1 else {(0, 0): 1}
            p = mul_p(g_cs, mono)
            if all(i + j <= max_deg for (i, j) in p):
                add_nonneg(f'CS+·s^{2*mi}t^{2*mj}', p)

    # s·t × constraints
    st = {(1, 1): 1}
    for cname, cpoly in [('A-s²', g_As2), ('C-t²', g_Ct2), ('X', g_X)]:
        p = mul_p(st, cpoly)
        if all(i + j <= max_deg for (i, j) in p):
            add_nonneg(f'st·{cname}', p)
        # st · constraint · monomial
        for mi in range(2):
            for mj in range(2 - mi):
                if mi + mj >= 1:
                    mono = {(mi, mj): 1}
                    p2 = mul_p(p, mono)
                    if all(i + j <= max_deg for (i, j) in p2):
                        add_nonneg(f'st·{cname}·s^{mi}t^{mj}', p2)

    n_nonneg = len(nonneg_terms)
    lambdas = cp.Variable(n_nonneg, nonneg=True)
    nonneg_mat = np.array(nonneg_terms).T  # n_mono × n_nonneg

    # Constraint: for each monomial, G_coeff = SOS_coeff + Σ λ_k · nonneg_k_coeff
    constraints = [Q >> 0]
    for m_idx in range(n_mono):
        mono = monos[m_idx]
        lhs = nonneg_mat[m_idx, :] @ lambdas
        if mono in sos_expr:
            lhs = lhs + sos_expr[mono]
        constraints.append(lhs == G_vec[m_idx])

    prob = cp.Problem(cp.Minimize(0), constraints)
    try:
        prob.solve(solver=cp.MOSEK, verbose=verbose)
    except Exception as e:
        print(f"  Solver error: {e}")
        return None, None, None, None

    if prob.status in ['optimal', 'optimal_inaccurate']:
        return Q.value, lambdas.value, nonneg_names, basis
    return None, None, None, None


def check_certificate(Q, lam, names, basis, a_val, c_val):
    """Verify the certificate numerically."""
    A = a_val**2
    B = 1 - A
    C = c_val**2

    if Q is None:
        return False, float('inf')

    eigs = np.linalg.eigvalsh(Q)
    min_eig = eigs[0]
    active = [(names[i], lam[i]) for i in range(len(lam)) if abs(lam[i]) > 1e-10]

    return min_eig >= -1e-10, min_eig


def rationalize(x, max_denom=10000):
    """Try to find a rational approximation."""
    return Fraction(x).limit_denominator(max_denom)


def extract_certificate(Q, basis, lam, names, a_val, c_val):
    """Extract and display the certificate."""
    A = a_val**2
    B = 1 - A
    C = c_val**2

    print(f"\n  Certificate for a={a_val:.4f}, c={c_val:.4f} (A={A:.6f}, C={C:.6f}):")

    # Eigendecomposition of Q
    eigs, vecs = np.linalg.eigh(Q)
    print(f"  Q eigenvalues: {np.sort(eigs)[::-1][:5]} ...")
    print(f"  Min eigenvalue: {eigs[0]:.6e}")

    # Check rank
    rank = np.sum(eigs > 1e-8)
    print(f"  Q rank: {rank} (of {Q.shape[0]})")

    # Active lambda terms
    active = [(names[i], lam[i]) for i in range(len(lam)) if abs(lam[i]) > 1e-8]
    print(f"  Active λ terms: {len(active)}")
    for name, val in sorted(active, key=lambda x: -x[1])[:10]:
        print(f"    {name}: {val:.10e}")

    # Try Cholesky-like decomposition for the SOS part
    # Q = L^T L, so v^T Q v = ||Lv||² = Σ (row_i · v)²
    if eigs[0] >= -1e-10:
        # Clamp small negative eigenvalues
        eigs_clamped = np.maximum(eigs, 0)
        sqrt_eigs = np.sqrt(eigs_clamped)
        L = np.diag(sqrt_eigs) @ vecs.T  # L such that Q ≈ L^T L

        # Each row of L gives a linear combination of basis monomials
        print(f"\n  SOS decomposition (v^T Q v = Σ_i (L_i · v)²):")
        for i in range(L.shape[0]):
            row = L[i]
            if np.max(np.abs(row)) > 1e-6:
                terms = []
                for j, (si, tj) in enumerate(basis):
                    if abs(row[j]) > 1e-8:
                        coeff = row[j]
                        if si == 0 and tj == 0:
                            terms.append(f"{coeff:+.8f}")
                        else:
                            mono = ""
                            if si > 0:
                                mono += f"s^{si}" if si > 1 else "s"
                            if tj > 0:
                                mono += f"t^{tj}" if tj > 1 else "t"
                            terms.append(f"{coeff:+.8f}·{mono}")
                if terms:
                    expr = " ".join(terms)
                    print(f"    ({expr})²")

    # Reconstruction residual
    max_deg = 6
    monos = []
    for d in range(max_deg + 1):
        for j in range(d + 1):
            monos.append((d - j, j))

    return eigs[0] >= -1e-10


# Main
print("RVW SOS Certificate Extraction via MOSEK")
print("=" * 50)

test_points = [
    (0.5, 0.3),
    (0.7, 0.4),
    (0.3, 0.5),
    (0.8, 0.3),
    (0.9, 0.2),
    (0.6, 0.6),  # near tight manifold (c ≈ b)
    (0.5, 0.49 * np.sqrt(0.75)),  # near tight
]

all_ok = True
for a_v, c_v in test_points:
    b_v = np.sqrt(1 - a_v**2)
    if c_v > b_v:
        c_v = b_v * 0.99
    print(f"\na={a_v:.4f}, b={b_v:.4f}, c={c_v:.4f}")
    Q, lam, names, basis = find_certificate(a_v, c_v, verbose=False)
    if Q is not None:
        ok, min_eig = check_certificate(Q, lam, names, basis, a_v, c_v)
        print(f"  Status: {'OK' if ok else 'FAIL'} (min_eig={min_eig:.6e})")
        extract_certificate(Q, basis, lam, names, a_v, c_v)
        if not ok:
            all_ok = False
    else:
        print("  Status: INFEASIBLE")
        all_ok = False

print(f"\n{'=' * 50}")
print(f"Overall: {'ALL OK' if all_ok else 'SOME FAILED'}")
