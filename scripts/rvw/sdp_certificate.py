"""
SDP to find full-matrix SOS certificate for the RVW inequality.

After case split (p≥0, X≥0) and substituting at CS- boundary
(q = st, s=√(a²-p), t=√(c²-r)):
  G(s,t) = a²c² + (b²-c²)(a²-s²)(a²+c²-(s-t)²) - a²b²(a²+c²-(s-t)²)² ≥ 0

with constraints s ≥ 0, t ≥ 0, s² ≤ a², t² ≤ 2c²,
(2a²-s²)(2c²-t²) ≥ s²t² [CS+ at CS- boundary].

G is degree 4 in (s,t). We seek:
  G = v^T Q v + Σ λ_i g_i(s,t) · (nonneg multiplier)
where v is a vector of monomials and Q is PSD.

Using degree-3 monomial vector v = [1, s, t, s², st, t², s³, s²t, st², t³]
gives a 10x10 PSD matrix Q, representing degree-6 SOS.
"""
import cvxpy as cp
import numpy as np

def find_certificate(a_val, c_val, verbose=False):
    A = a_val**2
    B = 1 - A
    b_val = np.sqrt(B)
    C = c_val**2

    # Degree-4 monomials in (s,t): s^i t^j with i+j ≤ 4
    # We index them as (i,j) pairs
    max_deg = 4
    monos = [(i,j) for d in range(max_deg+1) for j in range(d+1) for i in [d-j]]
    n_mono = len(monos)  # 15
    mono_idx = {m: i for i, m in enumerate(monos)}

    def poly_vec(poly_dict):
        v = np.zeros(n_mono)
        for (i,j), c in poly_dict.items():
            if (i,j) in mono_idx:
                v[mono_idx[(i,j)]] = c
        return v

    def mult_mono(m1, m2):
        return (m1[0]+m2[0], m1[1]+m2[1])

    # Build G(s,t)
    X_poly = {(0,0): A+C, (2,0): -1, (1,1): 2, (0,2): -1}
    Ams2 = {(0,0): A, (2,0): -1}

    def mul_p(p1, p2):
        r = {}
        for m1, c1 in p1.items():
            for m2, c2 in p2.items():
                m = mult_mono(m1, m2)
                r[m] = r.get(m, 0) + c1*c2
        return r

    term1 = {k: (B-C)*v for k,v in mul_p(Ams2, X_poly).items()}
    X2 = mul_p(X_poly, X_poly)
    term2 = {k: -A*B*v for k,v in X2.items()}
    G_poly = {(0,0): A*C}
    for p in [term1, term2]:
        for k,v in p.items():
            G_poly[k] = G_poly.get(k, 0) + v

    G_vec = poly_vec(G_poly)

    # SDP variable: Q is n_basis x n_basis PSD matrix
    # Basis for degree-2 monomials (so Q*v gives degree-4 sum of squares)
    basis_2 = [(i,j) for d in range(3) for j in range(d+1) for i in [d-j]]
    n_basis = len(basis_2)  # 6: 1, s, t, s², st, t²

    Q = cp.Variable((n_basis, n_basis), symmetric=True)

    # The SOS from Q: sum over (i,j),(k,l) in basis: Q[ij,kl] * s^(i+k) t^(j+l)
    sos_coeffs = np.zeros(n_mono)
    constraints_list = [Q >> 0]  # PSD

    # Build SOS coefficient vector as function of Q
    # sos_coeffs[mono_idx[m]] = sum over (i,j),(k,l) such that i+k,j+l = m of Q[idx(i,j), idx(k,l)]
    sos_expr = [0] * n_mono
    for bi, bm1 in enumerate(basis_2):
        for bj, bm2 in enumerate(basis_2):
            m = mult_mono(bm1, bm2)
            if m in mono_idx:
                sos_expr[mono_idx[m]] = sos_expr[mono_idx[m]] + Q[bi, bj]

    # Constraint multipliers (nonneg scalars times constraint polynomials)
    # g1 = A - s² (degree 2): multiplier can be degree-2 SOS
    # For simplicity, use scalar multipliers on degree-2 constraints
    # and linear multipliers on degree-1 constraints (giving degree 3 products, need degree ≤ 4)

    # Scalar multipliers on constraints:
    lam = {}
    constraint_polys = {
        'A-s2': {(0,0): A, (2,0): -1},
        '2C-t2': {(0,0): 2*C, (0,2): -1},
        'X>=0': X_poly.copy(),
        'CS+': None,  # will compute
        's': {(1,0): 1},
        't': {(0,1): 1},
    }
    # CS+ = (2A-s²)(2C-t²) - s²t²
    cs_plus = mul_p({(0,0):2*A,(2,0):-1}, {(0,0):2*C,(0,2):-1})
    cs_plus[(2,2)] = cs_plus.get((2,2),0) - 1
    constraint_polys['CS+'] = cs_plus

    # For degree-2 constraints, multiplier is degree ≤ 2 (to give degree ≤ 4 product)
    # Use SOS multiplier: v_small^T P v_small where v_small = [1, s, t]
    # For degree-1 constraints (s, t), multiplier is degree ≤ 3

    # Let's use: for each degree-2 constraint g, a scalar λ ≥ 0
    # Plus: for each pair (degree-1 constraint, degree-1 nonneg), scalar μ ≥ 0
    # Plus: for each degree-2 constraint, a degree-2 SOS multiplier

    # Strategy: use scalar multipliers on ALL constraint products up to degree 4
    nonneg_terms = []
    nonneg_names = []

    def add_nonneg(name, poly_dict):
        v = poly_vec(poly_dict)
        nonneg_terms.append(v)
        nonneg_names.append(name)

    # Degree-2 constraints as nonneg:
    add_nonneg('A-s²', {(0,0): A, (2,0): -1})
    add_nonneg('2C-t²', {(0,0): 2*C, (0,2): -1})
    add_nonneg('X', X_poly)
    add_nonneg('CS+', cs_plus)

    # Degree-1 nonneg:
    add_nonneg('s', {(1,0): 1})
    add_nonneg('t', {(0,1): 1})

    # Products of degree-1 nonneg (degree 2):
    add_nonneg('s²', {(2,0): 1})
    add_nonneg('st', {(1,1): 1})
    add_nonneg('t²', {(0,2): 1})

    # Products: degree-2 constraint × degree-2 nonneg (degree 4):
    for cname, cpoly in [('A-s²', {(0,0):A,(2,0):-1}), ('2C-t²', {(0,0):2*C,(0,2):-1}),
                          ('X', X_poly)]:
        for mname, mpoly in [('s²', {(2,0):1}), ('st', {(1,1):1}), ('t²', {(0,2):1}),
                              ('1', {(0,0):1})]:
            p = mul_p(cpoly, mpoly)
            # Check degree ≤ 4
            if all(i+j <= 4 for (i,j) in p):
                add_nonneg(f'{cname}*{mname}', p)

    # Products: degree-1 × degree-2 constraint (degree 3):
    for sname, spoly in [('s', {(1,0):1}), ('t', {(0,1):1})]:
        for cname, cpoly in [('A-s²', {(0,0):A,(2,0):-1}), ('2C-t²', {(0,0):2*C,(0,2):-1}),
                              ('X', X_poly)]:
            p = mul_p(spoly, cpoly)
            if all(i+j <= 4 for (i,j) in p):
                add_nonneg(f'{sname}*{cname}', p)

    # Products: CS+ × nonneg (degree 4 + 0 = 4):
    add_nonneg('CS+*1', cs_plus)  # redundant, but ok

    # Degree-4 products of two degree-2 constraints:
    for cn1, cp1 in [('A-s²', {(0,0):A,(2,0):-1}), ('2C-t²', {(0,0):2*C,(0,2):-1}), ('X', X_poly)]:
        for cn2, cp2 in [('A-s²', {(0,0):A,(2,0):-1}), ('2C-t²', {(0,0):2*C,(0,2):-1}), ('X', X_poly)]:
            p = mul_p(cp1, cp2)
            if all(i+j <= 4 for (i,j) in p):
                add_nonneg(f'{cn1}*{cn2}', p)

    # Degree-3 nonneg: s³, s²t, st², t³, s·X, t·X, s(A-s²), t(2C-t²)
    add_nonneg('s³', {(3,0): 1})
    add_nonneg('s²t', {(2,1): 1})
    add_nonneg('st²', {(1,2): 1})
    add_nonneg('t³', {(0,3): 1})

    # Degree-4 nonneg: s⁴, s³t, s²t², st³, t⁴
    add_nonneg('s⁴', {(4,0): 1})
    add_nonneg('s³t', {(3,1): 1})
    add_nonneg('s²t²', {(2,2): 1})
    add_nonneg('st³', {(1,3): 1})
    add_nonneg('t⁴', {(0,4): 1})

    n_nonneg = len(nonneg_terms)
    lambdas = cp.Variable(n_nonneg, nonneg=True)

    # Constraint: G = SOS(Q) + Σ λ_i * nonneg_i
    nonneg_mat = np.array(nonneg_terms).T  # n_mono x n_nonneg

    for m_idx in range(n_mono):
        lhs = sos_expr[m_idx] + nonneg_mat[m_idx, :] @ lambdas
        constraints_list.append(lhs == G_vec[m_idx])

    prob = cp.Problem(cp.Minimize(0), constraints_list)
    try:
        prob.solve(solver=cp.SCS, verbose=False, max_iters=10000)
    except:
        return None, None, None

    if prob.status in ['optimal', 'optimal_inaccurate']:
        return Q.value, lambdas.value, nonneg_names
    return None, None, None


# Test
print("SDP certificate search (degree-4 SOS in s,t at CS- boundary):")
results = []
for a_v in [0.3, 0.5, 0.6, 0.7, 0.8, 0.9, 0.95]:
    b_v = np.sqrt(1 - a_v**2)
    for c_frac in [0.1, 0.3, 0.5, 0.7, 0.9, 0.99]:
        c_v = c_frac * b_v
        Q, lam, names = find_certificate(a_v, c_v)
        status = "OK" if Q is not None else "FAIL"
        results.append((a_v, c_frac, status))
        if Q is not None:
            eigs = np.linalg.eigvalsh(Q)
            min_eig = min(eigs)
            active = [(names[i], lam[i]) for i in range(len(lam)) if lam[i] > 1e-6]
            n_active = len(active)
            print(f"  a={a_v:.2f} c/b={c_frac:.2f}: {status} (min_eig={min_eig:.2e}, {n_active} active λ)")
        else:
            print(f"  a={a_v:.2f} c/b={c_frac:.2f}: {status}")

n_ok = sum(1 for _,_,s in results if s == "OK")
print(f"\nSummary: {n_ok}/{len(results)} feasible")
