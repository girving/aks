"""
Extended LP with sq_nonneg hints using a, b, c directly (not just a², c²).
Key: terms like sq_nonneg(a*q - c*p) create ac·pq cross-terms.
"""
import numpy as np
from scipy.optimize import linprog

def test_certificate(a_val, c_val):
    """Test LP feasibility with explicit a, c values."""
    A = a_val**2
    B = 1 - A
    b_val = np.sqrt(B)
    C = c_val**2

    # Monomials in (p,q,r): 1, p, q, r, p², pq, pr, q², qr, r²
    # G coefficients:
    G = np.array([A*C, 0, 0, 0, B**2-C, 2*(B**2-A*B-C),
                  B**2-A*B-C, -4*A*B, -4*A*B, -A*B])

    terms = []
    names = []

    def add(name, vec):
        terms.append(vec)
        names.append(name)

    # Constraint slacks
    add('cs+', [A*C, C, 0, A, 0, 0, 1, -1, 0, 0])
    add('cs-', [A*C, -C, 0, -A, 0, 0, 1, -1, 0, 0])
    add('comb', [C*A**2, 0, 0, 0, -C, 0, 0, -A, 0, 0])

    # Products of nonneg linear terms (in p≥0, X≥0 case)
    add('(C-r)X', [0, C, 2*C, C, 0, 0, -1, 0, -2, -1])
    add('pX', [0, 0, 0, 0, 1, 2, 1, 0, 0, 0])
    add('(A-p)X', [0, A, 2*A, A, -1, -2, -1, 0, 0, 0])
    add('p(C-r)', [0, C, 0, 0, 0, 0, -1, 0, 0, 0])
    add('(A-p)(C-r)', [A*C, -C, 0, -A, 0, 0, 1, 0, 0, 0])
    add('(C+r)X', [0, C, 2*C, C, 0, 0, 1, 0, 2, 1])
    add('(A+p)X', [0, A, 2*A, A, 1, 2, 1, 0, 0, 0])

    # sq_nonneg basic
    add('sq_q', [0,0,0,0, 0,0,0, 1,0,0])
    add('sq_r', [0,0,0,0, 0,0,0, 0,0,1])
    add('sq_p', [0,0,0,0, 1,0,0, 0,0,0])

    # KEY: sq_nonneg with a, c cross terms
    # sq(a*q - c*p) = A*q² - 2ac*pq + C*p²
    ac = a_val * c_val
    ab = a_val * b_val
    bc = b_val * c_val
    add('sq(aq-cp)', [0,0,0,0, C, -2*ac, 0, A, 0, 0])
    add('sq(aq+cp)', [0,0,0,0, C, 2*ac, 0, A, 0, 0])
    add('sq(ar-cq)', [0,0,0,0, 0, 0, 0, C, -2*ac, A])
    add('sq(ar+cq)', [0,0,0,0, 0, 0, 0, C, 2*ac, A])
    add('sq(ap-cr)', [0,0,0,0, A, 0, -2*ac, 0, 0, C])
    add('sq(ap+cr)', [0,0,0,0, A, 0, 2*ac, 0, 0, C])

    # sq with b
    add('sq(bq-something)', [0,0,0,0, 0,0,0, B, 0, 0])  # = b²q²
    add('sq(bp-something)', [0,0,0,0, B,0,0, 0,0,0])  # = b²p²
    add('sq(br)', [0,0,0,0, 0,0,0, 0,0,B])

    # Cross terms with ab, bc
    add('sq(abq-cp)', [0,0,0,0, C, -2*ab*c_val, 0, A*B, 0, 0])  # = a²b²q² - 2abcpq + c²p²
    add('sq(aq-bcr)', [0,0,0,0, 0, 0, 0, A, -2*a_val*bc, B*C])  # a²q² - 2abcqr + b²c²r²
    add('sq(abq-r)', [0,0,0,0, 0, 0, 0, A*B, -2*ab, 1])  # a²b²q² - 2abqr + r²

    # More general: sq(αp + βq + γr) for various (α,β,γ)
    for alpha, beta, gamma, name in [
        (b_val, -a_val, 0, 'sq(bp-aq)'),
        (0, ab, -1, 'sq(abq-r)2'),
        (0, ab, -c_val, 'sq(abq-cr)'),
        (a_val, 0, -c_val, 'sq(ap-cr)2'),
        (c_val, -a_val, 0, 'sq(cp-aq)2'),
        (1, -ab, 0, 'sq(p-abq)'),
        (0, 1, -ab, 'sq(q-abr)'),
        (ac, -1, 0, 'sq(acp-q)'),
        (0, ac, -1, 'sq(acq-r)'),
        (bc, -a_val, 0, 'sq(bcp-aq)'),
    ]:
        sq = [0, 0, 0, 0,
              alpha**2, 2*alpha*beta, 2*alpha*gamma,
              beta**2, 2*beta*gamma, gamma**2]
        add(name, sq)

    # Linear constraints
    add('lam_p', [0,1,0,0, 0,0,0, 0,0,0])
    add('lam_Ap', [A,-1,0,0, 0,0,0, 0,0,0])
    add('lam_Cr', [C,0,0,1, 0,0,0, 0,0,0])
    add('lam_Cr2', [C,0,0,-1, 0,0,0, 0,0,0])
    add('lam_X', [0,1,2,1, 0,0,0, 0,0,0])

    # Products involving linear × linear (degree 2 nonneg products)
    add('C²-r²', [C**2,0,0,0, 0,0,0, 0,0,-1])
    add('p(A-p)', [0,A,0,0, -1,0,0, 0,0,0])
    add('(A-p)(C+r)', [A*C,-C,0,A, 0,0,-1, 0,0,0])
    add('(A+p)(C-r)', [A*C,C,0,-A, 0,0,-1, 0,0,0])
    add('(C+r)p', [0,C,0,0, 0,0,1, 0,0,0])
    add('X²', [0,0,0,0, 1,4,2, 4,4,1])

    n = len(terms)
    A_eq = np.array(terms).T
    result = linprog(np.zeros(n), A_eq=A_eq, b_eq=G,
                     bounds=[(0,None)]*n, method='highs')
    return result, names

# Test
for a_v in [0.3, 0.5, 0.7, 0.8, 0.9, 0.95]:
    b_v = np.sqrt(1 - a_v**2)
    for c_v in [0.1*b_v, 0.3*b_v, 0.5*b_v, 0.7*b_v, 0.9*b_v, 0.99*b_v]:
        result, names = test_certificate(a_v, c_v)
        status = "OK" if result.success else "FAIL"
        if result.success:
            active = [(names[i], result.x[i]) for i in range(len(result.x))
                      if result.x[i] > 1e-8]
            detail = '; '.join(f'{n}={v:.4f}' for n,v in active[:6])
            print(f"a={a_v:.2f} c={c_v:.4f}: {status}  [{detail}]")
        else:
            print(f"a={a_v:.2f} c={c_v:.4f}: {status}")
