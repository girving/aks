"""
At CS- boundary: q = st where s=√(a²-p), t=√(c²-r).
Then X = a²+c² - (s-t)², and G becomes polynomial in (s,t).
Check LP feasibility in (s,t) variables.
"""
import numpy as np
from scipy.optimize import linprog
from itertools import product as iprod

def monomial_index(i, j, max_deg=4):
    """Index for s^i * t^j monomial."""
    idx = 0
    for d in range(max_deg+1):
        for jj in range(d+1):
            ii = d - jj
            if ii == i and jj == j:
                return idx
            idx += 1
    return -1

def num_monomials(max_deg=4, nvars=2):
    """Number of monomials up to max_deg in nvars variables."""
    from math import comb
    return comb(nvars + max_deg, max_deg)

def poly_to_vec(poly_dict, max_deg=4):
    """Convert {(i,j): coeff} to vector."""
    n = num_monomials(max_deg)
    v = np.zeros(n)
    for (i,j), c in poly_dict.items():
        idx = monomial_index(i, j, max_deg)
        if idx >= 0:
            v[idx] = c
    return v

def multiply_polys(p1, p2):
    """Multiply two polynomial dicts."""
    result = {}
    for (i1,j1), c1 in p1.items():
        for (i2,j2), c2 in p2.items():
            key = (i1+i2, j1+j2)
            result[key] = result.get(key, 0) + c1*c2
    return result

def square_poly(p):
    return multiply_polys(p, p)

def test_boundary(a_val, c_val, max_deg=4):
    A = a_val**2
    B = 1 - A
    b_val = np.sqrt(B)
    C = c_val**2

    # Variables: s, t where s²=A-p, t²=C-r, q=s*t
    # p = A - s², r = C - t², X = A+C - (s-t)²
    # G = AC + (B-C)*(A-s²)*(A+C-(s-t)²) - AB*(A+C-(s-t)²)²

    # Build G as polynomial in (s,t)
    # First: (A-s²) = A - s²
    Ams2 = {(0,0): A, (2,0): -1}
    # (A+C-(s-t)²) = A+C - s² + 2st - t²
    X_poly = {(0,0): A+C, (2,0): -1, (1,1): 2, (0,2): -1}

    # (B-C)*(A-s²)*X
    term1_inner = multiply_polys(Ams2, X_poly)
    term1 = {k: (B-C)*v for k,v in term1_inner.items()}

    # AB*X²
    X2 = square_poly(X_poly)
    term2 = {k: -A*B*v for k,v in X2.items()}

    # G = AC + term1 + term2
    G_poly = {(0,0): A*C}
    for k, v in term1.items():
        G_poly[k] = G_poly.get(k, 0) + v
    for k, v in term2.items():
        G_poly[k] = G_poly.get(k, 0) + v

    G_vec = poly_to_vec(G_poly, max_deg)
    n_mono = len(G_vec)

    terms = []
    names = []
    def add(name, poly_dict):
        terms.append(poly_to_vec(poly_dict, max_deg))
        names.append(name)

    # Constraints (as nonneg expressions):
    # 1. s ≥ 0: can use s as degree-1 nonneg
    # 2. t ≥ 0: same
    # 3. A - s² ≥ 0 (p ≥ 0)
    add('A-s²', {(0,0): A, (2,0): -1})
    # 4. s² ≤ 2A... wait, s² ≤ A for p ≥ 0 case (redundant with above)
    # 5. 0 ≤ t² ≤ 2C: t² ≤ 2C
    add('2C-t²', {(0,0): 2*C, (0,2): -1})
    # 6. X ≥ 0: A+C - (s-t)² ≥ 0
    add('X≥0', {(0,0): A+C, (2,0): -1, (1,1): 2, (0,2): -1})
    # 7. CS+ at boundary: (2A-s²)(2C-t²) - s²t² ≥ 0
    cs_plus = multiply_polys({(0,0): 2*A, (2,0): -1}, {(0,0): 2*C, (0,2): -1})
    cs_plus[(2,2)] = cs_plus.get((2,2), 0) - 1  # subtract s²t²
    add('CS+', cs_plus)

    # Products of degree-1 nonneg (giving degree-2 nonneg):
    # s*t ≥ 0
    add('s·t', {(1,1): 1})
    # s*(√A - s) type... hmm, √A is not polynomial. Skip.
    # s²
    add('s²', {(2,0): 1})
    # t²
    add('t²', {(0,2): 1})

    # Products of constraints (degree 2 × degree 2 = degree 4):
    # (A-s²)·(2C-t²)
    add('(A-s²)(2C-t²)', multiply_polys({(0,0):A,(2,0):-1}, {(0,0):2*C,(0,2):-1}))
    # (A-s²)·X
    add('(A-s²)·X', multiply_polys({(0,0):A,(2,0):-1}, X_poly))
    # (2C-t²)·X
    add('(2C-t²)·X', multiply_polys({(0,0):2*C,(0,2):-1}, X_poly))
    # (A-s²)·CS+
    # Too high degree (degree 4+2=6), skip if max_deg=4

    # sq_nonneg of degree-1 expressions:
    for alpha, beta, nm in [
        (1, 0, 'sq(s)'), (0, 1, 'sq(t)'), (1, -1, 'sq(s-t)'),
        (1, 1, 'sq(s+t)'), (a_val, -c_val, 'sq(as-ct)'),
        (c_val, -a_val, 'sq(cs-at)'), (b_val, -a_val, 'sq(bs-at)'),
        (b_val, -c_val, 'sq(bs-ct)'), (a_val, c_val, 'sq(as+ct)'),
        (1, -a_val, 'sq(s-at)'), (1, -c_val, 'sq(s-ct)'),
        (a_val, -1, 'sq(as-t)'), (c_val, -1, 'sq(cs-t)'),
        (b_val, 0, 'sq(bs)'), (0, b_val, 'sq(bt)'),
        (a_val*b_val, -1, 'sq(abs-t)'), (1, -a_val*b_val, 'sq(s-abt)'),
    ]:
        sq = {(0,0): 0, (2,0): alpha**2, (1,1): 2*alpha*beta, (0,2): beta**2}
        add(nm, sq)

    # sq_nonneg of degree-2 expressions (gives degree 4):
    for coeffs, nm in [
        ({(0,0): a_val, (1,0): -1}, 'sq(a-s)'),  # (a-s)²
        ({(0,0): c_val, (0,1): -1}, 'sq(c-t)'),
        ({(0,0): 0, (2,0): 1, (0,2): -1}, 'sq(s²-t²)'),
        ({(0,0): 0, (1,0): 1, (0,1): -1}, 'sq(s-t)_dup'),  # redundant
        ({(0,0): A+C, (2,0): -1, (1,1): 2, (0,2): -1}, 'sq(X)'),  # X²
        ({(0,0): A, (2,0): -1}, 'sq(A-s²)'),
        ({(0,0): 0, (1,1): 1, (0,0): 0}, 'sq(st)'),
        ({(0,0): a_val*c_val, (1,1): -1}, 'sq(ac-st)'),
        ({(2,0): 1, (0,2): 1, (0,0): -(A+C)}, 'sq(s²+t²-(A+C))'),
        ({(1,0): a_val, (0,1): -c_val, (0,0): 0}, 'sq(as-ct)_v2'),
    ]:
        sq = square_poly(coeffs)
        add(nm, sq)

    # Constraint × sq (degree up to 4):
    # (A-s²) · s²
    add('(A-s²)·s²', multiply_polys({(0,0):A,(2,0):-1}, {(2,0):1}))
    # (A-s²) · t²
    add('(A-s²)·t²', multiply_polys({(0,0):A,(2,0):-1}, {(0,2):1}))
    # (A-s²) · st
    add('(A-s²)·st', multiply_polys({(0,0):A,(2,0):-1}, {(1,1):1}))
    # (2C-t²) · s²
    add('(2C-t²)·s²', multiply_polys({(0,0):2*C,(0,2):-1}, {(2,0):1}))
    # (2C-t²) · t²
    add('(2C-t²)·t²', multiply_polys({(0,0):2*C,(0,2):-1}, {(0,2):1}))
    # (2C-t²) · st
    add('(2C-t²)·st', multiply_polys({(0,0):2*C,(0,2):-1}, {(1,1):1}))
    # X · s²
    add('X·s²', multiply_polys(X_poly, {(2,0):1}))
    # X · t²
    add('X·t²', multiply_polys(X_poly, {(0,2):1}))
    # X · st
    add('X·st', multiply_polys(X_poly, {(1,1):1}))

    # Linear terms × degree-1 nonneg:
    # s · (A-s²) -- degree 3, need higher max_deg? No, stays within degree 4 product
    # Actually s is nonneg (degree 1), (A-s²) is nonneg (degree 2), product is degree 3
    # s · X is also degree 3 nonneg product
    # These give degree-3 nonneg expressions
    add('s', {(1,0): 1})
    add('t', {(0,1): 1})
    add('s³', {(3,0): 1})
    add('t³', {(0,3): 1})
    add('s²t', {(2,1): 1})
    add('st²', {(1,2): 1})
    # s·(A-s²) = As - s³
    add('s(A-s²)', {(1,0): A, (3,0): -1})
    # t·(2C-t²) = 2Ct - t³
    add('t(2C-t²)', {(0,1): 2*C, (0,3): -1})
    # s·X = s(A+C) - s³ + 2s²t - st²
    add('s·X', multiply_polys({(1,0):1}, X_poly))
    # t·X
    add('t·X', multiply_polys({(0,1):1}, X_poly))

    n = len(terms)
    A_eq = np.array([poly_to_vec(t if isinstance(t, dict) else {}, max_deg)
                     if isinstance(t, dict) else t for t in terms]).T
    # terms are already vectors
    A_eq = np.array(terms).T

    result = linprog(np.zeros(n), A_eq=A_eq, b_eq=G_vec,
                     bounds=[(0,None)]*n, method='highs')
    return result, names, G_vec

# Test
print("Testing at CS- boundary (q=st, s=√(A-p), t=√(C-r)):")
for a_v in [0.3, 0.5, 0.7, 0.8, 0.9, 0.95]:
    b_v = np.sqrt(1 - a_v**2)
    for c_frac in [0.1, 0.3, 0.5, 0.7, 0.9, 0.99]:
        c_v = c_frac * b_v
        result, names, G_vec = test_boundary(a_v, c_v)
        status = "OK" if result.success else "FAIL"
        if result.success:
            active = [(names[i], result.x[i]) for i in range(len(result.x))
                      if result.x[i] > 1e-8]
            detail = '; '.join(f'{n}={v:.4f}' for n,v in active[:5])
            print(f"  a={a_v:.2f} c/b={c_frac:.2f}: {status}  [{detail}]")
        else:
            print(f"  a={a_v:.2f} c/b={c_frac:.2f}: {status}")
