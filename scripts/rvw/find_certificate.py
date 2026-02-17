"""
Find Positivstellensatz certificate for RVW quadratic inequality.

G(p,q,r) = a²c² + (b²-c²)·p·X - a²b²·X² ≥ 0
where X = p+2q+r, in the case p ≥ 0, X ≥ 0.

G is QUADRATIC in (p,q,r). We seek a certificate:
  G = Σ λᵢ·hᵢ + Σ μⱼ·(product of nonneg quantities)
where hᵢ are constraint slacks and products are of nonneg linear terms.

This is an LP in the certificate coefficients. We test at many (A,C) values.
"""
import numpy as np
from scipy.optimize import linprog

def test_certificate(A, C):
    """Test LP feasibility at given A=a², C=c² values."""
    B = 1 - A  # b²

    # Monomials in (p,q,r): 1, p, q, r, p², pq, pr, q², qr, r²
    # G coefficients (target):
    G = np.array([
        A*C,           # [1]
        0,             # [p]
        0,             # [q]
        0,             # [r]
        B**2 - C,      # [p²]
        2*(B**2 - A*B - C),  # [pq]
        B**2 - A*B - C,      # [pr]
        -4*A*B,        # [q²]
        -4*A*B,        # [qr]
        -A*B,          # [r²]
    ])

    # Decision variables: coefficients of nonneg terms
    # Order: c_cs_plus, c_cs_minus, c_combined, c_h1, c_h2, c_h3, c_h4, c_h5,
    #         c_sq_q, c_sq_r, c_sq_p, c_sq_X, c_sq_ap, c_sq_cr,
    #         lam1, lam2, lam3, lam4, lam7,
    #         c_pX, c_apX  (= (a²-p)·X product)

    # Each nonneg term is a vector of 10 monomial coefficients.
    terms = []

    # h_cs_plus = (A+p)(C+r) - q² = AC + Cp + Ar + pr - q²
    terms.append([A*C, C, 0, A, 0, 0, 1, -1, 0, 0])

    # h_cs_minus = (A-p)(C-r) - q² = AC - Cp - Ar + pr - q²
    terms.append([A*C, -C, 0, -A, 0, 0, 1, -1, 0, 0])

    # h_combined = c²(a⁴-p²) - a²q² = C·A² - C·p² - A·q²
    terms.append([C*A**2, 0, 0, 0, -C, 0, 0, -A, 0, 0])

    # h1 = (c²-r)·X = (C-r)(p+2q+r) = Cp+2Cq+Cr-pr-2qr-r²
    terms.append([0, C, 2*C, C, 0, 0, -1, 0, -2, -1])

    # h2 = p·X = p(p+2q+r) = p²+2pq+pr
    terms.append([0, 0, 0, 0, 1, 2, 1, 0, 0, 0])

    # h3 = (a²-p)·X = (A-p)(p+2q+r) = Ap+2Aq+Ar-p²-2pq-pr
    terms.append([0, A, 2*A, A, -1, -2, -1, 0, 0, 0])

    # h4 = p·(c²-r) = Cp - pr
    terms.append([0, C, 0, 0, 0, 0, -1, 0, 0, 0])

    # h5 = (a²-p)(c²-r) = AC-Ar-Cp+pr  [same as CS- without q² term]
    terms.append([A*C, -C, 0, -A, 0, 0, 1, 0, 0, 0])

    # sq_nonneg(q) = q²
    terms.append([0, 0, 0, 0, 0, 0, 0, 1, 0, 0])

    # sq_nonneg(r) = r²
    terms.append([0, 0, 0, 0, 0, 0, 0, 0, 0, 1])

    # sq_nonneg(p) = p²
    terms.append([0, 0, 0, 0, 1, 0, 0, 0, 0, 0])

    # sq_nonneg(X) = (p+2q+r)² = p²+4q²+r²+4pq+4qr+2pr
    terms.append([0, 0, 0, 0, 1, 4, 2, 4, 4, 1])

    # sq_nonneg(a²-p) = A²-2Ap+p²
    terms.append([A**2, -2*A, 0, 0, 1, 0, 0, 0, 0, 0])

    # sq_nonneg(c²-r) = C²-2Cr+r²
    terms.append([C**2, 0, 0, -2*C, 0, 0, 0, 0, 0, 0, ])  # BUG: 11 entries

    # Fix: sq_nonneg(c²-r) = C² - 2Cr + r²
    terms[-1] = [C**2, 0, 0, -2*C, 0, 0, 0, 0, 0, 1]

    # lam1·p: [p]=1
    terms.append([0, 1, 0, 0, 0, 0, 0, 0, 0, 0])

    # lam2·(A-p): [1]=A, [p]=-1
    terms.append([A, -1, 0, 0, 0, 0, 0, 0, 0, 0])

    # lam3·(C+r): [1]=C, [r]=1
    terms.append([C, 0, 0, 1, 0, 0, 0, 0, 0, 0])

    # lam4·(C-r): [1]=C, [r]=-1
    terms.append([C, 0, 0, -1, 0, 0, 0, 0, 0, 0])

    # lam7·X = lam7·(p+2q+r)
    terms.append([0, 1, 2, 1, 0, 0, 0, 0, 0, 0])

    # (c²+r)·(c²-r) = C²-r²
    terms.append([C**2, 0, 0, 0, 0, 0, 0, 0, 0, -1])

    # p·(a²-p) = Ap - p²
    terms.append([0, A, 0, 0, -1, 0, 0, 0, 0, 0])

    # (a²-p)·(c²+r) = AC+Ar-Cp-pr
    terms.append([A*C, -C, 0, A, 0, 0, -1, 0, 0, 0])

    # (c²+r)·X = Cp+2Cq+Cr+pr+2qr+r²
    terms.append([0, C, 2*C, C, 0, 0, 1, 0, 2, 1])

    # sq_nonneg(a·q - c·p) needs a = √A which is irrational...
    # Instead, sq_nonneg in terms of a², c²:
    # A·q² - 2√(AC)·pq + C·p²  -- involves √(AC), can't use in LP

    # Let's add more cross-term products:
    # (a²+p)·(c²-r) = AC-Ar+Cp-pr
    terms.append([A*C, C, 0, -A, 0, 0, -1, 0, 0, 0])

    # (a²+p)·X = (A+p)(p+2q+r) = Ap+2Aq+Ar+p²+2pq+pr
    terms.append([0, A, 2*A, A, 1, 2, 1, 0, 0, 0])

    # (a²+p)·(c²+r) = AC+Ar+Cp+pr [redundant with CS+ + q²]
    terms.append([A*C, C, 0, A, 0, 0, 1, 0, 0, 0])

    # r·X = r(p+2q+r) = pr + 2qr + r² (when r ≥ 0 and X ≥ 0)
    # But r can be negative... skip for now

    # (C+r)·p = Cp + pr
    terms.append([0, C, 0, 0, 0, 0, 1, 0, 0, 0])

    n_terms = len(terms)
    # Assemble constraint matrix: A_eq @ x = G
    A_eq = np.array(terms).T  # 10 x n_terms
    b_eq = G

    # Objective: minimize 0 (feasibility)
    c_obj = np.zeros(n_terms)

    # All variables ≥ 0
    bounds = [(0, None)] * n_terms

    result = linprog(c_obj, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method='highs')
    return result

# Test at many parameter values
test_points = [
    (0.5, 0.3),   # B²=0.25, C=0.3: B²<C
    (0.5, 0.2),   # B²=0.25, C=0.2: B²>C
    (0.3, 0.4),   # B²=0.49, C=0.4
    (0.7, 0.2),   # B²=0.09, C=0.2: B²<C
    (0.8, 0.1),   # B²=0.04, C=0.1: B²<C
    (0.2, 0.6),   # B²=0.64, C=0.6
    (0.49, 0.49), # Near tight: A≈C≈B²
    (0.1, 0.8),   # Extreme
    (0.9, 0.09),  # Near tight
    (0.5, 0.499), # B²=0.25<C, close to tight
    (0.4, 0.36),  # B²=0.36=C, exactly B²=C
    (0.3, 0.3),   # B²=0.49>C
    (0.45, 0.3),  # B²=0.3025, C=0.3, very close
]

for A, C in test_points:
    B = 1 - A
    if C > B:
        continue  # Invalid: c ≤ b means C ≤ B
    result = test_certificate(A, C)
    status = "FEASIBLE" if result.success else "INFEASIBLE"
    print(f"A={A:.3f}, C={C:.3f}, B²={B**2:.3f}: {status}")
    if result.success:
        x = result.x
        # Show which terms have nonzero coefficients
        names = ['cs+', 'cs-', 'comb', 'h1=(C-r)X', 'h2=pX', 'h3=(A-p)X',
                 'h4=p(C-r)', 'h5=(A-p)(C-r)', 'sq_q', 'sq_r', 'sq_p', 'sq_X',
                 'sq_ap', 'sq_cr', 'lam1', 'lam2', 'lam3', 'lam4', 'lam7',
                 'g34=(C²-r²)', 'g12=p(A-p)', 'g23=(A-p)(C+r)', 'g37=(C+r)X',
                 'g14=(A+p)(C-r)', 'g17=(A+p)X', 'g13=(A+p)(C+r)', 'g13b=(C+r)p']
        active = [(names[i] if i < len(names) else f't{i}', x[i])
                  for i in range(len(x)) if x[i] > 1e-8]
        if active:
            print(f"  Active: {', '.join(f'{n}={v:.6f}' for n,v in active)}")
