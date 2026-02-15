#!/usr/bin/env python3
# DEAD END: This script explores the diagonal Positivstellensatz / LP approach
# to rvw_quadratic_ineq. LP infeasibility at degrees 4-8 proves this approach
# is structurally impossible — see scripts/RVW_QUADRATIC_PROOF_STATUS.md.
"""
Find an algebraic (Positivstellensatz) proof of the RVW quadratic inequality.

Goal: Prove G := A*C + (B-C)*p*X - A*B*X^2 >= 0
where B = 1-A, subject to constraints from the reflection structure.

Variables: A, C, p, r, X (all real, with q = (X-p-r)/2)

Constraints (all >= 0):
  h1 = (A+p)*(C+r) - ((X-p-r)/2)^2     (V1: q^2 <= (A+p)(C+r))
  h2 = (A-p)*(C-r) - ((X-p-r)/2)^2     (V2: q^2 <= (A-p)(C-r))
  h3 = A - p                             (p <= A, i.e., |p| <= A with WLOG p >= 0)
  h4 = p                                 (p >= 0)
  h5 = C - r                             (|r| <= C)
  h6 = C + r                             (|r| <= C)
  h7 = X                                 (X >= 0, WLOG)
  h8 = A + C - X                         (X <= A + C, from rvw_X_le_sum_sq)
  h9 = 1 - A - C                         (C <= B = 1-A)
  h10 = A                                (A > 0, use A >= 0)
  h11 = C                                (C >= 0)

We seek sigma_i >= 0 (polynomial multipliers) such that:
  G = sigma_0 + sum_i sigma_i * h_i

where sigma_0 is SOS (sum of squares).

Approach: parameterize sigma_i as polynomials with unknown coefficients,
expand, match monomials, solve linear system.
"""

import numpy as np
from itertools import product as iproduct
from fractions import Fraction
from collections import defaultdict
import sys

# We work with polynomials in 5 variables: A, C, p, r, X
# Represented as dict: (a_exp, c_exp, p_exp, r_exp, x_exp) -> coefficient

def poly_zero():
    return defaultdict(lambda: Fraction(0))

def poly_const(c):
    d = poly_zero()
    d[(0,0,0,0,0)] = Fraction(c)
    return d

def poly_var(idx):
    """Variable: A=0, C=1, p=2, r=3, X=4"""
    d = poly_zero()
    key = [0,0,0,0,0]
    key[idx] = 1
    d[tuple(key)] = Fraction(1)
    return d

def poly_add(p1, p2):
    d = poly_zero()
    for k, v in p1.items():
        d[k] += v
    for k, v in p2.items():
        d[k] += v
    return d

def poly_sub(p1, p2):
    d = poly_zero()
    for k, v in p1.items():
        d[k] += v
    for k, v in p2.items():
        d[k] -= v
    return d

def poly_mul(p1, p2):
    d = poly_zero()
    for k1, v1 in p1.items():
        for k2, v2 in p2.items():
            k = tuple(a+b for a,b in zip(k1, k2))
            d[k] += v1 * v2
    return d

def poly_scale(p, c):
    d = poly_zero()
    c = Fraction(c)
    for k, v in p.items():
        d[k] = v * c
    return d

# Define variables
A = poly_var(0)
C = poly_var(1)
p = poly_var(2)
r = poly_var(3)
X = poly_var(4)
ONE = poly_const(1)
ZERO = poly_zero()

# B = 1 - A
B = poly_sub(ONE, A)

# q_term = (X - p - r) / 2, but we work with 4*q^2 = (X-p-r)^2
# Actually let's define q_sq_times_4 = (X-p-r)^2
Xpr = poly_sub(poly_sub(X, p), r)  # X - p - r
Xpr_sq = poly_mul(Xpr, Xpr)  # (X-p-r)^2

# Constraints (all >= 0):
# h1 = (A+p)*(C+r) - (X-p-r)^2/4
h1 = poly_sub(poly_mul(poly_add(A, p), poly_add(C, r)), poly_scale(Xpr_sq, Fraction(1,4)))
# h2 = (A-p)*(C-r) - (X-p-r)^2/4
h2 = poly_sub(poly_mul(poly_sub(A, p), poly_sub(C, r)), poly_scale(Xpr_sq, Fraction(1,4)))
# h3 = A - p
h3 = poly_sub(A, p)
# h4 = p
h4 = p
# h5 = C - r
h5 = poly_sub(C, r)
# h6 = C + r
h6 = poly_add(C, r)
# h7 = X
h7 = X
# h8 = A + C - X
h8 = poly_sub(poly_add(A, C), X)
# h9 = 1 - A - C (C <= B)
h9 = poly_sub(poly_sub(ONE, A), C)
# h10 = A
h10 = A
# h11 = C
h11 = C

constraints = [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
constraint_names = ['h1(V1)', 'h2(V2)', 'h3(A-p)', 'h4(p)', 'h5(C-r)', 'h6(C+r)',
                    'h7(X)', 'h8(A+C-X)', 'h9(1-A-C)', 'h10(A)', 'h11(C)']

# Goal: G = A*C + (B-C)*p*X - A*B*X^2 >= 0
# where B = 1-A
G = poly_add(
    poly_mul(A, C),
    poly_sub(
        poly_mul(poly_mul(poly_sub(B, C), p), X),
        poly_mul(poly_mul(A, B), poly_mul(X, X))
    )
)

print("Goal G:")
for k, v in sorted(G.items()):
    if v != 0:
        print(f"  {k}: {v}")

def get_monomials_up_to_degree(nvars, max_deg):
    """Generate all monomials up to given total degree."""
    if nvars == 0:
        return [()] if max_deg >= 0 else []
    result = []
    for d in range(max_deg + 1):
        for rest in get_monomials_up_to_degree(nvars - 1, d):
            result.append((d - sum(rest),) + rest)
    # Actually let me do this properly
    result = []
    def gen(remaining_vars, remaining_deg, current):
        if remaining_vars == 0:
            result.append(tuple(current))
            return
        for d in range(remaining_deg + 1):
            gen(remaining_vars - 1, remaining_deg - d, current + [d])
    gen(nvars, max_deg, [])
    return result

def collect_monomials(poly):
    """Get set of monomials with nonzero coefficients."""
    return {k for k, v in poly.items() if v != 0}

# Determine the degree of G
G_degree = max(sum(k) for k, v in G.items() if v != 0)
print(f"G has degree {G_degree}")

# For each constraint h_i of degree d_i, the multiplier sigma_i should have
# degree <= G_degree - d_i
constraint_degrees = []
for i, h in enumerate(constraints):
    deg = max(sum(k) for k, v in h.items() if v != 0) if any(v != 0 for v in h.values()) else 0
    constraint_degrees.append(deg)
    print(f"  {constraint_names[i]} has degree {deg}")

# Strategy: Try with constant multipliers first, then linear, then quadratic
def try_with_multiplier_degree(mult_max_deg, use_products=False):
    """
    Try to find: G = sigma_0 + sum_i sigma_i * h_i
    where sigma_i are polynomials of degree <= mult_max_deg
    and sigma_0 is SOS.

    For simplicity, we first try sigma_0 = 0 (no SOS remainder needed).
    If that fails, try sigma_0 = sum of squared monomials.
    """
    print(f"\n{'='*60}")
    print(f"Trying multiplier degree {mult_max_deg}")
    print(f"{'='*60}")

    # Generate multiplier monomials for each constraint
    nvars = 5
    multiplier_vars = []  # list of (constraint_idx, monomial, variable_idx)
    var_idx = 0

    for ci, (h, cdeg) in enumerate(zip(constraints, constraint_degrees)):
        max_deg = G_degree - cdeg
        if max_deg < 0:
            continue
        effective_deg = min(mult_max_deg, max_deg)
        monoms = get_monomials_up_to_degree(nvars, effective_deg)
        for m in monoms:
            multiplier_vars.append((ci, m, var_idx))
            var_idx += 1

    if use_products:
        # Also add products of pairs of constraints (with constant multipliers)
        for ci in range(len(constraints)):
            for cj in range(ci, len(constraints)):
                prod_deg = constraint_degrees[ci] + constraint_degrees[cj]
                if prod_deg <= G_degree:
                    # h_i * h_j with a constant multiplier
                    multiplier_vars.append((-1, (ci, cj), var_idx))
                    var_idx += 1

    num_vars = var_idx
    print(f"Number of unknown coefficients: {num_vars}")

    # Collect all monomials that appear in G and in all sigma_i * h_i
    all_monoms = set()
    for k, v in G.items():
        if v != 0:
            all_monoms.add(k)

    for ci, m_or_pair, vi in multiplier_vars:
        if ci == -1:
            # Product constraint
            ci1, ci2 = m_or_pair
            h_prod = poly_mul(constraints[ci1], constraints[ci2])
            for k in h_prod:
                if h_prod[k] != 0:
                    all_monoms.add(k)
        else:
            h = constraints[ci]
            for hk, hv in h.items():
                if hv != 0:
                    mk = tuple(a+b for a,b in zip(m_or_pair, hk))
                    all_monoms.add(mk)

    all_monoms = sorted(all_monoms)
    monom_idx = {m: i for i, m in enumerate(all_monoms)}
    num_monoms = len(all_monoms)
    print(f"Number of monomial constraints: {num_monoms}")

    # Build the linear system: for each monomial, coefficient of that monomial
    # in sum_i sigma_i * h_i should equal coefficient in G.
    # Variables: the coefficients of sigma_i
    # We want: sigma_i >= 0 (for constant multipliers this means the coefficient is >= 0,
    # but for polynomial multipliers, we need sigma_i to be nonneg on the feasible set)

    # Actually for a Positivstellensatz, sigma_i just need to be SOS (sum of squares),
    # but for the LP approach let's try CONSTANT nonneg multipliers first.

    if mult_max_deg == 0 and not use_products:
        # Constant multipliers: just need sigma_i >= 0 (scalar)
        # G = sigma_0 + sum_i sigma_i * h_i
        # sigma_0 is SOS... but with constant multipliers, try sigma_0 = 0 first

        # Each sigma_i is a single nonneg variable
        # Build matrix: A_matrix @ sigma = g_vector
        A_matrix = np.zeros((num_monoms, num_vars), dtype=np.float64)
        g_vector = np.zeros(num_monoms, dtype=np.float64)

        for k, v in G.items():
            if v != 0 and k in monom_idx:
                g_vector[monom_idx[k]] = float(v)

        for ci, m, vi in multiplier_vars:
            h = constraints[ci]
            for hk, hv in h.items():
                if hv != 0:
                    mk = tuple(a+b for a,b in zip(m, hk))
                    if mk in monom_idx:
                        A_matrix[monom_idx[mk], vi] += float(hv)

        # Solve: A_matrix @ sigma = g_vector, sigma >= 0
        # This is a linear feasibility problem
        from scipy.optimize import linprog

        # linprog minimizes c^T x subject to A_ub x <= b_ub, A_eq x = b_eq, bounds
        # We want: A_matrix @ x = g_vector, x >= 0
        c = np.zeros(num_vars)  # dummy objective
        result = linprog(c, A_eq=A_matrix, b_eq=g_vector,
                        bounds=[(0, None)] * num_vars,
                        method='highs')

        if result.success:
            print("SUCCESS with constant multipliers!")
            sigma = result.x
            for ci, m, vi in multiplier_vars:
                if sigma[vi] > 1e-10:
                    print(f"  sigma_{ci} ({constraint_names[ci]}): {sigma[vi]:.6f}")
            return sigma, multiplier_vars
        else:
            print(f"INFEASIBLE with constant multipliers: {result.message}")
            return None, None

    # For polynomial multipliers, we need a different approach.
    # Let's try: sigma_i are POLYNOMIALS with NONNEG COEFFICIENTS
    # (stronger than needed - sigma_i SOS would suffice, but harder to parameterize)

    # Actually let's try: sigma_i are sums of squares of affine/linear polynomials.
    # For degree 1 multipliers: sigma_i = alpha_i (a constant >= 0)
    # For degree 2: sigma_i could be affine^2 terms

    # Let's try the simplest extension: allow products of pairs of constraints
    # G = sum_i alpha_i * h_i + sum_{i<=j} beta_{ij} * h_i * h_j
    # where alpha_i, beta_{ij} >= 0.

    if use_products:
        # Include products of constraints
        # Variables: alpha_i for each h_i, beta_{ij} for each h_i * h_j
        num_alpha = len(constraints)
        num_beta = 0
        product_pairs = []
        for ci in range(len(constraints)):
            for cj in range(ci, len(constraints)):
                if constraint_degrees[ci] + constraint_degrees[cj] <= G_degree:
                    product_pairs.append((ci, cj))
                    num_beta += 1

        total_vars = num_alpha + num_beta
        print(f"  {num_alpha} single terms + {num_beta} product terms = {total_vars} variables")

        # Recompute all monomials
        all_monoms_set = set()
        for k, v in G.items():
            if v != 0:
                all_monoms_set.add(k)

        # Single constraint terms
        for ci, h in enumerate(constraints):
            for k, v in h.items():
                if v != 0:
                    all_monoms_set.add(k)

        # Product terms
        product_polys = []
        for ci, cj in product_pairs:
            pp = poly_mul(constraints[ci], constraints[cj])
            product_polys.append(pp)
            for k, v in pp.items():
                if v != 0:
                    all_monoms_set.add(k)

        all_monoms = sorted(all_monoms_set)
        monom_idx = {m: i for i, m in enumerate(all_monoms)}
        num_monoms = len(all_monoms)
        print(f"  {num_monoms} monomials")

        A_matrix = np.zeros((num_monoms, total_vars), dtype=np.float64)
        g_vector = np.zeros(num_monoms, dtype=np.float64)

        for k, v in G.items():
            if v != 0 and k in monom_idx:
                g_vector[monom_idx[k]] = float(v)

        # Single terms
        for ci, h in enumerate(constraints):
            for k, v in h.items():
                if v != 0 and k in monom_idx:
                    A_matrix[monom_idx[k], ci] += float(v)

        # Product terms
        for idx, ((ci, cj), pp) in enumerate(zip(product_pairs, product_polys)):
            for k, v in pp.items():
                if v != 0 and k in monom_idx:
                    A_matrix[monom_idx[k], num_alpha + idx] += float(v)

        from scipy.optimize import linprog
        c = np.zeros(total_vars)
        result = linprog(c, A_eq=A_matrix, b_eq=g_vector,
                        bounds=[(0, None)] * total_vars,
                        method='highs')

        if result.success:
            print("SUCCESS with constant + product multipliers!")
            sigma = result.x
            for ci in range(num_alpha):
                if sigma[ci] > 1e-10:
                    print(f"  alpha[{constraint_names[ci]}] = {sigma[ci]:.6f}")
            for idx, (ci, cj) in enumerate(product_pairs):
                if sigma[num_alpha + idx] > 1e-10:
                    print(f"  beta[{constraint_names[ci]} * {constraint_names[cj]}] = {sigma[num_alpha + idx]:.6f}")
            return sigma, (product_pairs, num_alpha)
        else:
            print(f"INFEASIBLE: {result.message}")
            return None, None

    return None, None

# Try constant multipliers
result, info = try_with_multiplier_degree(0)

if result is None:
    # Try with products of pairs
    result, info = try_with_multiplier_degree(0, use_products=True)

if result is None:
    print("\n\nConstant and product multipliers failed.")
    print("Trying a more sophisticated approach...\n")

# Now try the key insight: use LINEAR polynomial multipliers on the key constraints
# h1 and h2 (the Cauchy-Schwarz constraints), with products for the rest.

def advanced_psatz():
    """
    Try: G = sum_i sigma_i * h_i + sum_{i<=j} beta_{ij} * h_i * h_j
              + sum_i (linear_poly_i) * h_i   (with linear_poly nonneg)

    But nonneg polynomial multipliers are hard. Instead, try:
    G = sum of terms of the form: (monomial)^2 * h_i
    which are manifestly nonneg since h_i >= 0 and (monomial)^2 >= 0.

    So: G = SOS_remainder + sum_i sum_j coeff_{ij} * (monomial_j)^2 * h_i
    where coeff_{ij} >= 0.
    """
    print(f"\n{'='*60}")
    print("Advanced: SOS multipliers (monomial^2 * h_i basis)")
    print(f"{'='*60}")

    # Generate basis: for each constraint h_i, and each monomial m with
    # deg(m^2 * h_i) <= G_degree = 4, generate m^2 * h_i as a column.
    # Also include squared monomials for the SOS remainder.

    nvars = 5
    columns = []  # list of (description, polynomial)

    # SOS remainder terms: m^2 for each monomial m with deg(m^2) <= 4
    sos_monoms = get_monomials_up_to_degree(nvars, 2)  # deg <= 2 so m^2 has deg <= 4
    for m in sos_monoms:
        m_poly = poly_const(1)
        for var_idx, exp in enumerate(m):
            for _ in range(exp):
                m_poly = poly_mul(m_poly, poly_var(var_idx))
        m_sq = poly_mul(m_poly, m_poly)
        if max(sum(k) for k, v in m_sq.items() if v != 0) <= G_degree:
            columns.append((f"SOS({m})", m_sq))

    # m^2 * h_i terms
    for ci, (h, cdeg) in enumerate(zip(constraints, constraint_degrees)):
        max_m_deg = (G_degree - cdeg) // 2  # so that deg(m^2 * h_i) <= G_degree
        if max_m_deg < 0:
            continue
        monoms = get_monomials_up_to_degree(nvars, max_m_deg)
        for m in monoms:
            m_poly = poly_const(1)
            for var_idx, exp in enumerate(m):
                for _ in range(exp):
                    m_poly = poly_mul(m_poly, poly_var(var_idx))
            m_sq = poly_mul(m_poly, m_poly)
            term = poly_mul(m_sq, h)
            deg = max((sum(k) for k, v in term.items() if v != 0), default=0)
            if deg <= G_degree:
                columns.append((f"{constraint_names[ci]}*({m})^2", term))

    print(f"Number of basis terms: {len(columns)}")

    # Collect all monomials
    all_monoms_set = set()
    for k, v in G.items():
        if v != 0:
            all_monoms_set.add(k)
    for desc, poly in columns:
        for k, v in poly.items():
            if v != 0:
                all_monoms_set.add(k)

    all_monoms = sorted(all_monoms_set)
    monom_idx = {m: i for i, m in enumerate(all_monoms)}
    num_monoms = len(all_monoms)
    num_cols = len(columns)
    print(f"Number of monomials: {num_monoms}")

    # Build matrix
    A_matrix = np.zeros((num_monoms, num_cols), dtype=np.float64)
    g_vector = np.zeros(num_monoms, dtype=np.float64)

    for k, v in G.items():
        if v != 0 and k in monom_idx:
            g_vector[monom_idx[k]] = float(v)

    for col_idx, (desc, poly) in enumerate(columns):
        for k, v in poly.items():
            if v != 0 and k in monom_idx:
                A_matrix[monom_idx[k], col_idx] += float(v)

    print(f"Matrix shape: {A_matrix.shape}")
    print(f"Matrix rank: {np.linalg.matrix_rank(A_matrix)}")

    from scipy.optimize import linprog

    c = np.zeros(num_cols)
    result = linprog(c, A_eq=A_matrix, b_eq=g_vector,
                    bounds=[(0, None)] * num_cols,
                    method='highs')

    if result.success:
        print("\nSUCCESS!")
        sigma = result.x
        active = [(i, sigma[i]) for i in range(num_cols) if sigma[i] > 1e-10]
        print(f"Active terms: {len(active)}")
        for i, val in sorted(active, key=lambda x: -x[1]):
            print(f"  {columns[i][0]}: {val:.8f}")

        # Try to rationalize
        rationalize(A_matrix, g_vector, sigma, columns, all_monoms, monom_idx)
        return True
    else:
        print(f"INFEASIBLE: {result.message}")
        return False

def rationalize(A_matrix, g_vector, sigma, columns, all_monoms, monom_idx):
    """Try to find exact rational coefficients."""
    print("\n--- Rationalization ---")

    # Identify active columns
    active_cols = [i for i in range(len(sigma)) if sigma[i] > 1e-10]
    print(f"Number of active columns: {len(active_cols)}")

    # Restrict to active columns and solve exactly
    A_active = A_matrix[:, active_cols]
    rank = np.linalg.matrix_rank(A_active)
    print(f"Active submatrix rank: {rank} (need {A_matrix.shape[0]})")

    if rank < A_matrix.shape[0]:
        print("Rank deficient - need more columns or different approach")
        # Try adding nearby columns
        return

    # Solve the reduced system with exact arithmetic
    from fractions import Fraction

    nrows, ncols = A_active.shape

    # Convert to Fraction matrix
    # First get the exact rational values from the polynomial construction
    A_rat = []
    for row_idx in range(nrows):
        row = []
        m = all_monoms[row_idx]
        for col_idx_local, col_idx_global in enumerate(active_cols):
            desc, poly = columns[col_idx_global]
            val = poly.get(m, Fraction(0))
            row.append(val)
        A_rat.append(row)

    g_rat = []
    for row_idx in range(nrows):
        m = all_monoms[row_idx]
        g_rat.append(G.get(m, Fraction(0)))

    print(f"\nSolving {nrows}x{ncols} rational system...")

    # Use Gaussian elimination to find a nonneg solution
    # First try: just solve the linear system (may not be nonneg)
    # Use numpy for a quick check
    try:
        x_float = np.linalg.lstsq(A_active, g_vector, rcond=None)[0]
        residual = np.max(np.abs(A_active @ x_float - g_vector))
        min_val = np.min(x_float)
        print(f"Least-squares residual: {residual:.2e}")
        print(f"Min coefficient: {min_val:.6f}")
        if min_val >= -1e-10:
            print("All coefficients nonneg (within tolerance)!")
        else:
            print("Some negative coefficients - need to use LP on active set")

            # Re-solve LP with just active columns
            from scipy.optimize import linprog
            c = np.zeros(len(active_cols))
            result2 = linprog(c, A_eq=A_active, b_eq=g_vector,
                            bounds=[(0, None)] * len(active_cols),
                            method='highs')
            if result2.success:
                x_float = result2.x
                print("LP on active set succeeded!")
            else:
                print("LP on active set failed")
                return
    except Exception as e:
        print(f"Numerical solve failed: {e}")
        return

    # Round to simple fractions
    print("\n--- Attempting exact rational certificate ---")
    active_with_vals = [(active_cols[i], x_float[i]) for i in range(len(active_cols))
                        if x_float[i] > 1e-10]
    print(f"Nonzero terms: {len(active_with_vals)}")

    for col_idx, val in sorted(active_with_vals, key=lambda x: -x[1]):
        # Try to find a nice fraction
        frac = Fraction(val).limit_denominator(10000)
        print(f"  {columns[col_idx][0]}: {val:.10f} ~ {frac}")

    # Try exact verification with the rounded fractions
    print("\n--- Exact verification ---")
    # Build the candidate certificate with rational approximations
    candidate = poly_zero()
    for col_idx, val in active_with_vals:
        frac = Fraction(val).limit_denominator(10000)
        desc, poly = columns[col_idx]
        candidate = poly_add(candidate, poly_scale(poly, frac))

    # Check if candidate == G
    diff = poly_sub(G, candidate)
    max_err = max((abs(v) for v in diff.values()), default=Fraction(0))
    print(f"Max monomial error after rationalization: {float(max_err):.2e}")

    if max_err == 0:
        print("EXACT MATCH! Certificate is verified.")
    else:
        print("Not exact - trying to refine...")
        # Show the error terms
        for k, v in sorted(diff.items()):
            if v != 0:
                print(f"  {k}: {v} ({float(v):.6e})")

        # Try a different approach: solve the exact rational system
        # using a subset of rows equal to the number of active columns
        print("\n--- Trying exact rational solve via basis selection ---")
        try_exact_rational_solve(A_rat, g_rat, active_cols, columns, all_monoms)


def try_exact_rational_solve(A_rat, g_rat, active_cols, columns, all_monoms):
    """Try to find exact rational solution by selecting a basis."""
    nrows = len(A_rat)
    ncols = len(active_cols)

    if ncols > nrows:
        print(f"Underdetermined: {ncols} vars, {nrows} equations")
        return

    # Gaussian elimination on the rational matrix
    # Augmented matrix [A | g]
    aug = []
    for i in range(nrows):
        row = list(A_rat[i]) + [g_rat[i]]
        aug.append(row)

    # Forward elimination
    pivot_rows = []
    col = 0
    for col in range(ncols):
        # Find pivot
        pivot = None
        for row in range(len(pivot_rows), nrows):
            if aug[row][col] != 0:
                pivot = row
                break
        if pivot is None:
            continue

        # Swap
        aug[len(pivot_rows)], aug[pivot] = aug[pivot], aug[len(pivot_rows)]
        pivot_row = len(pivot_rows)
        pivot_rows.append(pivot_row)

        # Eliminate
        for row in range(nrows):
            if row != pivot_row and aug[row][col] != 0:
                factor = Fraction(aug[row][col], aug[pivot_row][col])
                for j in range(ncols + 1):
                    aug[row][j] -= factor * aug[pivot_row][j]

    print(f"Pivot rows: {len(pivot_rows)}")

    if len(pivot_rows) < ncols:
        print("Rank deficient - system has free variables")
        # Still extract a solution by setting free variables to 0
        # ... this is complex, skip for now
        return

    # Back-substitute
    solution = [Fraction(0)] * ncols
    for i in range(len(pivot_rows) - 1, -1, -1):
        row = pivot_rows[i]
        # Find the pivot column for this row
        pcol = None
        for c in range(ncols):
            if aug[row][c] != 0:
                pcol = c
                break
        if pcol is None:
            continue
        val = aug[row][ncols]
        for c in range(pcol + 1, ncols):
            val -= aug[row][c] * solution[c]
        solution[pcol] = Fraction(val, aug[row][pcol])

    # Check if all nonneg
    all_nonneg = all(s >= 0 for s in solution)
    print(f"All nonneg: {all_nonneg}")
    if not all_nonneg:
        negs = [(i, solution[i]) for i in range(ncols) if solution[i] < 0]
        print(f"Negative entries: {len(negs)}")
        for i, v in negs:
            print(f"  {columns[active_cols[i]][0]}: {v}")

    # Verify
    print("\nVerifying solution...")
    candidate = poly_zero()
    for i in range(ncols):
        if solution[i] != 0:
            desc, poly = columns[active_cols[i]]
            candidate = poly_add(candidate, poly_scale(poly, solution[i]))
            if solution[i] > 0:
                print(f"  {solution[i]} * {desc}")

    diff = poly_sub(G, candidate)
    nonzero = {k: v for k, v in diff.items() if v != 0}
    if not nonzero:
        print("\nEXACT RATIONAL CERTIFICATE VERIFIED!")
    else:
        print(f"\nResidual has {len(nonzero)} nonzero terms")
        for k, v in sorted(nonzero.items()):
            print(f"  {k}: {v}")


# Run the advanced approach
success = advanced_psatz()

if not success:
    print("\n\nTrying extended approach with triple products...")

    def extended_psatz():
        """
        Add triple products of LINEAR constraints (h3..h11, which have degree 1).
        """
        print(f"\n{'='*60}")
        print("Extended: Include triple products of linear constraints")
        print(f"{'='*60}")

        nvars = 5
        columns = []

        # SOS terms (m^2, deg(m) <= 2)
        sos_monoms = get_monomials_up_to_degree(nvars, 2)
        for m in sos_monoms:
            m_poly = poly_const(1)
            for var_idx, exp in enumerate(m):
                for _ in range(exp):
                    m_poly = poly_mul(m_poly, poly_var(var_idx))
            m_sq = poly_mul(m_poly, m_poly)
            if max((sum(k) for k, v in m_sq.items() if v != 0), default=0) <= G_degree:
                columns.append((f"SOS({m})", m_sq))

        # m^2 * h_i
        for ci, (h, cdeg) in enumerate(zip(constraints, constraint_degrees)):
            max_m_deg = (G_degree - cdeg) // 2
            if max_m_deg < 0:
                continue
            monoms = get_monomials_up_to_degree(nvars, max_m_deg)
            for m in monoms:
                m_poly = poly_const(1)
                for var_idx, exp in enumerate(m):
                    for _ in range(exp):
                        m_poly = poly_mul(m_poly, poly_var(var_idx))
                m_sq = poly_mul(m_poly, m_poly)
                term = poly_mul(m_sq, h)
                deg = max((sum(k) for k, v in term.items() if v != 0), default=0)
                if deg <= G_degree:
                    columns.append((f"{constraint_names[ci]}*({m})^2", term))

        # Pairwise products h_i * h_j (with m^2 multiplier)
        for ci in range(len(constraints)):
            for cj in range(ci, len(constraints)):
                pair_deg = constraint_degrees[ci] + constraint_degrees[cj]
                if pair_deg > G_degree:
                    continue
                max_m_deg = (G_degree - pair_deg) // 2
                monoms = get_monomials_up_to_degree(nvars, max_m_deg)
                pair_poly = poly_mul(constraints[ci], constraints[cj])
                for m in monoms:
                    m_poly = poly_const(1)
                    for var_idx, exp in enumerate(m):
                        for _ in range(exp):
                            m_poly = poly_mul(m_poly, poly_var(var_idx))
                    m_sq = poly_mul(m_poly, m_poly)
                    term = poly_mul(m_sq, pair_poly)
                    deg = max((sum(k) for k, v in term.items() if v != 0), default=0)
                    if deg <= G_degree:
                        columns.append((f"{constraint_names[ci]}*{constraint_names[cj]}*({m})^2", term))

        # Triple products of degree-1 constraints (only if total degree <= 4)
        linear_constraints = [i for i in range(len(constraints)) if constraint_degrees[i] == 1]
        for ci in linear_constraints:
            for cj in linear_constraints:
                if cj < ci:
                    continue
                for ck in linear_constraints:
                    if ck < cj:
                        continue
                    triple_deg = 3
                    if triple_deg > G_degree:
                        continue
                    max_m_deg = (G_degree - triple_deg) // 2
                    if max_m_deg < 0:
                        continue
                    triple_poly = poly_mul(poly_mul(constraints[ci], constraints[cj]), constraints[ck])
                    monoms = get_monomials_up_to_degree(nvars, max_m_deg)
                    for m in monoms:
                        m_poly = poly_const(1)
                        for var_idx, exp in enumerate(m):
                            for _ in range(exp):
                                m_poly = poly_mul(m_poly, poly_var(var_idx))
                        m_sq = poly_mul(m_poly, m_poly)
                        term = poly_mul(m_sq, triple_poly)
                        deg = max((sum(k) for k, v in term.items() if v != 0), default=0)
                        if deg <= G_degree:
                            columns.append((f"{constraint_names[ci]}*{constraint_names[cj]}*{constraint_names[ck]}*({m})^2", term))

        # Quadruple products of degree-1 constraints
        for ci in linear_constraints:
            for cj in linear_constraints:
                if cj < ci:
                    continue
                for ck in linear_constraints:
                    if ck < cj:
                        continue
                    for cl in linear_constraints:
                        if cl < ck:
                            continue
                        quad_deg = 4
                        if quad_deg > G_degree:
                            continue
                        quad_poly = poly_mul(poly_mul(poly_mul(constraints[ci], constraints[cj]), constraints[ck]), constraints[cl])
                        deg = max((sum(k) for k, v in quad_poly.items() if v != 0), default=0)
                        if deg <= G_degree:
                            columns.append((f"4-prod:{constraint_names[ci]}*{constraint_names[cj]}*{constraint_names[ck]}*{constraint_names[cl]}", quad_poly))

        print(f"Total basis terms: {len(columns)}")

        # Collect monomials
        all_monoms_set = set()
        for k, v in G.items():
            if v != 0:
                all_monoms_set.add(k)
        for desc, poly in columns:
            for k, v in poly.items():
                if v != 0:
                    all_monoms_set.add(k)

        all_monoms = sorted(all_monoms_set)
        monom_idx = {m: i for i, m in enumerate(all_monoms)}
        num_monoms = len(all_monoms)
        num_cols = len(columns)
        print(f"Monomials: {num_monoms}")

        A_matrix = np.zeros((num_monoms, num_cols), dtype=np.float64)
        g_vector = np.zeros(num_monoms, dtype=np.float64)

        for k, v in G.items():
            if v != 0 and k in monom_idx:
                g_vector[monom_idx[k]] = float(v)

        for col_idx, (desc, poly) in enumerate(columns):
            for k, v in poly.items():
                if v != 0 and k in monom_idx:
                    A_matrix[monom_idx[k], col_idx] += float(v)

        print(f"Matrix: {A_matrix.shape}, rank: {np.linalg.matrix_rank(A_matrix)}")

        from scipy.optimize import linprog
        c = np.zeros(num_cols)
        result = linprog(c, A_eq=A_matrix, b_eq=g_vector,
                        bounds=[(0, None)] * num_cols,
                        method='highs')

        if result.success:
            print("\nSUCCESS!")
            sigma = result.x
            active = [(i, sigma[i]) for i in range(num_cols) if sigma[i] > 1e-10]
            print(f"Active terms: {len(active)}")
            for i, val in sorted(active, key=lambda x: -x[1])[:30]:
                print(f"  {columns[i][0]}: {val:.8f}")

            rationalize(A_matrix, g_vector, sigma, columns, all_monoms, monom_idx)
            return True
        else:
            print(f"INFEASIBLE: {result.message}")
            return False

    success = extended_psatz()

if not success:
    print("\n\nAll approaches failed. The inequality may need higher-degree multipliers.")
