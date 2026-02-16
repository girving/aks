"""Find SOS decompositions for the RVW vertex inequalities.

After concavity reduction, the proof of rvw_quadratic_ineq reduces to checking
G = AC + (B-C)*p*|X| - AB*X² ≥ 0 at four vertices of the feasible set:

Vertex 1: q=0, r=C  →  X = p+C
Vertex 2: q=0, r=-C →  X = p-C
Vertex 3+: both CS tight, q>0 →  X = p(A-C)/A + 2√(C(A²-p²)/A)
Vertex 3-: both CS tight, q<0 →  X = p(A-C)/A - 2√(C(A²-p²)/A)

Vertices 1,2 are polynomial. Vertex 3 uses squaring to eliminate √.
"""
import sympy as sp

A, B, C, p = sp.symbols('A B C p', nonneg=True)

# Constraints: A+B=1, 0≤C≤B, 0≤p≤A, A>0, B>0
# We substitute B = 1-A throughout.
B_val = 1 - A

def check_vertex(name, G_expr):
    """Check if G ≥ 0 and try to find a proof."""
    G = sp.expand(G_expr.subs(B, B_val))
    print(f"\n=== {name} ===")
    print(f"G = {G}")

    # Check at tight point: A=1/2, C=1/2, p=1/2
    val = G.subs([(A, sp.Rational(1,2)), (C, sp.Rational(1,2)), (p, sp.Rational(1,2))])
    print(f"  At tight point (A=C=p=1/2): G = {val}")

    # Check at other points
    for (a_val, c_val, p_val) in [(0.5, 0.2, 0.3), (0.9, 0.05, 0.1), (0.3, 0.1, 0.2), (0.1, 0.05, 0.05)]:
        if p_val <= a_val and c_val <= 1 - a_val:
            val = float(G.subs([(A, a_val), (C, c_val), (p, p_val)]))
            print(f"  At A={a_val}, C={c_val}, p={p_val}: G = {val:.6f}")

    # Try to factor or find SOS
    poly = sp.Poly(G, A, C, p)
    print(f"  Degree: {poly.total_degree()}, Terms: {len(poly.as_dict())}")
    return G

# Vertex 1: q=0, r=C, X=p+C (p≥0 so X≥0)
G1 = A*C + (B-C)*p*(p+C) - A*B*(p+C)**2
print("Vertex 1: q=0, r=C, X=p+C")
g1 = check_vertex("Vertex 1 (X=p+C)", G1)

# Vertex 2a: q=0, r=-C, X=p-C, p≥C (so |X|=p-C)
G2a = A*C + (B-C)*p*(p-C) - A*B*(p-C)**2
print("\nVertex 2a: q=0, r=-C, p≥C, X=p-C")
g2a = check_vertex("Vertex 2a (X=p-C, p≥C)", G2a)

# Vertex 2b: q=0, r=-C, X=C-p, p<C (so |X|=C-p)
G2b = A*C + (B-C)*p*(C-p) - A*B*(C-p)**2
print("\nVertex 2b: q=0, r=-C, p<C, X=C-p")
g2b = check_vertex("Vertex 2b (X=C-p, p<C)", G2b)

# Vertex 3: Both CS tight. r=-pC/A, q²=C(A²-p²)/A.
# X = p(A-C)/A + 2q. G = R + S*q where:
# R = γ₀ - 4AB*q² = γ₀ - 4AB*C*(A²-p²)/A
# S = 2*(B-C)*p - 4*A*B*p*(A-C)/A = 2*p*(1-2A)*(B+C)
# G ≥ 0 iff R + S*q ≥ 0 (with q = ±√(C(A²-p²)/A))
#
# Need: R ≥ 0 AND R² ≥ S²*C*(A²-p²)/A
# (The second ensures |S*q| ≤ R when R ≥ 0.)

# Compute R and S²*Q² symbolically
u = p*(A-C)/A  # = X when q=0 at the CS vertex
gamma0 = A*C + (B-C)*p*u - A*B*u**2
Q2 = C*(A**2 - p**2)/A  # q² at both CS tight
R = gamma0 - 4*A*B*Q2
S = 2*p*(1-2*A)*(B+C)
S2Q2 = S**2 * Q2  # = S²*q²

print("\n=== Vertex 3: Both CS tight ===")
R_expanded = sp.expand(R.subs(B, B_val))
S2Q2_expanded = sp.expand(S2Q2.subs(B, B_val))
print(f"R = {R_expanded}")
print(f"S²Q² = {S2Q2_expanded}")

# Check R ≥ 0
print("\n--- R ≥ 0 ---")
g3_R = check_vertex("R (≥ 0)", R)

# Check R² - S²Q² ≥ 0 (after multiplying by A to clear denominator)
# Actually need A*R² ≥ S²*C*(A²-p²) but let me compute R²-S²Q² directly
D = sp.expand((R**2 - S2Q2).subs(B, B_val))
# Multiply by A² to clear denominators
D_cleared = sp.expand(D * A**2)
print(f"\n--- A²(R² - S²Q²) ---")
print(f"D = {D_cleared}")
poly_D = sp.Poly(D_cleared, A, C, p)
print(f"  Degree: {poly_D.total_degree()}, Terms: {len(poly_D.as_dict())}")

# Check D ≥ 0 numerically
for (a_val, c_val, p_val) in [(0.5, 0.2, 0.3), (0.9, 0.05, 0.1), (0.3, 0.1, 0.2),
                               (0.5, 0.5, 0.5), (0.5, 0.5, 0.0), (0.1, 0.05, 0.05),
                               (0.8, 0.1, 0.7), (0.6, 0.15, 0.3)]:
    if p_val <= a_val and c_val <= 1 - a_val:
        val = float(D_cleared.subs([(A, a_val), (C, c_val), (p, p_val)]))
        print(f"  At A={a_val}, C={c_val}, p={p_val}: D = {val:.8f}")

# Now try to factor D_cleared
print("\n--- Factoring D_cleared ---")
# D_cleared is a polynomial in A, C, p. Try to express as SOS.
# First let's see the structure
for monom, coeff in sorted(poly_D.as_dict().items()):
    a_exp, c_exp, p_exp = monom
    print(f"  A^{a_exp} C^{c_exp} p^{p_exp}: {coeff}")

# Try substitution p = A*mu (where 0 ≤ mu ≤ 1)
mu = sp.Symbol('mu', nonneg=True)
D_mu = sp.expand(D_cleared.subs(p, A*mu))
print(f"\n--- D with p=A*mu ---")
print(f"D = {D_mu}")

# Factor out common powers of A
D_mu_poly = sp.Poly(D_mu, A, C, mu)
print(f"  Degree: {D_mu_poly.total_degree()}, Terms: {len(D_mu_poly.as_dict())}")
