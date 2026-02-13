"""
Find SOS decomposition for the RVW quadratic inequality:
  (b²-c²)*|p|*|X| + a²*c² - a²*b²*X² ≥ 0

Subject to:
  q² ≤ (a²+p)(c²+r) [CS+], q² ≤ (a²-p)(c²-r) [CS-]
  X = p + 2q + r, a² + b² = 1, |p| ≤ a², |r| ≤ c², c ≤ b

Case p≥0, X≥0: need (b²-c²)*p*X + a²c² - a²b²X² ≥ 0.

Try: Goal_neg = multiplier₁*CS+ + multiplier₂*CS- + Σ squares
where multipliers can be polynomials in the variables.
"""
import numpy as np
from numpy.linalg import lstsq

def eval_goal(a2, c2, p, q, r):
    b2 = 1 - a2
    X = p + 2*q + r
    return (b2 - c2)*p*X + a2*c2 - a2*b2*X**2

def eval_cs_plus(a2, c2, p, q, r):
    return (a2 + p)*(c2 + r) - q**2

def eval_cs_minus(a2, c2, p, q, r):
    return (a2 - p)*(c2 - r) - q**2

np.random.seed(42)
N = 1000
points = []
for _ in range(N*3):
    a = np.random.uniform(0.05, 0.99)
    a2 = a**2
    b2 = 1 - a2
    b = np.sqrt(b2)
    c = np.random.uniform(0, b)
    c2 = c**2
    p = np.random.uniform(0, a2)
    r = np.random.uniform(-c2, c2)
    q_max_plus = np.sqrt(max(0, (a2+p)*(c2+r)))
    q_max_minus = np.sqrt(max(0, (a2-p)*(c2-r)))
    q_max = min(q_max_plus, q_max_minus)
    q = np.random.uniform(-q_max, q_max)
    X = p + 2*q + r
    if X >= 0:
        points.append((a2, c2, p, q, r, X))
    if len(points) >= N:
        break

print(f"Generated {len(points)} valid points")

# S-procedure decomposition analysis
print("\n=== S-procedure with constant multipliers ===")
for pt in points[:5]:
    a2, c2, p, q, r, X = pt
    b2 = 1 - a2
    goal = eval_goal(a2, c2, p, q, r)
    v_sum = a2*c2 + p*r - q**2
    term1 = 4*a2*b2 * v_sum
    term2 = a2*c2*(2*a2-1)**2
    term3 = a2*b2*(p-r)**2
    L = p*(b2**2 - a2*b2 - c2) - 2*a2*b2*r
    print(f"  goal={goal:.6f} T1+T2+T3={term1+term2+term3:.6f} L*X={L*X:.6f}")

# Try decomposition with X-dependent multipliers
# Goal_neg = (α₀ + α₁X)*CS+ + (β₀ + β₁X)*CS- + squares
print("\n=== Linear-in-X multiplier fit ===")
A_mat = []
b_vec = []
for pt in points:
    a2, c2, p, q, r, X = pt
    cs_plus = eval_cs_plus(a2, c2, p, q, r)
    cs_minus = eval_cs_minus(a2, c2, p, q, r)
    goal = eval_goal(a2, c2, p, q, r)
    row = [cs_plus, cs_minus, X*cs_plus, X*cs_minus]
    A_mat.append(row)
    b_vec.append(goal)

A_mat = np.array(A_mat)
b_vec = np.array(b_vec)
coeffs, _, _, _ = lstsq(A_mat, b_vec, rcond=None)
print(f"Coefficients [α₀, β₀, α₁, β₁]: {coeffs}")
fitted = A_mat @ coeffs
residuals = b_vec - fitted
print(f"Min residual: {np.min(residuals):.8f}")
print(f"Max residual: {np.max(residuals):.8f}")

# Try extended multipliers: (a²-p)*CS+, (a²+p)*CS-, X*CS+, X*CS-, etc.
print("\n=== Extended multiplier fit ===")
A_mat2 = []
for pt in points:
    a2, c2, p, q, r, X = pt
    cs_p = eval_cs_plus(a2, c2, p, q, r)
    cs_m = eval_cs_minus(a2, c2, p, q, r)
    row = [(a2-p)*cs_p, (a2+p)*cs_m, X*cs_p, X*cs_m,
           (c2-r)*cs_p, (c2+r)*cs_m, p*cs_m, (a2-p)*X*cs_p]
    A_mat2.append(row)

A_mat2 = np.array(A_mat2)
coeffs2, _, _, _ = lstsq(A_mat2, b_vec, rcond=None)
print(f"Coefficients: {coeffs2}")
fitted2 = A_mat2 @ coeffs2
residuals2 = b_vec - fitted2
print(f"Min residual: {np.min(residuals2):.8f}")

# Try with square terms too
print("\n=== With square basis terms ===")
A_mat3 = []
for pt in points:
    a2, c2, p, q, r, X = pt
    b2 = 1-a2
    cs_p = eval_cs_plus(a2, c2, p, q, r)
    cs_m = eval_cs_minus(a2, c2, p, q, r)
    # Constraint terms
    terms = [cs_p, cs_m, X*cs_p, X*cs_m,
             (a2-p)*cs_p, (a2+p)*cs_m]
    # Square terms (each is ≥ 0)
    terms += [
        (a2*(2*a2-1))**2,      # a⁴(2a²-1)²
        (a2*b2)**2,            # a⁴b⁴
        p**2,                  # p²
        r**2,                  # r²
        (p-r)**2,              # (p-r)²
        c2**2,                 # c⁴
        (a2*c2)**2,            #
        (p*X),                 # p*X (nonneg since p≥0, X≥0)
        a2*b2*p**2,            # nonneg
        a2*c2*(2*a2-1)**2,     # nonneg
        a2*b2*(p-r)**2,        # nonneg
    ]
    A_mat3.append(terms)

A_mat3 = np.array(A_mat3)
coeffs3, _, _, _ = lstsq(A_mat3, b_vec, rcond=None)
fitted3 = A_mat3 @ coeffs3
residuals3 = b_vec - fitted3
print(f"Coefficients: {np.round(coeffs3, 6)}")
print(f"Min residual: {np.min(residuals3):.8f}")

# Check if all coefficients are nonneg (required for valid decomposition)
print(f"Any negative coefficients? {np.any(coeffs3 < -1e-6)}")

# Focused approach: try to verify the decomposition
# Goal_neg = 4a²b²*(sum_CS) + a²c²(2a²-1)² + a²b²(p-r)² + L*X
# where L*X is the problematic term.
# Can we absorb L*X using X * (some_nonneg)?
# L = p(b⁴-a²b²-c²) - 2a²b²r
# We want: X * |something| ≤ constant_terms
# Try: |L|*X ≤ some_multiple * (a²c²(2a²-1)² + a²b²(p-r)²)?
# Or use X*p*CS- ≥ 0 and X*(a²-p)*CS+ ≥ 0 to absorb L*X.
print("\n=== Targeted decomposition analysis ===")
max_ratio = 0
for pt in points:
    a2, c2, p, q, r, X = pt
    b2 = 1 - a2

    # The constant S-procedure terms
    sum_cs = a2*c2 + p*r - q**2
    T_const = 4*a2*b2*sum_cs + a2*c2*(2*a2-1)**2 + a2*b2*(p-r)**2
    L = p*(b2**2 - a2*b2 - c2) - 2*a2*b2*r

    goal = eval_goal(a2, c2, p, q, r)

    # goal = T_const + L*X
    # If L < 0, we need -L*X ≤ T_const
    if L < 0 and X > 1e-10:
        ratio = (-L*X) / T_const if T_const > 1e-15 else float('inf')
        if ratio > max_ratio:
            max_ratio = ratio
            worst = pt

print(f"Max ratio (-L*X / T_const): {max_ratio:.6f}")
if max_ratio > 0:
    a2, c2, p, q, r, X = worst
    b2 = 1-a2
    print(f"Worst point: a²={a2:.4f} c²={c2:.4f} p={p:.4f} q={q:.4f} r={r:.4f} X={X:.4f}")
    L = p*(b2**2 - a2*b2 - c2) - 2*a2*b2*r
    print(f"  L={L:.6f}")

    # Check if X*CS+_slack or X*CS-_slack can absorb the deficit
    cs_p = eval_cs_plus(a2, c2, p, q, r)
    cs_m = eval_cs_minus(a2, c2, p, q, r)
    print(f"  X*CS+ = {X*cs_p:.6f}")
    print(f"  X*CS- = {X*cs_m:.6f}")
    print(f"  -L*X = {-L*X:.6f}")
    print(f"  Does X*CS- absorb? {X*cs_m >= -L*X - 1e-10}")
