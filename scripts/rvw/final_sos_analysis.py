#!/usr/bin/env python3
"""
Final analysis: Find the exact SOS decomposition by working backwards
from what we know must be true.

Since the inequality holds, there MUST exist a decomposition:
  -goal = sum(lambda_i * constraint_i) + R
where R is non-negative (ideally a sum of squares).
"""

import numpy as np
from sympy import *

def main():
    print("=" * 80)
    print("FINAL SOS ANALYSIS")
    print("=" * 80)

    a, c, p, q, r = symbols('a c p q r', real=True)
    b_sq = 1 - a**2

    # Goal (should be <= 0)
    X = p + 2*q + r
    goal = a**2 * b_sq * X**2 - (b_sq - c**2)*p*X - a**2*c**2
    goal = expand(goal)

    print("\nGoal (expanded):")
    print(f"  {goal}")

    # Key constraint for elimination
    sum_CS = a**2*c**2 + p*r - q**2

    print("\n" + "-" * 80)
    print("STRATEGY: Eliminate q² using sum_CS")
    print("-" * 80)

    print("\nFrom sum_CS: q² ≤ a²c² + pr")
    print("Equivalently: q² - a²c² - pr ≤ 0")
    print("So: a²c² + pr - q² ≥ 0")

    print("\nThe coefficient of q² in goal is:")
    goal_poly = Poly(goal, [q])
    q2_coeff = goal_poly.nth(2)
    print(f"  {q2_coeff} = {expand(q2_coeff)}")
    print(f"  = 4a²(1-a²) = 4a²b²")

    print("\nSo we use: 4a²b² · (a²c² + pr - q²)")
    print("This eliminates the q² term and adds: 4a²b²(a²c² + pr)")

    residual = expand(goal + 4*a**2*b_sq*(sum_CS))
    print(f"\nResidual after using sum_CS:")
    print(f"  {residual}")

    # Simplify
    residual = expand(residual.subs(b_sq, 1 - a**2))
    print(f"\nSimplified (with b² = 1-a²):")
    residual_simple = simplify(residual)
    print(f"  {residual_simple}")

    # Factor if possible
    print(f"\nAttempting to factor:")
    residual_factored = factor(residual_simple)
    print(f"  {residual_factored}")

    # Check structure
    print("\n" + "-" * 80)
    print("ANALYZING RESIDUAL STRUCTURE")
    print("-" * 80)

    # Collect terms
    residual_poly = Poly(residual, [a, c, p, r])
    coeffs = residual_poly.as_dict()

    print(f"\nResidual has {len(coeffs)} terms")
    print("Coefficients by monomial (showing top terms):")

    # Sort by monomial degree, not coefficient magnitude (which may be symbolic)
    sorted_coeffs = sorted(coeffs.items(), key=lambda x: (sum(x[0]), x[0]), reverse=True)
    for monom, coeff in sorted_coeffs[:15]:
        monom_str = '*'.join([f"{var}^{exp}" if exp > 1 else var
                             for var, exp in zip(['a', 'c', 'p', 'r'], monom)
                             if exp > 0])
        if not monom_str:
            monom_str = "1"
        print(f"  {monom_str:20s}: {coeff}")

    # Try to identify if it's a sum of squares
    print("\n" + "-" * 80)
    print("LOOKING FOR SQUARE STRUCTURE")
    print("-" * 80)

    # Check if residual is non-positive
    print("\nNumerically checking sign of residual...")

    import random
    random.seed(42)

    signs = {'positive': 0, 'negative': 0, 'zero': 0}

    for _ in range(1000):
        a_val = random.uniform(0.1, 0.99)
        b_val = np.sqrt(1 - a_val**2)
        c_val = random.uniform(0, b_val)
        p_val = random.uniform(-a_val**2, a_val**2)
        r_val = random.uniform(-c_val**2, c_val**2)

        # Check sum_CS constraint
        sum_cs_val = a_val**2 * c_val**2 + p_val * r_val
        if sum_cs_val <= 0:
            continue

        q_val = random.uniform(-np.sqrt(sum_cs_val), np.sqrt(sum_cs_val))

        # Evaluate residual
        res_val = residual.subs([
            (a, a_val), (c, c_val), (p, p_val), (q, q_val), (r, r_val)
        ])

        if res_val > 1e-10:
            signs['positive'] += 1
        elif res_val < -1e-10:
            signs['negative'] += 1
        else:
            signs['zero'] += 1

    print(f"  Positive: {signs['positive']}")
    print(f"  Negative: {signs['negative']}")
    print(f"  Zero: {signs['zero']}")

    if signs['positive'] > 0:
        print("\n⚠ Residual is sometimes POSITIVE!")
        print("This means sum_CS alone is not sufficient.")
        print("We need additional constraints.")
    else:
        print("\n✓ Residual is always non-positive!")
        print("The constraint sum_CS is sufficient!")

    # Try adding another constraint
    print("\n" + "=" * 80)
    print("TRYING ADDITIONAL CONSTRAINTS")
    print("=" * 80)

    c_le_b = b_sq - c**2

    print("\nTry adding: λ · (b² - c²) = λ · (1 - a² - c²)")
    print("to eliminate the a²c² constant term...")

    # We have a constant term in residual, find it
    const_term = coeffs.get((0, 0, 0, 0), 0)
    print(f"\nConstant term in residual: {const_term}")

    if const_term != 0:
        # Find coefficient for c_le_b to cancel constant
        # residual has terms in a, c
        # Let's examine the a²c² coefficient more carefully
        pass

    print("\nAlternative: Try multiple constraints simultaneously")

    # Use both sum_CS and c_le_b
    lambda_sum_cs = 4*a**2*(1-a**2)
    lambda_c_le_b = a**2

    combo_residual = expand(
        goal +
        lambda_sum_cs * sum_CS +
        lambda_c_le_b * c_le_b
    )
    combo_residual = expand(combo_residual.subs(b_sq, 1-a**2))

    print(f"\nResidual with sum_CS and c_le_b:")
    combo_simple = simplify(combo_residual)
    print(f"  {combo_simple}")

    # Check sign
    signs2 = {'positive': 0, 'negative': 0, 'zero': 0}

    for _ in range(1000):
        a_val = random.uniform(0.1, 0.99)
        c_val = random.uniform(0, np.sqrt(1 - a_val**2))
        p_val = random.uniform(-a_val**2, a_val**2)
        r_val = random.uniform(-c_val**2, c_val**2)

        sum_cs_val = a_val**2 * c_val**2 + p_val * r_val
        if sum_cs_val <= 0:
            continue

        q_val = random.uniform(-np.sqrt(sum_cs_val), np.sqrt(sum_cs_val))

        res_val = combo_residual.subs([
            (a, a_val), (c, c_val), (p, p_val), (q, q_val), (r, r_val)
        ])

        if res_val > 1e-10:
            signs2['positive'] += 1
        elif res_val < -1e-10:
            signs2['negative'] += 1
        else:
            signs2['zero'] += 1

    print(f"\n  Positive: {signs2['positive']}")
    print(f"  Negative: {signs2['negative']}")
    print(f"  Zero: {signs2['zero']}")

    if signs2['positive'] == 0:
        print("\n✓ Combined constraints work!")

        # Try to express residual as sum of squares
        print("\n" + "-" * 80)
        print("SEARCHING FOR SOS REPRESENTATION OF RESIDUAL")
        print("-" * 80)

        print(f"\nResidual to decompose:")
        print(f"  {combo_simple}")

        # Try to complete squares
        # The residual is a polynomial in a, c, p, r
        # Look for patterns like (...)²

if __name__ == '__main__':
    main()
