#!/usr/bin/env python3
"""
Search for specific sum-of-squares decomposition of the RVW inequality.

Try to express: -goal = sum(lambda_i * constraint_i) + sum(s_j^2)
"""

import numpy as np
from sympy import *
import itertools

# Define symbolic variables
a, c, p, q, r = symbols('a c p q r', real=True)

def setup_problem():
    """Set up the goal and constraints."""
    # Goal: a²(1-a²)X² - (1-a²-c²)pX - a²c² with X = p + 2q + r
    X = p + 2*q + r
    goal = a**2 * (1-a**2) * X**2 - ((1-a**2) - c**2)*p*X - a**2*c**2
    goal = expand(goal)

    # Constraints (should all be >= 0)
    constraints = {
        'bound_p': a**2 - p,
        'bound_r': c**2 - r,
        'CS+': (a**2 + p)*(c**2 + r) - q**2,
        'CS-': (a**2 - p)*(c**2 - r) - q**2,
        'weighted_CS': c**2*(a**4 - p**2) - a**2*q**2,
        'sum_CS': a**2*c**2 + p*r - q**2,
        'c_le_b': (1 - a**2) - c**2,
    }

    # Expand all constraints
    constraints = {name: expand(expr) for name, expr in constraints.items()}

    return goal, constraints

def collect_monomials(*polys):
    """Collect all monomials appearing in the given polynomials."""
    monoms = set()
    for poly in polys:
        p = Poly(poly, [a, c, p, q, r])
        monoms.update(p.as_dict().keys())
    return sorted(monoms, key=lambda x: (sum(x), x), reverse=True)

def try_linear_combination(goal, constraints, lambdas):
    """
    Try a specific linear combination: -goal - sum(lambda_i * constraint_i).
    Return the residual.
    """
    residual = -goal
    for name, lam in lambdas.items():
        if lam != 0:
            residual = expand(residual - lam * constraints[name])
    return residual

def check_if_sos_candidates(residual):
    """
    Check if residual has structure suggesting it could be a SOS.
    A necessary condition: all coefficients of even-degree monomials must be <= 0.
    """
    poly = Poly(residual, [a, c, p, q, r])
    coeff_dict = poly.as_dict()

    # Check if it could be a SOS (necessary: -(residual) should have non-negative diagonal)
    neg_residual = -residual
    neg_poly = Poly(neg_residual, [a, c, p, q, r])
    neg_coeff = neg_poly.as_dict()

    # Check pure squares (these form the "diagonal" of the Gram matrix)
    pure_squares = {monom: coeff for monom, coeff in neg_coeff.items()
                   if all(exp % 2 == 0 for exp in monom)}

    all_nonneg = all(coeff >= 0 for coeff in pure_squares.values())

    return all_nonneg, pure_squares

def main():
    print("=" * 80)
    print("SUM-OF-SQUARES DECOMPOSITION SEARCH")
    print("=" * 80)

    goal, constraints = setup_problem()

    print("\nGoal (should be <= 0):")
    print(f"  {goal}")

    print("\nConstraints:")
    for name, expr in constraints.items():
        print(f"  {name}: {expr}")

    # Strategy: Try different combinations of constraints
    print("\n" + "=" * 80)
    print("TRYING SPECIFIC COMBINATIONS")
    print("=" * 80)

    # Combination 1: Focus on q² terms
    # The goal has -4a⁴q² + 4a²q² = 4a²(1-a²)q²
    # Use weighted_CS: c²(a⁴ - p²) - a²q² >= 0
    # This gives: a²q² <= c²(a⁴ - p²)
    print("\n--- Combination 1: Use weighted_CS to eliminate q² ---")
    lambdas1 = {'weighted_CS': 4 * (1 - a**2)}
    residual1 = try_linear_combination(goal, constraints, lambdas1)
    print(f"Residual: {residual1}")
    is_candidate, squares = check_if_sos_candidates(residual1)
    print(f"Could be SOS: {is_candidate}")
    if is_candidate:
        print(f"  Pure square terms in -residual: {squares}")

    # Combination 2: Use CS+ or CS-
    print("\n--- Combination 2: Use CS+ with coefficient 4a²(1-a²) ---")
    lambdas2 = {'CS+': 4 * a**2 * (1 - a**2)}
    residual2 = try_linear_combination(goal, constraints, lambdas2)
    residual2_simple = simplify(residual2)
    print(f"Residual: {residual2_simple}")
    is_candidate, squares = check_if_sos_candidates(residual2_simple)
    print(f"Could be SOS: {is_candidate}")

    # Combination 3: Use sum_CS
    print("\n--- Combination 3: Use sum_CS with coefficient 4a²(1-a²) ---")
    lambdas3 = {'sum_CS': 4 * a**2 * (1 - a**2)}
    residual3 = try_linear_combination(goal, constraints, lambdas3)
    residual3_simple = simplify(residual3)
    print(f"Residual: {residual3_simple}")
    is_candidate, squares = check_if_sos_candidates(residual3_simple)
    print(f"Could be SOS: {is_candidate}")

    # Combination 4: Multiple constraints
    print("\n--- Combination 4: Combine multiple constraints ---")
    # Try: use sum_CS for q², and bound_r for r terms
    lambdas4 = {
        'sum_CS': 4 * a**2 * (1 - a**2),
        'c_le_b': a**2 * c**2,  # To eliminate -a²c² term
    }
    residual4 = try_linear_combination(goal, constraints, lambdas4)
    residual4_simple = simplify(residual4)
    print(f"Residual: {residual4_simple}")
    is_candidate, squares = check_if_sos_candidates(residual4_simple)
    print(f"Could be SOS: {is_candidate}")
    if is_candidate:
        print("  Analyzing structure...")
        poly = Poly(residual4_simple, [a, c, p, q, r])
        print(f"  Degree: {poly.total_degree()}")
        print(f"  Terms: {len(poly.as_dict())}")

    # Combination 5: Try to eliminate the a²c² term first
    print("\n--- Combination 5: Eliminate -a²c² using c_le_b ---")
    # -a²c² + lambda*(1-a²-c²) = -a²c² + lambda - lambda*a² - lambda*c²
    # To cancel -a²c², need: lambda*c² = a²c², so lambda = a²
    lambdas5 = {'c_le_b': a**2}
    residual5 = try_linear_combination(goal, constraints, lambdas5)
    print(f"Residual: {residual5}")
    print("Now try to handle q² terms...")

    # Add weighted_CS or sum_CS to residual5
    lambdas5b = {
        'c_le_b': a**2,
        'sum_CS': 4 * a**2 * (1 - a**2),
    }
    residual5b = try_linear_combination(goal, constraints, lambdas5b)
    residual5b_simple = simplify(residual5b)
    print(f"After adding sum_CS: {residual5b_simple}")
    is_candidate, squares = check_if_sos_candidates(residual5b_simple)
    print(f"Could be SOS: {is_candidate}")

    # Try expanding as (p + 2q + r)² structure
    print("\n" + "=" * 80)
    print("STRUCTURAL ANALYSIS")
    print("=" * 80)

    # Look at the structure modulo X²
    print("\nNote: X = p + 2q + r")
    print("X² = p² + 4q² + r² + 4pq + 4qr + 2pr")
    print("\nThe goal is: a²(1-a²)X² - (1-a²-c²)pX - a²c²")
    print("Let's denote b² = 1-a² for clarity")
    print("Goal = a²b²X² - (b²-c²)pX - a²c²")
    print("\nThis is a quadratic in X:")
    print("  a²b²X² - (b²-c²)pX - a²c²")
    print("\nFor this to be <= 0 for all valid X, we need:")
    print("  1. Either it factors as -(X - r₁)(X - r₂) with appropriate signs")
    print("  2. Or the quadratic form is dominated by constraint terms")

    # Try completing the square in X
    print("\n--- Completing the square in X ---")
    print("a²b²X² - (b²-c²)pX - a²c²")
    print("= a²b²[X² - ((b²-c²)p)/(a²b²)X] - a²c²")
    print("= a²b²[X - (b²-c²)p/(2a²b²)]² - a²b²[(b²-c²)p/(2a²b²)]² - a²c²")
    print("= a²b²[X - (b²-c²)p/(2a²b²)]² - [(b²-c²)²p²]/(4b²) - a²c²")
    print("\nFor this to be <= 0, need:")
    print("  a²b²[X - (b²-c²)p/(2a²b²)]² <= [(b²-c²)²p²]/(4b²) + a²c²")

    # Analyze the bound on X
    print("\n--- Bounds on X from CS constraints ---")
    print("CS+: q² <= (a² + p)(c² + r)")
    print("CS-: q² <= (a² - p)(c² - r)")
    print("sum_CS: q² <= a²c² + pr")
    print("\nThese bound q in terms of p, r")
    print("Combined with bounds on p, r, they constrain X = p + 2q + r")

    # Try a specific structure: (aX - f(p,r,c))²
    print("\n--- Looking for square structure ---")
    print("Could -residual after constraint elimination be a perfect square?")

    # Final attempt: systematic search
    print("\n" + "=" * 80)
    print("SYSTEMATIC SEARCH (small coefficients)")
    print("=" * 80)

    # Try small integer/rational combinations
    candidates = []
    for lam_sumCS in [0, 1, 2, 4*a**2*(1-a**2), 4*(1-a**2)]:
        for lam_c_le_b in [0, a**2, c**2, 1]:
            for lam_weighted in [0, 4*(1-a**2)]:
                lambdas = {}
                if lam_sumCS != 0:
                    lambdas['sum_CS'] = lam_sumCS
                if lam_c_le_b != 0:
                    lambdas['c_le_b'] = lam_c_le_b
                if lam_weighted != 0:
                    lambdas['weighted_CS'] = lam_weighted

                if not lambdas:
                    continue

                residual = try_linear_combination(goal, constraints, lambdas)
                is_cand, _ = check_if_sos_candidates(residual)

                if is_cand:
                    candidates.append((lambdas, residual))

    print(f"Found {len(candidates)} candidate combinations")
    for i, (lams, res) in enumerate(candidates[:5]):
        print(f"\nCandidate {i+1}:")
        print(f"  Lambdas: {lams}")
        print(f"  Residual: {simplify(res)}")

if __name__ == '__main__':
    main()
