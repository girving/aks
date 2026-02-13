#!/usr/bin/env python3
"""
Analyze the RVW inequality and search for sum-of-squares proof.

Goal: X^2 * a^2 * b^2 <= (b^2 - c^2) * p * X + a^2 * c^2
where X = p + 2*q + r, b^2 = 1 - a^2

Rearranged (case p>=0, X>=0):
  a^2*b^2*X^2 - (b^2-c^2)*p*X - a^2*c^2 <= 0

Constraints:
1. a^2 + b^2 = 1 (implicitly: b^2 = 1 - a^2)
2. |p| <= a^2
3. |r| <= c^2
4. q^2 <= (a^2 + p)*(c^2 + r) [CS+]
5. q^2 <= (a^2 - p)*(c^2 - r) [CS-]
6. a^2*q^2 <= c^2*(a^4 - p^2) [weighted CS]
7. q^2 <= a^2*c^2 + p*r [sum of CS]
"""

import numpy as np
from sympy import *
import random

# Define symbolic variables
a, b, c, p, q, r, X = symbols('a b c p q r X', real=True, positive=True)

def test_numerically():
    """Test the inequality at random points satisfying constraints."""
    print("=" * 80)
    print("NUMERICAL VERIFICATION")
    print("=" * 80)

    violations = []
    test_cases = []

    for _ in range(10000):
        # Sample a, c with constraints
        a_val = random.uniform(0.1, 0.99)
        b_val = np.sqrt(1 - a_val**2)
        c_val = random.uniform(0, b_val)

        # Sample p, r within bounds
        p_val = random.uniform(-a_val**2, a_val**2)
        r_val = random.uniform(-c_val**2, c_val**2)

        # Sample q satisfying both CS constraints
        cs_plus = (a_val**2 + p_val) * (c_val**2 + r_val)
        cs_minus = (a_val**2 - p_val) * (c_val**2 - r_val)

        if cs_plus <= 0 or cs_minus <= 0:
            continue

        q_max = min(np.sqrt(cs_plus), np.sqrt(cs_minus))
        q_val = random.uniform(-q_max, q_max)

        X_val = p_val + 2*q_val + r_val

        # Focus on p>=0, X>=0 case
        if p_val < 0 or X_val < 0:
            continue

        # Compute LHS and RHS of inequality
        lhs = a_val**2 * b_val**2 * X_val**2
        rhs = (b_val**2 - c_val**2) * p_val * X_val + a_val**2 * c_val**2

        violation = lhs - rhs

        test_cases.append({
            'a': a_val, 'b': b_val, 'c': c_val,
            'p': p_val, 'q': q_val, 'r': r_val, 'X': X_val,
            'lhs': lhs, 'rhs': rhs, 'violation': violation
        })

        if violation > 1e-10:
            violations.append((a_val, b_val, c_val, p_val, q_val, r_val, X_val, violation))

    print(f"Tested {len(test_cases)} points (p>=0, X>=0)")
    print(f"Violations found: {len(violations)}")

    if violations:
        print("\nWorst violations:")
        violations.sort(key=lambda x: x[-1], reverse=True)
        for i, v in enumerate(violations[:5]):
            print(f"  {i+1}. a={v[0]:.4f}, b={v[1]:.4f}, c={v[2]:.4f}, "
                  f"p={v[3]:.4f}, q={v[4]:.4f}, r={v[5]:.4f}, X={v[6]:.4f}, "
                  f"violation={v[7]:.6e}")
    else:
        print("✓ All test cases satisfy the inequality!")

        # Show distribution of violation values
        viols = [tc['violation'] for tc in test_cases]
        print(f"\nViolation statistics:")
        print(f"  Min: {min(viols):.6e}")
        print(f"  Max: {max(viols):.6e}")
        print(f"  Mean: {np.mean(viols):.6e}")
        print(f"  Median: {np.median(viols):.6e}")

        # Show worst cases (closest to violation)
        test_cases.sort(key=lambda x: x['violation'], reverse=True)
        print(f"\nClosest cases to equality:")
        for i, tc in enumerate(test_cases[:5]):
            print(f"  {i+1}. a={tc['a']:.4f}, c={tc['c']:.4f}, "
                  f"p={tc['p']:.4f}, q={tc['q']:.4f}, r={tc['r']:.4f}, "
                  f"X={tc['X']:.4f}, slack={-tc['violation']:.6e}")

    return len(violations) == 0, test_cases

def analyze_symbolically():
    """Analyze the polynomial structure symbolically."""
    print("\n" + "=" * 80)
    print("SYMBOLIC ANALYSIS")
    print("=" * 80)

    # Substitute b^2 = 1 - a^2 and X = p + 2q + r
    goal_expr = a**2 * (1 - a**2) * X**2 - ((1 - a**2) - c**2) * p * X - a**2 * c**2
    goal_expr = expand(goal_expr.subs(X, p + 2*q + r))

    print("\nGoal (should be <= 0):")
    print(f"  {goal_expr}")

    # Define constraints (inequalities expressed as non-negative terms)
    constraints = {
        'bound_p': a**2 - p,  # p <= a^2
        'bound_-p': a**2 + p,  # -p <= a^2
        'bound_r': c**2 - r,  # r <= c^2
        'bound_-r': c**2 + r,  # -r <= c^2
        'CS+': (a**2 + p)*(c**2 + r) - q**2,
        'CS-': (a**2 - p)*(c**2 - r) - q**2,
        'weighted_CS': c**2*(a**4 - p**2) - a**2*q**2,
        'sum_CS': a**2*c**2 + p*r - q**2,
        'c_le_b': (1 - a**2) - c**2,  # c^2 <= b^2 = 1 - a^2
    }

    print("\nConstraints (all >= 0):")
    for name, expr in constraints.items():
        print(f"  {name}: {expr}")

    # Expand constraints
    expanded_constraints = {name: expand(expr) for name, expr in constraints.items()}

    return goal_expr, expanded_constraints

def search_sos_decomposition(goal_expr, constraints, test_cases):
    """Search for sum-of-squares proof using numerical optimization hints."""
    print("\n" + "=" * 80)
    print("SUM-OF-SQUARES PROOF SEARCH")
    print("=" * 80)

    # We want: -goal = sum(lambda_i * constraint_i) + sum(s_j^2)
    # Start by looking at extreme cases from numerical tests

    print("\nAnalyzing structure at extreme points...")

    # Look at cases where violation is close to 0 (tight constraints)
    tight_cases = sorted(test_cases, key=lambda x: abs(x['violation']))[:10]

    print("\nTightest cases:")
    for i, tc in enumerate(tight_cases[:5]):
        print(f"\n  Case {i+1}: a={tc['a']:.4f}, c={tc['c']:.4f}, "
              f"p={tc['p']:.4f}, q={tc['q']:.4f}, r={tc['r']:.4f}")

        # Evaluate which constraints are tight
        a_val, c_val, p_val, q_val, r_val = tc['a'], tc['c'], tc['p'], tc['q'], tc['r']
        b_val = tc['b']

        print(f"    Constraint tightness:")
        print(f"      bound_p:  {a_val**2 - p_val:.6e}")
        print(f"      bound_r:  {c_val**2 - r_val:.6e}")

        cs_plus = (a_val**2 + p_val)*(c_val**2 + r_val) - q_val**2
        cs_minus = (a_val**2 - p_val)*(c_val**2 - r_val) - q_val**2
        print(f"      CS+:      {cs_plus:.6e}")
        print(f"      CS-:      {cs_minus:.6e}")

        weighted = c_val**2*(a_val**4 - p_val**2) - a_val**2*q_val**2
        sum_cs = a_val**2*c_val**2 + p_val*r_val - q_val**2
        print(f"      weighted: {weighted:.6e}")
        print(f"      sum_CS:   {sum_cs:.6e}")
        print(f"      c_le_b:   {b_val**2 - c_val**2:.6e}")

def attempt_manual_sos():
    """Try specific manual SOS decompositions based on structure."""
    print("\n" + "=" * 80)
    print("MANUAL SOS ATTEMPTS")
    print("=" * 80)

    # Strategy 1: Focus on the quadratic form in X
    print("\nStrategy 1: Quadratic in X")
    print("Goal: a²(1-a²)X² - (1-a²-c²)pX - a²c² <= 0")
    print("This is quadratic in X with:")
    print("  A = a²(1-a²)")
    print("  B = -(1-a²-c²)p")
    print("  C = -a²c²")
    print("For AX² + BX + C <= 0, need discriminant B² - 4AC >= 0")
    print("  B² - 4AC = [(1-a²-c²)p]² + 4a²(1-a²)·a²c²")
    print("           = (1-a²-c²)²p² + 4a⁴(1-a²)c²")

    # Strategy 2: Factor as product
    print("\nStrategy 2: Try to factor goal")
    X_sym = p + 2*q + r
    goal = a**2 * (1-a**2) * X_sym**2 - ((1-a**2) - c**2)*p*X_sym - a**2*c**2
    goal_expanded = expand(goal)
    print(f"  Expanded goal: {goal_expanded}")

    # Try factoring
    from sympy import factor, collect
    print(f"  Factored: {factor(goal_expanded)}")

    # Strategy 3: Examine coefficients of different monomials
    print("\nStrategy 3: Monomial analysis")
    goal_poly = Poly(goal_expanded, [a, c, p, q, r])
    print("  Coefficients by monomial:")
    for monom, coeff in sorted(goal_poly.as_dict().items(),
                               key=lambda x: sum(x[0]), reverse=True):
        if coeff != 0:
            monom_str = '*'.join([f"{var}^{exp}" if exp > 1 else var
                                 for var, exp in zip(['a', 'c', 'p', 'q', 'r'], monom)
                                 if exp > 0])
            if not monom_str:
                monom_str = "1"
            print(f"    {monom_str}: {coeff}")

    # Strategy 4: Look for completion patterns
    print("\nStrategy 4: Completion of squares patterns")
    print("Note: X² = (p + 2q + r)² = p² + 4q² + r² + 4pq + 4qr + 2pr")
    print("      q² appears with coefficient 4a²(1-a²)")
    print("      This suggests combining with CS constraints that bound q²")

def main():
    random.seed(42)
    np.random.seed(42)

    print("RVW Inequality Analysis")
    print("=" * 80)

    # Step 1: Numerical verification
    is_valid, test_cases = test_numerically()

    if not is_valid:
        print("\n⚠ WARNING: Inequality violated numerically! Check formulation.")
        return

    # Step 2: Symbolic analysis
    goal_expr, constraints = analyze_symbolically()

    # Step 3: Search for SOS decomposition
    search_sos_decomposition(goal_expr, constraints, test_cases)

    # Step 4: Manual attempts
    attempt_manual_sos()

    print("\n" + "=" * 80)
    print("CONCLUSIONS")
    print("=" * 80)
    print("The inequality appears numerically valid.")
    print("Key observations:")
    print("  1. The goal is quadratic in X = p + 2q + r")
    print("  2. Tightest when certain CS constraints are active")
    print("  3. The term 4a²(1-a²)q² from X² expansion suggests")
    print("     combining with q² bounds from CS constraints")
    print("\nNext steps:")
    print("  - Try Positivstellensatz with computer algebra (SageMath/SOSTOOLS)")
    print("  - Look for geometric interpretation (reflection/projection)")
    print("  - Check RVW paper Section 4.2 for proof hints")

if __name__ == '__main__':
    main()
