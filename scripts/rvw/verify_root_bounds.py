#!/usr/bin/env python3
"""
Verify that X always lies between the roots of the quadratic.

We need to prove:
  X₋ ≤ X ≤ X₊

where X₋, X₊ are the roots of a²b²X² - (b²-c²)pX - a²c² = 0
and X = p + 2q + r with CS constraints on q.
"""

import numpy as np
from sympy import *

def compute_bounds():
    """Compute explicit bounds on X from CS constraints."""
    print("=" * 80)
    print("EXPLICIT COMPUTATION OF X BOUNDS")
    print("=" * 80)

    a, c, p, r = symbols('a c p r', real=True, positive=True)

    print("\nGiven constraints (case p ≥ 0):")
    print("  0 ≤ p ≤ a²")
    print("  -c² ≤ r ≤ c²")
    print("  q² ≤ (a² + p)(c² + r)  [CS+]")
    print("  q² ≤ (a² - p)(c² - r)  [CS-]")
    print("  q² ≤ a²c² + pr         [sum_CS]")

    print("\n" + "-" * 80)
    print("UPPER BOUND ON X")
    print("-" * 80)

    print("\nX = p + 2q + r is maximized when q, r are maximized.")
    print("\nFrom CS+, q is maximized when r = c²:")
    print("  q_max² = (a² + p)(c² + c²) = 2(a² + p)c²")
    print("  q_max = c√[2(a² + p)]")

    print("\nSo X_max = p + 2c√[2(a² + p)] + c²")

    # Quadratic root X₊
    print("\nThe upper root of the quadratic is:")
    print("  X₊ = [(b²-c²)p + √Δ] / [2a²b²]")
    print("where Δ = (b²-c²)²p² + 4a⁴b²c²")
    print("      √Δ = √[(b²-c²)²p² + 4a⁴b²c²]")

    print("\nWe need to prove: X_max ≤ X₊")
    print("i.e., p + 2c√[2(a² + p)] + c² ≤ [(b²-c²)p + √Δ] / [2a²b²]")

    print("\n" + "-" * 80)
    print("LOWER BOUND ON X")
    print("-" * 80)

    print("\nX = p + 2q + r is minimized when q, r are minimized.")
    print("\nSince we're in case X ≥ 0, consider two scenarios:")
    print("\n  Scenario A: r = -c², q minimized")
    print("    From CS-: q² ≤ (a² - p)(c² - (-c²)) = 2(a² - p)c²")
    print("    q can be negative, so q_min = -c√[2(a² - p)]")
    print("    X_min = p - 2c√[2(a² - p)] - c²")

    print("\n  Scenario B: q = 0, r = 0 (conservative)")
    print("    X_min = p")

    print("\nThe true minimum depends on which constraint is active.")

    print("\nThe lower root of the quadratic is:")
    print("  X₋ = [(b²-c²)p - √Δ] / [2a²b²]")

    print("\nWe need to prove: X₋ ≤ X_min")

    # Special insight
    print("\n" + "=" * 80)
    print("KEY INSIGHT")
    print("=" * 80)
    print("\nNote that X₋ can be NEGATIVE!")
    print("Since X₋ = [(b²-c²)p - √Δ] / [2a²b²]")
    print("and √Δ ≥ |b²-c²|p (from 4a⁴b²c² ≥ 0)")
    print("\nSo X₋ can be ≤ 0 even when p > 0.")
    print("\nSince we're in the case X ≥ 0, we need:")
    print("  max(X₋, 0) ≤ X ≤ X₊")
    print("\nIf X₋ < 0, the lower bound is automatically satisfied!")

def numerical_verification():
    """Numerically verify the bounds."""
    print("\n" + "=" * 80)
    print("NUMERICAL VERIFICATION OF BOUNDS")
    print("=" * 80)

    import random
    random.seed(42)

    violations_upper = []
    violations_lower = []

    for trial in range(10000):
        # Sample parameters
        a_val = random.uniform(0.01, 0.99)
        b_val = np.sqrt(1 - a_val**2)
        c_val = random.uniform(0.001, min(b_val, 0.5))
        p_val = random.uniform(0.001, a_val**2)

        # Test all combinations of extremal r and q
        for r_val in [-c_val**2, 0, c_val**2]:
            # Compute q bounds
            cs_plus = (a_val**2 + p_val) * (c_val**2 + r_val)
            cs_minus = (a_val**2 - p_val) * (c_val**2 - r_val)
            sum_cs = a_val**2 * c_val**2 + p_val * r_val

            if cs_plus <= 0 or cs_minus <= 0 or sum_cs <= 0:
                continue

            q_max = min(np.sqrt(cs_plus), np.sqrt(cs_minus), np.sqrt(sum_cs))

            for q_val in [-q_max, 0, q_max]:
                X_val = p_val + 2*q_val + r_val

                if X_val < 0:
                    continue

                # Compute quadratic roots
                A_val = a_val**2 * b_val**2
                B_val = -(b_val**2 - c_val**2) * p_val
                C_val = -a_val**2 * c_val**2

                Delta = B_val**2 - 4*A_val*C_val

                if Delta < 0:
                    # No real roots, quadratic always negative (good!)
                    continue

                X_minus = (-B_val - np.sqrt(Delta)) / (2*A_val)
                X_plus = (-B_val + np.sqrt(Delta)) / (2*A_val)

                # Check bounds
                if X_val > X_plus + 1e-10:
                    violations_upper.append({
                        'a': a_val, 'c': c_val, 'p': p_val, 'q': q_val, 'r': r_val,
                        'X': X_val, 'X_plus': X_plus, 'gap': X_val - X_plus
                    })

                if X_val < X_minus - 1e-10:
                    violations_lower.append({
                        'a': a_val, 'c': c_val, 'p': p_val, 'q': q_val, 'r': r_val,
                        'X': X_val, 'X_minus': X_minus, 'gap': X_minus - X_val
                    })

    print(f"\nTested 10000 trials with extremal points")
    print(f"Upper bound violations: {len(violations_upper)}")
    print(f"Lower bound violations: {len(violations_lower)}")

    if violations_upper:
        print("\n⚠ Upper bound violations found:")
        for v in violations_upper[:3]:
            print(f"  X={v['X']:.6f} > X_plus={v['X_plus']:.6f} (gap={v['gap']:.6e})")
            print(f"    a={v['a']:.4f}, c={v['c']:.4f}, p={v['p']:.4f}, q={v['q']:.4f}, r={v['r']:.4f}")

    if violations_lower:
        print("\n⚠ Lower bound violations found:")
        for v in violations_lower[:3]:
            print(f"  X={v['X']:.6f} < X_minus={v['X_minus']:.6f} (gap={v['gap']:.6e})")
            print(f"    a={v['a']:.4f}, c={v['c']:.4f}, p={v['p']:.4f}, q={v['q']:.4f}, r={v['r']:.4f}")

    if not violations_upper and not violations_lower:
        print("\n✓ All bounds satisfied!")

def analyze_upper_bound_algebraically():
    """Try to prove the upper bound algebraically."""
    print("\n" + "=" * 80)
    print("ALGEBRAIC PROOF OF UPPER BOUND")
    print("=" * 80)

    print("\nWe need: p + 2c√[2(a² + p)] + c² ≤ [(b²-c²)p + √Δ] / [2a²b²]")
    print("\nMultiply both sides by 2a²b²:")
    print("  2a²b²[p + 2c√[2(a² + p)] + c²] ≤ (b²-c²)p + √Δ")

    print("\nLet's denote:")
    print("  L = 2a²b²[p + 2c√[2(a² + p)] + c²]")
    print("  R = (b²-c²)p + √Δ")
    print("where Δ = (b²-c²)²p² + 4a⁴b²c²")

    print("\nExpanding L:")
    print("  L = 2a²b²p + 4a²b²c√[2(a² + p)] + 2a²b²c²")

    print("\nMove (b²-c²)p to the left:")
    print("  L - (b²-c²)p = 2a²b²p - (b²-c²)p + 4a²b²c√[2(a² + p)] + 2a²b²c²")
    print("               = 2a²b²p - b²p + c²p + 4a²b²c√[2(a² + p)] + 2a²b²c²")
    print("               = p(2a²b² - b² + c²) + 4a²b²c√[2(a² + p)] + 2a²b²c²")

    print("\nNote: 2a²b² - b² = b²(2a² - 1) = b²(2a² - (a² + b²)) = b²(a² - b²)")
    print("So: 2a²b² - b² + c² = b²(a² - b²) + c² = a²b² - b⁴ + c²")

    print("\nThis is getting complex. Let's try a different approach...")

def try_direct_verification():
    """Try direct algebraic manipulation."""
    print("\n" + "=" * 80)
    print("ALTERNATIVE: STRENGTHEN THE CONSTRAINT")
    print("=" * 80)

    print("\nInstead of finding exact bounds, note that:")
    print("  1. The quadratic a²b²X² - (b²-c²)pX - a²c² is ≤ 0 between roots")
    print("  2. We can verify the inequality directly without computing roots!")

    print("\nApproach: Substitute X = p + 2q + r into the quadratic")
    print("and use CS constraints to show it's ≤ 0.")

    print("\nLet f(X) = a²b²X² - (b²-c²)pX - a²c²")
    print("Substitute X = p + 2q + r:")
    print("  f(p + 2q + r) = a²b²(p + 2q + r)² - (b²-c²)p(p + 2q + r) - a²c²")

    print("\nExpand (p + 2q + r)²:")
    print("  = p² + 4q² + r² + 4pq + 4qr + 2pr")

    print("\nSo:")
    print("  f = a²b²[p² + 4q² + r² + 4pq + 4qr + 2pr]")
    print("    - (b²-c²)p[p + 2q + r] - a²c²")

    print("\nExpanding:")
    print("  f = a²b²p² + 4a²b²q² + a²b²r² + 4a²b²pq + 4a²b²qr + 2a²b²pr")
    print("    - (b²-c²)p² - 2(b²-c²)pq - (b²-c²)pr - a²c²")

    print("\nCollect terms by monomial:")
    print("  p² terms: a²b²p² - (b²-c²)p² = [a²b² - b² + c²]p² = [a²b² - b² + c²]p²")
    print("  q² terms: 4a²b²q²")
    print("  r² terms: a²b²r²")
    print("  pq terms: 4a²b²pq - 2(b²-c²)pq = [4a²b² - 2b² + 2c²]pq")
    print("  qr terms: 4a²b²qr")
    print("  pr terms: 2a²b²pr - (b²-c²)pr = [2a²b² - b² + c²]pr")
    print("  constant: -a²c²")

    print("\nThis matches the goal we computed symbolically!")
    print("\nNow use CS constraints:")
    print("  q² ≤ a²c² + pr  [sum_CS]")
    print("So: 4a²b²q² ≤ 4a²b²(a²c² + pr)")

def main():
    compute_bounds()
    numerical_verification()
    analyze_upper_bound_algebraically()
    try_direct_verification()

    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print("\nTwo possible proof approaches:")
    print("\n1. ROOT BOUNDS (geometric):")
    print("   - Compute roots X₋, X₊ of the quadratic")
    print("   - Show X_min ≥ X₋ and X_max ≤ X₊")
    print("   - This involves square root inequalities")
    print("\n2. DIRECT SUBSTITUTION (algebraic):")
    print("   - Substitute X = p + 2q + r directly")
    print("   - Use CS constraints to bound q² terms")
    print("   - Show the resulting expression is ≤ 0")
    print("   - This is what we attempted with SOS search")
    print("\nThe second approach is likely cleaner for formalization.")

if __name__ == '__main__':
    main()
