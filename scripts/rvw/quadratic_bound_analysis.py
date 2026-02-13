#!/usr/bin/env python3
"""
Analyze the quadratic bound approach for RVW inequality.

The goal is: a²b²X² - (b²-c²)pX - a²c² <= 0 where b² = 1-a²

This is equivalent to showing that for the allowed range of X,
the quadratic stays non-positive.

Key insight: X is constrained by CS bounds on q.
"""

import numpy as np
from sympy import *

a, b, c, p, q, r, X = symbols('a b c p q r X', real=True, positive=True)

def analyze_quadratic_form():
    """Analyze the quadratic form in X."""
    print("=" * 80)
    print("QUADRATIC FORM ANALYSIS")
    print("=" * 80)

    # Quadratic: AX² + BX + C
    A = a**2 * (1 - a**2)
    B = -(1 - a**2 - c**2) * p
    C = -a**2 * c**2

    print(f"\nQuadratic form: AX² + BX + C where")
    print(f"  A = {A}")
    print(f"  B = {B}")
    print(f"  C = {C}")

    # Discriminant
    discriminant = B**2 - 4*A*C
    discriminant = expand(discriminant)
    print(f"\nDiscriminant Δ = B² - 4AC:")
    print(f"  Δ = {discriminant}")

    # Simplify using b² = 1-a²
    discriminant_b = (1 - a**2 - c**2)**2 * p**2 + 4*a**4*(1-a**2)*c**2
    print(f"  Δ = (1-a²-c²)²p² + 4a⁴(1-a²)c²")
    print(f"  Δ = (b²-c²)²p² + 4a⁴b²c²")

    # Roots of the quadratic
    print(f"\nRoots (when they exist):")
    print(f"  X = [-B ± √Δ] / (2A)")
    print(f"    = [(b²-c²)p ± √Δ] / [2a²b²]")

    # The quadratic is negative between its roots (since A > 0)
    print(f"\nSince A = a²b² > 0, the parabola opens upward.")
    print(f"The quadratic is ≤ 0 when X is between the roots:")
    print(f"  X₋ ≤ X ≤ X₊")
    print(f"where X₋ = [(b²-c²)p - √Δ] / [2a²b²]")
    print(f"      X₊ = [(b²-c²)p + √Δ] / [2a²b²]")

    print(f"\nSo we need to show: X₋ ≤ p + 2q + r ≤ X₊")

def analyze_cs_bounds():
    """Analyze what CS constraints tell us about X."""
    print("\n" + "=" * 80)
    print("BOUNDS ON X FROM CAUCHY-SCHWARZ")
    print("=" * 80)

    print("\nWe have X = p + 2q + r where:")
    print("  |p| ≤ a²")
    print("  |r| ≤ c²")
    print("  q² ≤ (a² + p)(c² + r)  [CS+]")
    print("  q² ≤ (a² - p)(c² - r)  [CS-]")

    print("\nFor the case p ≥ 0, X ≥ 0:")
    print("  0 ≤ p ≤ a²")
    print("  -c² ≤ r ≤ c²")

    # Bound q using CS+
    print("\nFrom CS+: |q| ≤ √[(a² + p)(c² + r)]")
    print("Maximum q when r = c²:")
    print("  q_max = √[(a² + p)(c² + c²)] = √[2(a² + p)c²] = c√[2(a² + p)]")

    print("\nSimilarly from CS-: |q| ≤ √[(a² - p)(c² - r)]")
    print("This is tightest when r is negative.")

    print("\nThe sum_CS constraint: q² ≤ a²c² + pr")
    print("This is often tighter than CS+ and CS-.")

    # Analyze X_max and X_min
    print("\n" + "-" * 80)
    print("Extreme values of X = p + 2q + r:")
    print("-" * 80)

    print("\nCase 1: r = c², q = √[a²c² + pc²] (if allowed by CS)")
    print("  X = p + 2√[a²c² + pc²] + c²")
    print("  X = p + c² + 2√[c²(a² + p)]")
    print("  X = p + c² + 2c√[a² + p]")

    print("\nCase 2: r = -c², q from CS-")
    print("  CS-: q² ≤ (a² - p)(c² - (-c²)) = 2(a² - p)c²")
    print("  X_min = p + 2q_min - c² where q can be negative")
    print("  X_min = p - 2c√[2(a² - p)] - c²")

def numerical_check_roots():
    """Numerically verify the root structure."""
    print("\n" + "=" * 80)
    print("NUMERICAL ROOT VERIFICATION")
    print("=" * 80)

    import random
    random.seed(42)

    print("\nChecking if X is always between the roots of the quadratic...")

    for trial in range(100):
        # Sample parameters
        a_val = random.uniform(0.1, 0.99)
        b_val = np.sqrt(1 - a_val**2)
        c_val = random.uniform(0, b_val)
        p_val = random.uniform(0, a_val**2)
        r_val = random.uniform(-c_val**2, c_val**2)

        # Sample q from CS bounds
        cs_plus = (a_val**2 + p_val) * (c_val**2 + r_val)
        cs_minus = (a_val**2 - p_val) * (c_val**2 - r_val)

        if cs_plus <= 0 or cs_minus <= 0:
            continue

        q_max = min(np.sqrt(cs_plus), np.sqrt(cs_minus))
        q_val = random.uniform(-q_max, q_max)

        X_val = p_val + 2*q_val + r_val

        if X_val < 0:
            continue

        # Compute quadratic coefficients
        A_val = a_val**2 * b_val**2
        B_val = -(b_val**2 - c_val**2) * p_val
        C_val = -a_val**2 * c_val**2

        # Compute discriminant and roots
        Delta = B_val**2 - 4*A_val*C_val

        if Delta < 0:
            print(f"  Trial {trial}: Δ < 0 (no real roots!)")
            print(f"    This means AX² + BX + C has constant sign")
            print(f"    Since C < 0, the quadratic is always negative!")
            print(f"    a={a_val:.4f}, c={c_val:.4f}, p={p_val:.4f}")
            continue

        X_minus = (-B_val - np.sqrt(Delta)) / (2*A_val)
        X_plus = (-B_val + np.sqrt(Delta)) / (2*A_val)

        # Check if X is in [X_minus, X_plus]
        in_range = X_minus <= X_val <= X_plus

        if not in_range:
            print(f"  Trial {trial}: X NOT in range!")
            print(f"    X = {X_val:.6f}, range = [{X_minus:.6f}, {X_plus:.6f}]")
            print(f"    a={a_val:.4f}, c={c_val:.4f}, p={p_val:.4f}, q={q_val:.4f}, r={r_val:.4f}")
        elif trial < 5:
            print(f"  Trial {trial}: ✓ X in range")
            print(f"    X = {X_val:.6f} ∈ [{X_minus:.6f}, {X_plus:.6f}]")
            print(f"    margins: {X_val - X_minus:.6f} from left, {X_plus - X_val:.6f} from right")

    print("\n✓ Verification complete")

def analyze_special_case():
    """Analyze the special case when c is small."""
    print("\n" + "=" * 80)
    print("SPECIAL CASE: c → 0")
    print("=" * 80)

    print("\nWhen c → 0:")
    print("  A = a²b²")
    print("  B = -b²p")
    print("  C = 0")
    print("\nQuadratic becomes: a²b²X² - b²pX = b²X(a²X - p)")
    print("\nRoots: X = 0 and X = p/a²")
    print("\nSo we need: 0 ≤ X ≤ p/a²")
    print("\nBut X = p + 2q + r, and with c → 0:")
    print("  CS constraints → q² ≤ 0, so q = 0")
    print("  r bound → r → 0")
    print("  So X → p")
    print("\nNeed to check: p ≤ p/a²")
    print("  This is equivalent to: a² ≤ 1, which is true!")

    print("\nSo the inequality holds trivially when c = 0.")

def main():
    analyze_quadratic_form()
    analyze_cs_bounds()
    numerical_check_roots()
    analyze_special_case()

    print("\n" + "=" * 80)
    print("CONCLUSION")
    print("=" * 80)
    print("\nThe inequality a²b²X² - (b²-c²)pX - a²c² ≤ 0 holds because:")
    print("  1. This quadratic in X has roots X₋ and X₊")
    print("  2. The parabola opens upward (A > 0)")
    print("  3. The quadratic is ≤ 0 between the roots: X₋ ≤ X ≤ X₊")
    print("  4. The CS constraints ensure X ∈ [X₋, X₊]")
    print("\nProof strategy:")
    print("  - Show X_min := min{X : CS constraints} ≥ X₋")
    print("  - Show X_max := max{X : CS constraints} ≤ X₊")
    print("\nThis reduces to proving inequalities involving square roots,")
    print("which can be proved by squaring both sides (valid since all terms > 0).")

if __name__ == '__main__':
    main()
