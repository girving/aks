import numpy as np

def verify_concave_identity():
    """Verify: f(t) = f(0)(1-t/T) + f(T)(t/T) + α·t·(T-t) for f = -αt² + βt + γ"""
    for _ in range(100000):
        alpha = np.random.uniform(0.1, 10)
        beta = np.random.uniform(-10, 10)
        gamma = np.random.uniform(0, 10)
        T = np.random.uniform(0.1, 10)
        t = np.random.uniform(0, T)
        
        f_t = -alpha * t**2 + beta * t + gamma
        f_0 = gamma
        f_T = -alpha * T**2 + beta * T + gamma
        
        rhs = f_0 * (1 - t/T) + f_T * (t/T) + alpha * t * (T - t)
        
        if abs(f_t - rhs) > 1e-8:
            print(f"MISMATCH: f(t)={f_t}, rhs={rhs}, diff={f_t-rhs}")
            return False
    print("✓ Concave identity verified: f(t) = f(0)(1-t/T) + f(T)(t/T) + α·t·(T-t)")
    return True

def check_G_at_max_X():
    """Check G at maximum feasible |X| for given p.
    
    G(t) = -AB·t² + (B-C)·|p|·t + AC  where t = |X|
    
    Max |X| comes from V1∩V2 intersection. But first let's check T = A + C
    (which is an upper bound on |X| = |p + 2q + r| ≤ A + 2√(AC) + C... no, tighter)
    
    Actually max |X| when p ≥ 0:
    X = p + 2q + r, with q² ≤ (A+p)(C+r) and q² ≤ (A-p)(C-r)
    To maximize X, take q > 0, r as large as possible.
    From V2: q² ≤ (A-p)(C-r), so r ≤ C - q²/(A-p)
    From V1: q² ≤ (A+p)(C+r), so r ≥ q²/(A+p) - C
    We want to maximize p + 2q + r.
    
    At the V1∩V2 boundary with both tight:
    q² = (A+p)(C+r) and q² = (A-p)(C-r)
    => (A+p)(C+r) = (A-p)(C-r)
    => AC + Ar + pC + pr = AC - Ar - pC + pr
    => 2Ar + 2pC = 0
    => r = -pC/A
    Then q² = (A+p)(C - pC/A) = (A+p)·C(A-p)/A = C(A²-p²)/A
    So q = √(C(A²-p²)/A) = √(C/A)·√(A²-p²)
    
    X = p + 2√(C(A²-p²)/A) - pC/A = p(1 - C/A) + 2√(C(A²-p²)/A)
      = p(A-C)/A + 2√(C/A)·√(A²-p²)
    
    Let μ = p/A ∈ [0,1], ν = √(1-μ²):
    X = μ(A-C) + 2ν√(AC)
    """
    min_G = float('inf')
    counter = 0
    for _ in range(10000000):
        A = np.random.uniform(0.001, 0.999)
        B = 1 - A
        C = np.random.uniform(0, B)
        mu = np.random.uniform(0, 1)
        nu = np.sqrt(1 - mu**2)
        p = mu * A
        
        # X at V1∩V2
        X = mu * (A - C) + 2 * nu * np.sqrt(A * C)
        
        G = A*C + (B-C)*p*X - A*B*X**2
        if G < min_G:
            min_G = G
            if G < -1e-10:
                counter += 1
                if counter <= 5:
                    print(f"  COUNTEREXAMPLE: A={A:.6f}, C={C:.6f}, mu={mu:.6f}, G={G:.6e}")
    if counter == 0:
        print(f"✓ G at V1∩V2 always ≥ 0. Min G = {min_G:.6e}")
    else:
        print(f"✗ Found {counter} counterexamples. Min G = {min_G:.6e}")

def check_perfect_square():
    """Verify G at V1∩V2 = A · [(1-2A)·ν·√C + (B+C)·μ·√A]²"""
    max_err = 0
    for _ in range(1000000):
        A = np.random.uniform(0.001, 0.999)
        B = 1 - A
        C = np.random.uniform(0.001, B - 0.001) if B > 0.002 else 0.001
        mu = np.random.uniform(0, 1)
        nu = np.sqrt(1 - mu**2)
        
        # V1∩V2 values
        p = mu * A
        r = -mu * C
        q2 = C * A * (1 - mu**2)
        q = np.sqrt(max(q2, 0))
        X = p + 2*q + r
        
        G = A*C + (B-C)*abs(p)*abs(X) - A*B*X**2
        
        formula = A * ((1 - 2*A) * nu * np.sqrt(C) + (B+C) * mu * np.sqrt(A))**2
        
        err = abs(G - formula)
        if err > max_err:
            max_err = err
        if err > 1e-6:
            print(f"  MISMATCH at A={A:.6f}, C={C:.6f}, mu={mu:.6f}: G={G:.10f}, formula={formula:.10f}, err={err:.2e}")
            return
    print(f"✓ Perfect square identity verified at V1∩V2! Max error: {max_err:.2e}")

def check_G_at_zero():
    """Verify G(0) = AC ≥ 0"""
    print("✓ G(0) = A·C ≥ 0 (trivially, since A > 0, C ≥ 0)")

def check_concavity_coefficient():
    """Verify G is concave in t: coefficient of t² is -AB < 0"""
    print("✓ G(t) = -AB·t² + (B-C)·P·t + AC has leading coeff -AB < 0 (A,B > 0)")

def verify_full_proof_chain():
    """
    Full proof chain:
    1. G(t) = -AB·t² + (B-C)·P·t + AC is concave (AB > 0)
    2. G(0) = AC ≥ 0
    3. G(T) ≥ 0 where T = X at V1∩V2 = max feasible |X|
    4. By concave interpolation: G(t) ≥ 0 for all t ∈ [0, T]
    
    The concave interpolation identity:
    G(t) = G(0)·(1-t/T) + G(T)·(t/T) + AB·t·(T-t)
    All three terms ≥ 0 for t ∈ [0, T].
    """
    min_G = float('inf')
    counter = 0
    for _ in range(5000000):
        A = np.random.uniform(0.001, 0.999)
        B = 1 - A
        C = np.random.uniform(0, B)
        
        # Random p, q, r satisfying constraints
        p = np.random.uniform(-A, A)
        r = np.random.uniform(-C, C)
        
        # q must satisfy q² ≤ (A+p)(C+r) and q² ≤ (A-p)(C-r)
        max_q2 = min((A + p) * (C + r), (A - p) * (C - r))
        if max_q2 < 0:
            continue
        q = np.random.uniform(-np.sqrt(max_q2), np.sqrt(max_q2))
        
        X = p + 2*q + r
        P = abs(p)
        t = abs(X)
        
        G = A*C + (B-C)*P*t - A*B*t**2
        
        if G < min_G:
            min_G = G
            if G < -1e-8:
                counter += 1
                if counter <= 5:
                    print(f"  COUNTEREX: A={A:.6f}, B={B:.6f}, C={C:.6f}, p={p:.6f}, q={q:.6f}, r={r:.6f}, X={X:.6f}, G={G:.10f}")
    
    if counter == 0:
        print(f"✓ Full G ≥ 0 verified over 5M random samples. Min G = {min_G:.6e}")
    else:
        print(f"✗ Found {counter} counterexamples! Min G = {min_G:.6e}")

def verify_T_is_max():
    """Verify that X at V1∩V2 is indeed the maximum of |X| for given (A,C,p).
    
    For fixed p ≥ 0, max |X| = max (p + 2q + r) subject to:
      q² ≤ (A+p)(C+r), q² ≤ (A-p)(C-r), |r| ≤ C
    
    At V1∩V2: r = -pC/A, q = √(C(A²-p²)/A)
    T = p(A-C)/A + 2√(C(A²-p²)/A)
    """
    violations = 0
    for _ in range(2000000):
        A = np.random.uniform(0.01, 0.99)
        B = 1 - A
        C = np.random.uniform(0.01, B - 0.01) if B > 0.02 else 0.01
        p = np.random.uniform(0, A)
        
        # T at V1∩V2
        r_opt = -p * C / A
        q2_opt = C * (A**2 - p**2) / A
        if q2_opt < 0:
            continue
        q_opt = np.sqrt(q2_opt)
        T = p + 2*q_opt + r_opt
        
        # Random feasible (q, r)
        r = np.random.uniform(-C, C)
        max_q2 = min((A + p) * (C + r), (A - p) * (C - r))
        if max_q2 < 0:
            continue
        q = np.sqrt(max_q2)  # maximize q
        X = p + 2*q + r
        
        if X > T + 1e-8:
            violations += 1
            if violations <= 3:
                print(f"  VIOLATION: A={A:.6f}, C={C:.6f}, p={p:.6f}, r={r:.6f}, q={q:.6f}, X={X:.6f} > T={T:.6f}")
    
    if violations == 0:
        print(f"✓ V1∩V2 intersection gives max |X| (verified over 2M samples)")
    else:
        print(f"✗ Found {violations} violations where X > T")

def check_G_table():
    """Print G(A+C) for some values to understand the sign pattern"""
    print("\nG(A+C) table (T = A+C is a looser upper bound on |X|):")
    print(f"  {'A':>6s} {'C':>6s} {'P/A':>6s} {'G(A+C)':>12s}")
    for A in [0.1, 0.3, 0.5, 0.7, 0.9]:
        B = 1 - A
        for C_frac in [0.01, 0.1, 0.5, 0.99]:
            C = C_frac * B
            for P_frac in [0, 0.5, 1.0]:
                P = P_frac * A
                T = A + C
                G = A*C + (B-C)*P*T - A*B*T**2
                print(f"  {A:6.3f} {C:6.3f} {P_frac:6.2f} {G:12.6f}")

def find_polynomial_certificate():
    """
    Try to express G(T) at the V1∩V2 point as a polynomial SOS.
    
    G at V1∩V2:
    With A+B=1, 0<A<1, 0≤C≤B, 0≤μ≤1, ν²=1-μ²:
    
    G = A·[(1-2A)·ν·√C + (B+C)·μ·√A]²
    
    Since A > 0, this is ≥ 0. QED for step 3.
    
    Let's verify this algebraically by expanding both sides.
    """
    print("\n--- Algebraic verification of perfect square identity ---")
    
    # Let's use sympy for exact algebra
    try:
        from sympy import symbols, sqrt, expand, simplify, factor
        
        A, B, C, mu, nu = symbols('A B C mu nu', positive=True)
        
        # Substitute B = 1 - A
        # p = mu*A, r = -mu*C, q = nu*sqrt(A*C)
        # X = p + 2q + r = mu*A + 2*nu*sqrt(A*C) - mu*C = mu*(A-C) + 2*nu*sqrt(A*C)
        
        p = mu * A
        X = mu * (A - C) + 2 * nu * sqrt(A * C)
        Bval = 1 - A
        
        G_expr = A * C + (Bval - C) * p * X - A * Bval * X**2
        
        formula = A * ((1 - 2*A) * nu * sqrt(C) + (Bval + C) * mu * sqrt(A))**2
        
        diff = expand(G_expr - formula)
        # Substitute nu² = 1 - mu²
        diff = diff.subs(nu**2, 1 - mu**2)
        diff = expand(diff)
        
        print(f"  G - formula (after nu²=1-μ²): {diff}")
        
        if diff == 0:
            print("  ✓ EXACT algebraic identity confirmed!")
        else:
            print(f"  Difference is: {simplify(diff)}")
            print("  (May need more substitution to simplify)")
    except ImportError:
        print("  sympy not available, skipping algebraic verification")

print("="*70)
print("RVW Quadratic Inequality Proof Verification")
print("="*70)
print()

print("--- Step 1: Concave interpolation identity ---")
verify_concave_identity()
print()

print("--- Step 2: G(0) = AC ≥ 0 ---")
check_G_at_zero()
print()

print("--- Step 3: G is concave in |X| ---")
check_concavity_coefficient()
print()

print("--- Step 4: Perfect square identity at V1∩V2 ---")
check_perfect_square()
print()

print("--- Step 5: V1∩V2 gives maximum |X| ---")
verify_T_is_max()
print()

print("--- Step 6: G at V1∩V2 ≥ 0 (follows from perfect square) ---")
check_G_at_max_X()
print()

print("--- Step 7: Full verification of G ≥ 0 ---")
verify_full_proof_chain()
print()

print("--- Bonus: G(A+C) table (checking looser bound) ---")
check_G_table()
print()

print("--- Algebraic verification with sympy ---")
find_polynomial_certificate()

print()
print("="*70)
print("PROOF STRATEGY SUMMARY")
print("="*70)
print("""
To prove: G(t) = AC + (B-C)·P·t - AB·t² ≥ 0 for all feasible t = |X|.

Proof:
1. G is concave in t (coefficient of t² is -AB < 0).
2. G(0) = AC ≥ 0.
3. Let T = max feasible |X| for given (A,B,C,P).
   At V1∩V2: T = μ(A-C) + 2ν√(AC) where μ = P/A, ν = √(1-μ²).
   G(T) = A · [(1-2A)ν√C + (B+C)μ√A]² ≥ 0 (perfect square times A > 0).
4. Concave interpolation: for t ∈ [0, T]:
   G(t) = G(0)·(1-t/T) + G(T)·(t/T) + AB·t·(T-t)
   All three terms ≥ 0. QED.

Lean formalization plan:
- Lemma 1: concave_interp_nonneg (pure algebra, no graph theory)
- Lemma 2: G_at_zero_nonneg (trivial: AC ≥ 0)
- Lemma 3: G_at_V1V2_eq_perfect_square (algebraic identity)
- Lemma 4: V1V2_maximizes_X (Lagrange multiplier / AM-GM argument)
- Lemma 5: rvw_quadratic_ineq (chain lemmas 1-4)
""")
