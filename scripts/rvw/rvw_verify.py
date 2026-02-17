import numpy as np
from itertools import product

def check_ineq(a2, c2, p, q, r):
    """Check G = a^2*c^2 + (b^2-c^2)*|p|*|X| - a^2*b^2*X^2 >= 0"""
    b2 = 1 - a2
    X = p + 2*q + r
    G = a2*c2 + (b2 - c2)*abs(p)*abs(X) - a2*b2*X**2
    return G

# Random sampling
rng = np.random.default_rng(42)
min_G = float('inf')
for _ in range(10_000_000):
    a2 = rng.uniform(0.001, 0.999)
    b2 = 1 - a2
    c = rng.uniform(0, np.sqrt(b2))
    c2 = c**2
    p = rng.uniform(-a2, a2)
    r = rng.uniform(-c2, c2)
    # q must satisfy both CS constraints
    cs_plus_bound = (a2 + p) * (c2 + r)
    cs_minus_bound = (a2 - p) * (c2 - r)
    if cs_plus_bound < 0 or cs_minus_bound < 0:
        continue
    q_max = min(np.sqrt(cs_plus_bound), np.sqrt(cs_minus_bound))
    q = rng.uniform(-q_max, q_max)
    G = check_ineq(a2, c2, p, q, r)
    if G < min_G:
        min_G = G
        if G < -1e-10:
            print(f"COUNTEREXAMPLE: a2={a2}, c2={c2}, p={p}, q={q}, r={r}, G={G}")

print(f"Minimum G found: {min_G:.2e}")

# Check the V1∩V2 case
print("\n--- V1∩V2 boundary analysis ---")
for a2 in [0.1, 0.3, 0.5, 0.7, 0.9]:
    for c2 in [0.01, 0.1, 0.3]:
        b2 = 1 - a2
        if c2 > b2:
            continue
        for mu in [0, 0.3, 0.7, 1.0]:
            p = mu * a2
            r = -p * c2 / a2
            q2 = c2 * (a2**2 - p**2) / a2
            if q2 < 0:
                continue
            q = np.sqrt(q2)
            G = check_ineq(a2, c2, p, q, r)
            print(f"  a2={a2:.1f}, c2={c2:.2f}, mu={mu:.1f}: G={G:.6f}")

# Verify the G = A^2(B+C)^2 formula at mu=1
print("\n--- G at mu=1 (p=A) ---")
for a2 in [0.1, 0.3, 0.5, 0.7, 0.9]:
    for c2 in [0.01, 0.1, 0.3]:
        b2 = 1 - a2
        if c2 > b2:
            continue
        p = a2
        r = -c2
        q = 0
        G = check_ineq(a2, c2, p, q, r)
        formula = a2**2 * (b2 + c2)**2
        print(f"  a2={a2:.1f}, c2={c2:.2f}: G={G:.6f}, A^2(B+C)^2={formula:.6f}, match={abs(G-formula)<1e-10}")
