#!/usr/bin/env python3
"""Exact LDL^T experiment: measure entry growth in Cholesky factorization.

Key question: how many bits do L entries grow to for random d-regular graphs?
This determines whether kernel verification of L^T M = DL^T is feasible.

Uses networkx for random regular graph generation.
Run with: uv run --with numpy --with networkx scripts/exact_ldlt_experiment.py
"""

import sys
import time
from fractions import Fraction

try:
    import networkx as nx
    import numpy as np
except ImportError:
    print("Run with: uv run --with numpy --with networkx scripts/exact_ldlt_experiment.py")
    sys.exit(1)


def random_regular_adj(n, d, seed=42):
    """Generate adjacency matrix of random d-regular graph as list-of-lists."""
    G = nx.random_regular_graph(d, n, seed=seed)
    adj = [[0] * n for _ in range(n)]
    for u, v in G.edges():
        adj[u][v] = 1
        adj[v][u] = 1
    return adj


def ldlt_exact(M, n, progress_interval=10):
    """Exact LDL^T factorization using Fraction arithmetic.
    Returns (L, D, max_bits)."""
    L = [[Fraction(0)] * n for _ in range(n)]
    D = [Fraction(0)] * n

    max_bits = 0
    t0 = time.time()

    for j in range(n):
        s = M[j][j]
        for k in range(j):
            s -= L[j][k] * L[j][k] * D[k]
        D[j] = s

        if D[j] == 0:
            print(f"  Zero pivot at j={j}!")
            return None, None, 0

        L[j][j] = Fraction(1)

        for i in range(j + 1, n):
            s = M[i][j]
            for k in range(j):
                s -= L[i][k] * L[j][k] * D[k]
            L[i][j] = s / D[j]

        # Track max bit-length of column j
        col_max = 0
        for i in range(j, n):
            if L[i][j] != 0:
                nb = abs(L[i][j].numerator).bit_length()
                db = abs(L[i][j].denominator).bit_length()
                col_max = max(col_max, nb, db)
        max_bits = max(max_bits, col_max)

        if j % progress_interval == 0 or j == n - 1:
            D_bits = max(abs(D[j].numerator).bit_length(),
                         abs(D[j].denominator).bit_length())
            elapsed = time.time() - t0
            print(f"  j={j:4d}/{n}: max_bits(L)={max_bits:6d}, "
                  f"D[j] bits={D_bits:5d}, D[j]>0={D[j]>0}, "
                  f"time={elapsed:.1f}s", flush=True)

    return L, D, max_bits


def experiment(n, d, c_num=5, c_den=9):
    """Run exact LDL^T and report entry growth."""
    c = Fraction(c_num, c_den)
    print(f"\n{'='*70}")
    print(f"n={n}, d={d}, c={c}")
    print(f"{'='*70}")

    A = random_regular_adj(n, d)

    # Build M₊ = cI - A/d + J/n as exact Fraction matrix
    M = [[Fraction(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            M[i][j] = Fraction(1, n)  # J/n
            if i == j:
                M[i][j] += c
            M[i][j] -= Fraction(A[i][j], d)

    # Quick float check: is M PSD?
    M_np = np.array([[float(M[i][j]) for j in range(n)] for i in range(n)])
    eigs = np.linalg.eigvalsh(M_np)
    print(f"  λ_min = {eigs[0]:.8f}, λ_max = {eigs[-1]:.6f}, κ = {eigs[-1]/max(eigs[0],1e-15):.1f}")

    if eigs[0] < -1e-10:
        print(f"  NOT PSD! Skipping.")
        return None

    t0 = time.time()
    L, D, max_bits = ldlt_exact(M, n, progress_interval=max(1, n // 8))
    total = time.time() - t0

    if L is None:
        return None

    all_pos = all(d_val > 0 for d_val in D)
    D_bits = max(max(abs(d_val.numerator).bit_length(), abs(d_val.denominator).bit_length())
                 for d_val in D)

    # Measure bit distribution
    bit_histogram = {}
    total_entries = 0
    for i in range(n):
        for j in range(i):
            if L[i][j] != 0:
                bits = max(abs(L[i][j].numerator).bit_length(),
                           abs(L[i][j].denominator).bit_length())
                bucket = (bits // 50) * 50
                bit_histogram[bucket] = bit_histogram.get(bucket, 0) + 1
                total_entries += 1

    print(f"\n  SUMMARY n={n}:")
    print(f"    All D > 0: {all_pos}")
    print(f"    Max bits in L: {max_bits}")
    print(f"    Max bits in D: {D_bits}")
    print(f"    Total time: {total:.1f}s")
    print(f"    L nonzero entries: {total_entries}/{n*(n-1)//2}")

    if bit_histogram:
        print(f"    Bit distribution of L entries:")
        for bucket in sorted(bit_histogram.keys()):
            count = bit_histogram[bucket]
            pct = 100 * count / total_entries
            print(f"      {bucket:4d}-{bucket+49:4d} bits: {count:6d} ({pct:5.1f}%)")

    return {
        'n': n, 'd': d, 'max_bits': max_bits, 'D_bits': D_bits,
        'time': total, 'all_pos': all_pos
    }


def main():
    results = []

    # Test with d=12 at various sizes
    for n in [50, 100, 150, 200, 300]:
        r = experiment(n, 12)
        if r:
            results.append(r)

    # Also test d=4 for comparison (sparser graph, less fill-in?)
    for n in [50, 100, 200]:
        r = experiment(n, 4, c_num=4, c_den=5)  # c=4/5 > 2√3/4 ≈ 0.866? No, AB for d=4: 2√3/4≈0.866
        if r:
            results.append(r)

    # Extrapolation summary
    print(f"\n{'='*70}")
    print(f"EXTRAPOLATION TO n=20736")
    print(f"{'='*70}")
    d12_results = [r for r in results if r['d'] == 12]
    if len(d12_results) >= 2:
        # Fit bit growth: bits ~ a * n + b
        ns = [r['n'] for r in d12_results]
        bits = [r['max_bits'] for r in d12_results]
        times = [r['time'] for r in d12_results]

        print(f"\n  d=12 data points:")
        print(f"  {'n':>6s}  {'max_bits':>10s}  {'bits/n':>8s}  {'time':>8s}")
        for i, r in enumerate(d12_results):
            print(f"  {r['n']:6d}  {r['max_bits']:10d}  {r['max_bits']/r['n']:8.1f}  {r['time']:8.1f}s")

        # Linear extrapolation
        if len(ns) >= 2:
            # bits_per_n using last two points
            slope = (bits[-1] - bits[-2]) / (ns[-1] - ns[-2])
            intercept = bits[-1] - slope * ns[-1]
            est_bits = slope * 20736 + intercept
            print(f"\n  Linear fit: bits ≈ {slope:.2f}·n + {intercept:.0f}")
            print(f"  Extrapolated max bits at n=20736: ~{est_bits:.0f}")

            # Time extrapolation (cubic)
            t_per_n3 = times[-1] / ns[-1]**3
            est_time = t_per_n3 * 20736**3
            print(f"  Extrapolated LDL^T computation time: ~{est_time:.0f}s = {est_time/3600:.0f}h")

            # Data size estimate
            n_full = 20736
            entries = n_full * (n_full - 1) // 2
            bytes_per_entry = est_bits / 4  # rough: each "bit" of a Fraction is ~2 bytes
            total_bytes = entries * bytes_per_entry
            print(f"\n  Certificate data size estimates (n=20736):")
            print(f"    L entries: {entries:,.0f}")
            print(f"    Est. bits per entry: ~{est_bits:.0f}")
            print(f"    Est. total data: ~{total_bytes/1e9:.1f} GB")

            # One-sided verification cost
            ops = n_full * n_full * 13  # 13 nonzeros per column for d=12
            print(f"\n  One-sided verification (L^T M = DL^T):")
            print(f"    Operations: {ops:,.0f} ({ops/1e9:.1f} billion)")
            print(f"    Each op: ~{est_bits:.0f}-bit multiply + add")


if __name__ == "__main__":
    main()
