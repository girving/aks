#!/usr/bin/env python3
"""DEPRECATED: This experiment tested the WRONG identity L^T M = DL^T.

The correct identity is L⁻¹ M = DL^T, which requires O(n³) forward substitution
regardless of M's sparsity. See docs/psd-certificate-analysis.md for details.

Use scripts/approx_ldlt_experiment.py instead for the correct analysis.
"""

import numpy as np
from fractions import Fraction
import time
import sys

def random_regular_graph_adj(n, d, seed=42):
    """Generate adjacency matrix of a random d-regular graph on n vertices.
    Returns Python list-of-lists (not numpy) for compatibility with Fraction."""
    rng = np.random.RandomState(seed)
    # Configuration model: d perfect matchings on n vertices
    # Simple version: keep trying until we get a simple graph
    for attempt in range(100):
        adj = [[0] * n for _ in range(n)]
        stubs = []
        for v in range(n):
            stubs.extend([v] * d)
        stubs_arr = np.array(stubs)
        rng.shuffle(stubs_arr)
        stubs = stubs_arr.tolist()
        ok = True
        for i in range(0, len(stubs), 2):
            u, v = stubs[i], stubs[i+1]
            if u == v or adj[u][v] >= 1:
                ok = False
                break
            adj[u][v] += 1
            adj[v][u] += 1
        if ok and all(sum(row) == d for row in adj):
            return adj
    # Fallback: use repeated perfect matchings
    adj = [[0] * n for _ in range(n)]
    for _ in range(d):
        perm = rng.permutation(n).tolist()
        for i in range(0, n, 2):
            u, v = perm[i], perm[i+1]
            adj[u][v] += 1
            adj[v][u] += 1
    return adj


def adj_to_numpy(adj):
    """Convert list-of-lists adjacency matrix to numpy array."""
    return np.array(adj, dtype=float)


def experiment_float(n, d, c=5/9):
    """Float experiment: verify one-sided approach and measure operation counts."""
    print(f"\n{'='*60}")
    print(f"n={n}, d={d}, c={c:.4f}")
    print(f"{'='*60}")

    A_list = random_regular_graph_adj(n, d)
    A = adj_to_numpy(A_list)

    # Check regularity
    degrees = A.sum(axis=1)
    print(f"Degree range: [{degrees.min()}, {degrees.max()}]")

    # M₊ = cI - A/d + J/n
    J = np.ones((n, n))
    M_plus = c * np.eye(n) - A / d + J / n

    # M₋ = cI + A/d - J/n
    M_minus = c * np.eye(n) + A / d - J / n

    # M_quad = c²I - (A/d - J/n)²
    WmP = A / d - J / n
    M_quad = c**2 * np.eye(n) - WmP @ WmP

    # Eigenvalues
    eigs_plus = np.linalg.eigvalsh(M_plus)
    eigs_minus = np.linalg.eigvalsh(M_minus)
    eigs_quad = np.linalg.eigvalsh(M_quad)
    eigs_WmP = np.linalg.eigvalsh(WmP)

    spectral_gap = max(abs(eigs_WmP[0]), abs(eigs_WmP[-1]))
    # Actually for d-regular, the top eigenvalue of W = A/d is 1,
    # and P projects onto constant vector, so W-P has top eigenvalue = max(|λ_2|, |λ_n|)
    # where λ_i are eigenvalues of A/d
    eigs_A = np.linalg.eigvalsh(A.astype(float))
    eigs_W = eigs_A / d
    # Remove the eigenvalue 1 (constant vector)
    eigs_W_sorted = np.sort(eigs_W)
    spectral_gap_actual = max(abs(eigs_W_sorted[-2]), abs(eigs_W_sorted[0]))

    print(f"Spectral gap (‖W-P‖): {spectral_gap_actual:.6f}")
    print(f"Target bound c = {c:.6f}")
    print(f"Margin: c - gap = {c - spectral_gap_actual:.6f}")

    print(f"\nM₊ eigenvalues: min={eigs_plus.min():.8f}, max={eigs_plus.max():.6f}")
    print(f"M₋ eigenvalues: min={eigs_minus.min():.8f}, max={eigs_minus.max():.6f}")
    print(f"M_quad eigenvalues: min={eigs_quad.min():.8f}, max={eigs_quad.max():.6f}")

    is_psd_plus = eigs_plus.min() > -1e-10
    is_psd_minus = eigs_minus.min() > -1e-10
    is_psd_quad = eigs_quad.min() > -1e-10
    print(f"\nPSD? M₊: {is_psd_plus}, M₋: {is_psd_minus}, M_quad: {is_psd_quad}")

    if not (is_psd_plus and is_psd_minus):
        print("WARNING: M₊ or M₋ not PSD — spectral gap exceeds c!")
        return

    # Condition numbers
    cond_plus = eigs_plus.max() / max(eigs_plus.min(), 1e-15)
    cond_minus = eigs_minus.max() / max(eigs_minus.min(), 1e-15)
    cond_quad = eigs_quad.max() / max(eigs_quad.min(), 1e-15)
    print(f"\nCondition numbers: M₊={cond_plus:.1f}, M₋={cond_minus:.1f}, M_quad={cond_quad:.1f}")

    # Sparsity analysis
    S_plus = c * np.eye(n) - A / d  # sparse part of M₊
    nnz_S = np.count_nonzero(S_plus)
    nnz_per_col_S = np.count_nonzero(S_plus, axis=0).max()

    A2 = A @ A
    S_quad = c**2 * np.eye(n) - A2 / d**2  # sparse part of M_quad
    nnz_S_quad = np.count_nonzero(S_quad)
    nnz_per_col_S_quad = np.count_nonzero(S_quad, axis=0).max()

    print(f"\nSparsity of S (M₊ sparse part): nnz={nnz_S}, max_nnz/col={nnz_per_col_S}")
    print(f"Sparsity of S (M_quad sparse part): nnz={nnz_S_quad}, max_nnz/col={nnz_per_col_S_quad}")

    # One-sided verification timing
    # Standard: compute LDL^T, compare to M
    t0 = time.time()
    try:
        L_chol = np.linalg.cholesky(M_plus)
    except np.linalg.LinAlgError:
        print("Cholesky failed (M₊ not numerically PSD)")
        return
    t_chol = time.time() - t0

    # Verify standard way: L L^T = M
    t0 = time.time()
    residual_standard = np.max(np.abs(L_chol @ L_chol.T - M_plus))
    t_standard = time.time() - t0

    # Verify one-sided: L^T M = D L^T where D = diag(L L^T diag)
    # Actually for LL^T (not LDL^T), one-sided is L^{-1} M = L^T
    # Let's use the equation L^T M₊ and compare to (L^T L) L^T
    # Hmm, let's just do the sparse multiplication

    t0 = time.time()
    # Compute L^T @ S_plus (exploiting sparsity)
    LtS = np.zeros((n, n))
    for j in range(n):
        col_j = S_plus[:, j]
        nz = np.nonzero(col_j)[0]  # sparse column indices
        for k in nz:
            # L^T[i, k] = L[k, i] for i <= k (lower triangular)
            LtS[:k+1, j] += L_chol[k, :k+1] * col_j[k]
    t_sparse = time.time() - t0

    # Add the J/n contribution: L^T @ (J/n) = (1/n) (L^T @ 1) @ 1^T
    Lt1 = L_chol.T @ np.ones(n)  # O(n²)
    LtM = LtS + np.outer(Lt1, np.ones(n)) / n

    # Compare to L^T @ M₊ computed densely
    LtM_dense = L_chol.T @ M_plus
    residual_onesided = np.max(np.abs(LtM - LtM_dense))

    print(f"\nVerification timing (n={n}):")
    print(f"  Cholesky: {t_chol:.4f}s")
    print(f"  Standard L@L^T verify: {t_standard:.4f}s")
    print(f"  One-sided sparse L^T@S: {t_sparse:.4f}s")
    print(f"  Residual (one-sided vs dense): {residual_onesided:.2e}")

    # Operation count analysis
    ops_standard = n**3  # L L^T
    ops_onesided = n * n * (d + 1)  # L^T @ S, d+1 nonzeros per column
    ops_onesided_quad = n * n * nnz_per_col_S_quad  # if using M_quad
    print(f"\nOperation counts:")
    print(f"  Standard (n³): {ops_standard:,.0f}")
    print(f"  One-sided M₊ (n²·(d+1)): {ops_onesided:,.0f} ({ops_standard/ops_onesided:.1f}× savings)")
    print(f"  One-sided M_quad (n²·nnz): {ops_onesided_quad:,.0f} ({ops_standard/ops_onesided_quad:.1f}× savings)")

    # Fill-in of L
    L_nnz = np.count_nonzero(np.abs(L_chol) > 1e-14)
    L_total = n * (n + 1) // 2
    print(f"\nCholesky fill-in: {L_nnz}/{L_total} = {100*L_nnz/L_total:.1f}%")


def experiment_exact(n, d, c_num=5, c_den=9):
    """Exact rational experiment: measure entry growth in LDL^T."""
    print(f"\n{'='*60}")
    print(f"EXACT: n={n}, d={d}, c={c_num}/{c_den}")
    print(f"{'='*60}")

    A = random_regular_graph_adj(n, d)  # returns list-of-lists of Python ints

    # Build integer matrix n*M₊ = (c_num*n*d/c_den)I - (n/d)*A + J
    # M₊ = (c_num/c_den)I - A/d + J/n
    # n*d*c_den * M₊ = c_num*n*d*I - c_den*n*A + d*c_den*J
    # Use n*M₊ for simplicity:
    # n*M₊ = (c_num*n/c_den)I - (n/d)*A + J
    # For n*c_den*d * M₊ = c_num*n*d*I - c_den*n*A + c_den*d*J (all integer)

    # Actually let's just use Fraction directly
    c = Fraction(c_num, c_den)

    # Build M₊ as exact rational matrix
    M = [[Fraction(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            M[i][j] = Fraction(1, n)  # J/n
            if i == j:
                M[i][j] += c  # cI
            M[i][j] -= Fraction(A[i][j], d)  # -A/d

    # LDL^T factorization (Fraction arithmetic)
    L = [[Fraction(0)] * n for _ in range(n)]
    D = [Fraction(0)] * n

    t0 = time.time()
    for j in range(n):
        # D[j] = M[j][j] - sum(L[j][k]^2 * D[k] for k < j)
        s = M[j][j]
        for k in range(j):
            s -= L[j][k] * L[j][k] * D[k]
        D[j] = s

        if D[j] == 0:
            print(f"  Zero pivot at j={j}!")
            return

        L[j][j] = Fraction(1)

        for i in range(j + 1, n):
            # L[i][j] = (M[i][j] - sum(L[i][k]*L[j][k]*D[k] for k < j)) / D[j]
            s = M[i][j]
            for k in range(j):
                s -= L[i][k] * L[j][k] * D[k]
            L[i][j] = s / D[j]

        if j % 10 == 0 or j == n - 1:
            # Report progress and entry sizes
            max_num = 0
            max_den = 0
            for i in range(j + 1):
                for k in range(j + 1):
                    if L[i][k] != 0:
                        max_num = max(max_num, abs(L[i][k].numerator).bit_length())
                        max_den = max(max_den, abs(L[i][k].denominator).bit_length())
            D_num = abs(D[j].numerator).bit_length()
            D_den = abs(D[j].denominator).bit_length()
            elapsed = time.time() - t0
            print(f"  j={j:4d}: L max bits num={max_num:6d} den={max_den:6d}, "
                  f"D[j] bits={D_num}/{D_den}, D[j]>0: {D[j]>0}, time={elapsed:.1f}s")
            sys.stdout.flush()

    t_total = time.time() - t0
    print(f"\n  Total time: {t_total:.1f}s")

    # Summary statistics
    all_D_positive = all(d > 0 for d in D)
    max_L_bits = 0
    for i in range(n):
        for j in range(i):
            if L[i][j] != 0:
                bits = max(abs(L[i][j].numerator).bit_length(),
                           abs(L[i][j].denominator).bit_length())
                max_L_bits = max(max_L_bits, bits)

    print(f"\n  All D > 0: {all_D_positive}")
    print(f"  Max bit-length in L: {max_L_bits}")
    print(f"  Max bit-length in D: {max(max(abs(d.numerator).bit_length(), abs(d.denominator).bit_length()) for d in D)}")


if __name__ == "__main__":
    # Float experiments at various sizes
    for n in [100, 500, 1000]:
        experiment_float(n, 12)

    # Exact experiments at small sizes
    for n in [20, 40, 60, 80, 100]:
        experiment_exact(n, 12)
