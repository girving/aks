#!/usr/bin/env python3
"""Approximate LDL^T experiment: can bounded-precision Cholesky certify PSD?

Key questions:
1. How large are the Cholesky factor entries (do they stay bounded)?
2. What is the residual ||M - L̃ D̃ L̃^T|| with 64-bit precision?
3. How does ||L^{-1}|| scale? (needed for perturbation bounds)
4. Is the eigenvalue gap large enough to absorb rounding errors?

Run with: uv run --with numpy --with networkx --with scipy scripts/approx_ldlt_experiment.py
"""

import sys
import time

try:
    import numpy as np
    import networkx as nx
    from scipy import linalg as la
except ImportError:
    print("Run with: uv run --with numpy --with networkx --with scipy scripts/approx_ldlt_experiment.py")
    sys.exit(1)


def build_M_plus(n, d, c=5/9, seed=42):
    """Build M₊ = cI - A/d + J/n for a random d-regular graph."""
    G = nx.random_regular_graph(d, n, seed=seed)
    A = nx.adjacency_matrix(G).toarray().astype(float)
    J = np.ones((n, n))
    M = c * np.eye(n) - A / d + J / n
    return M, A


def ldlt_numpy(M):
    """Compute LDL^T factorization via scipy."""
    n = M.shape[0]
    # Use scipy's ldl decomposition
    L, D_vec, perm = la.ldl(M, lower=True)
    # D_vec is a matrix (possibly block diagonal for indefinite); for PD it's diagonal
    D = np.diag(D_vec) if D_vec.ndim == 1 else np.diag(np.diag(D_vec))
    return L, D, perm


def experiment(n, d=12, c=5/9):
    """Run approximate LDL^T experiment."""
    print(f"\n{'='*70}")
    print(f"n={n}, d={d}, c={c:.6f}")
    print(f"{'='*70}")

    M, A = build_M_plus(n, d, c)

    # Eigenvalue analysis
    eigs = np.linalg.eigvalsh(M)
    print(f"  λ_min = {eigs[0]:.8e}")
    print(f"  λ_max = {eigs[-1]:.6f}")
    print(f"  κ(M) = {eigs[-1]/max(eigs[0], 1e-30):.1f}")

    if eigs[0] < -1e-10:
        print(f"  NOT PSD! Skipping.")
        return

    # Cholesky factorization (LL^T, not LDL^T — simpler)
    try:
        R = np.linalg.cholesky(M)  # M = R R^T, R lower triangular
    except np.linalg.LinAlgError:
        print("  Cholesky failed (not numerically PSD)")
        return

    # 1. Entry size analysis
    R_max = np.max(np.abs(R))
    R_min_nonzero = np.min(np.abs(R[np.abs(R) > 1e-15]))
    R_diag = np.diag(R)
    print(f"\n  Cholesky factor R (M = R R^T):")
    print(f"    max |R_{'{ij}'}| = {R_max:.6f}")
    print(f"    min nonzero |R_{'{ij}'}| = {R_min_nonzero:.2e}")
    print(f"    max R_ii = {R_diag.max():.6f}")
    print(f"    min R_ii = {R_diag.min():.6f}")

    # Fill-in
    nnz = np.count_nonzero(np.abs(R) > 1e-14)
    total = n * (n + 1) // 2
    print(f"    Fill-in: {nnz}/{total} = {100*nnz/total:.1f}%")

    # 2. Residual analysis
    residual = M - R @ R.T
    res_fro = np.linalg.norm(residual, 'fro')
    res_2 = np.linalg.norm(residual, 2)
    print(f"\n  Residual ||M - R R^T||:")
    print(f"    Frobenius: {res_fro:.2e}")
    print(f"    Spectral:  {res_2:.2e}")
    print(f"    λ_min / ||res||_2 = {eigs[0]/max(res_2, 1e-30):.1e} (must be > 1)")

    # 3. Condition number of R (relates to ||R^{-1}||)
    try:
        sigma_R = la.svdvals(R)
        sigma_max_R = sigma_R[0]
        sigma_min_R = sigma_R[-1]
        cond_R = sigma_max_R / sigma_min_R
        R_inv_norm = 1.0 / sigma_min_R
        print(f"\n  Condition of R:")
        print(f"    σ_max(R) = {sigma_max_R:.6f}")
        print(f"    σ_min(R) = {sigma_min_R:.6f}")
        print(f"    κ(R) = σ_max/σ_min = {cond_R:.1f}")
        print(f"    ||R^{{-1}}|| = 1/σ_min = {R_inv_norm:.4f}")
    except Exception as e:
        print(f"  SVD failed: {e}")
        R_inv_norm = None
        cond_R = None

    # 4. Simulated bounded-precision approach
    # Round R entries to B-bit precision and measure residual
    for B in [32, 48, 64]:
        # Scale R to use B-bit integers
        scale = 2**(B - int(np.ceil(np.log2(R_max + 1))) - 2)  # leave room
        R_int = np.round(R * scale).astype(np.float64) / scale
        res_B = M - R_int @ R_int.T
        res_B_2 = np.linalg.norm(res_B, 2)
        margin = eigs[0] / max(res_B_2, 1e-30)

        # Check R_int diagonal (all positive?)
        R_int_diag_min = np.diag(R_int).min()

        print(f"\n  B={B}-bit precision:")
        print(f"    ||M - R̃ R̃^T||_2 = {res_B_2:.2e}")
        print(f"    λ_min / ||residual||_2 = {margin:.1e} ({'OK' if margin > 1 else 'FAIL'})")
        print(f"    min diag(R̃) = {R_int_diag_min:.6f} ({'OK' if R_int_diag_min > 0 else 'FAIL'})")

    # 5. Certificate size estimate for n=20736
    if n >= 100:
        n_target = 20736
        entries = n_target * (n_target + 1) // 2
        for B in [32, 48, 64]:
            data_GB = entries * (B / 8) / 1e9
            print(f"\n  Certificate at n={n_target}, B={B}: {data_GB:.1f} GB")

    # 6. Verification cost analysis
    # For M = R R^T, entry (i,j) = sum_k R_ik R_jk, with min(i,j)+1 terms
    # Total: sum_{i>=j} (j+1) ≈ n^3/6 multiplications
    ops_total = n**3 / 6
    print(f"\n  Verification cost (M = R R^T check):")
    print(f"    Total multiplications: {ops_total:.2e}")
    print(f"    For n=20736: {20736**3/6:.2e} (~{20736**3/6/1e9:.0f} billion)")

    # 7. Sharded verification
    # Shard by row i: verify M[i,:] = sum_k R[i,k] * R[:,k]
    # Cost per row: O(n * min(i,n)) ≈ O(n^2) for typical rows
    ops_per_shard = n * n  # worst case
    print(f"\n  Sharded verification (one row per shard):")
    print(f"    Ops per shard: ~{ops_per_shard:.2e}")
    print(f"    Number of shards: {n}")
    print(f"    For n=20736: {20736**2:.2e} ops/shard, 20736 shards")

    # 8. Perturbation bound (Rump's criterion)
    # M = R̃^T R̃ + E. M is PSD if ||R̃^{-T} E R̃^{-1}|| < 1
    # This requires ||R̃^{-1}||^2 * ||E|| < 1
    if R_inv_norm is not None:
        for B in [32, 48, 64]:
            scale = 2**(B - int(np.ceil(np.log2(R_max + 1))) - 2)
            R_int = np.round(R * scale).astype(np.float64) / scale
            res_B = M - R_int @ R_int.T
            res_B_2 = np.linalg.norm(res_B, 2)

            # Rump criterion: need ||R̃^{-1}||^2 * ||E|| < 1
            # Since R̃ ≈ R, ||R̃^{-1}|| ≈ ||R^{-1}||
            rump_val = R_inv_norm**2 * res_B_2
            print(f"\n  Rump criterion B={B}: ||R̃⁻¹||² × ||E|| = {R_inv_norm:.2f}² × {res_B_2:.2e} = {rump_val:.2e} ({'OK' if rump_val < 1 else 'FAIL'})")

    return {
        'n': n, 'lambda_min': eigs[0], 'cond_R': cond_R,
        'R_inv_norm': R_inv_norm, 'R_max': R_max
    }


def main():
    results = []
    for n in [100, 500, 1000, 2000]:
        r = experiment(n)
        if r:
            results.append(r)

    # Scaling analysis
    print(f"\n{'='*70}")
    print("SCALING ANALYSIS")
    print(f"{'='*70}")
    print(f"  {'n':>6s}  {'λ_min':>12s}  {'κ(R)':>8s}  {'||R⁻¹||':>10s}  {'max|R|':>8s}")
    for r in results:
        print(f"  {r['n']:6d}  {r['lambda_min']:12.6e}  {r['cond_R']:8.1f}  {r['R_inv_norm']:10.4f}  {r['R_max']:8.4f}")

    # Extrapolate to n=20736
    if len(results) >= 2:
        # κ(R) and ||R^{-1}|| should be roughly constant (they depend on eigenvalue distribution, not n)
        avg_R_inv = np.mean([r['R_inv_norm'] for r in results])
        avg_R_max = np.mean([r['R_max'] for r in results])
        print(f"\n  Average ||R⁻¹|| across sizes: {avg_R_inv:.2f}")
        print(f"  Average max|R|: {avg_R_max:.4f}")
        print(f"\n  Extrapolation to n=20736:")
        print(f"    Expected ||R⁻¹|| ≈ {avg_R_inv:.1f}")

        # Rump bound: need ||R̃⁻¹||² × n × ε_mach × ||M|| < 1
        # ||M|| ≈ c + 1/n + 1 ≈ 1.56
        M_norm = 5/9 + 1.0  # roughly
        for B in [32, 48, 64]:
            eps = 2**(-B) * avg_R_max  # rounding error per entry
            # Total ||E||_2 ≈ n * eps (rough estimate for structured rounding error)
            E_norm = 20736 * eps
            rump = avg_R_inv**2 * E_norm
            margin = 1.0 / rump if rump > 0 else float('inf')
            print(f"    B={B}: estimated Rump value = {rump:.2e} (margin: {margin:.0f}x)")


if __name__ == "__main__":
    main()
