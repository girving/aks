# PSD Certificate Analysis for the Base Expander

## Question

Can we certify that the matrix `M₊ = cI - A/d + J/n` is positive semidefinite
for the base expander (n = 20736, d = 12, c = 5/9) in a way that's feasible
to verify inside Lean? Specifically: can we avoid O(n³) verification?

## Summary

**No O(n²) deterministic PSD certificate exists for matrices with dense
Cholesky factors.** Our expander matrix has 100% Cholesky fill-in, forcing
any factorization-based verification to be O(n³). However, bounded-precision
certificates reduce the data to ~0.9 GB (vs 2.3 TB for exact rational), and
O(n³) verification can be distributed across ~20K parallel shards.

## Correction: L^T M ≠ DL^T

An earlier version of this document claimed that `L^T M = DL^T` when
`M = LDL^T`, giving O(n²d) verification via sparsity of M. **This identity is
wrong.** Counterexample:

    M = [[4, 2], [2, 3]]
    L = [[1, 0], [1/2, 1]],  D = diag(4, 2)
    L^T M = [[5, 7/2], [2, 3]]  ≠  DL^T = [[4, 2], [0, 2]]

The correct one-sided identity is **`L⁻¹ M = DL^T`** (multiply `M = LDL^T` on
the left by `L⁻¹`). Computing `L⁻¹ M` requires forward substitution with the
dense L matrix — O(n²) per column of M, O(n³) total regardless of M's
sparsity. There is no "one-sided trick" that avoids cubic verification for
dense factorizations.

## Exact LDL^T: Infeasible Due to Entry Growth

### Experimental data (exact rational arithmetic)

| n | Max bits in L | Bits/n | Total time |
|---|---------------|--------|------------|
| 50 | 207 | 4.1 | 0.1s |
| 100 | 413 | 4.1 | 1.3s |
| 150 | 612 | 4.1 | 5.5s |
| 200 | 812 | 4.1 | 13s |
| 300 | 1216 | 4.1 | 67s |

**Entry growth is perfectly linear: ~4.1 bits per elimination step.** This is a
fundamental property of the factorization — each pivot D_j divides through,
compounding denominators across all n steps.

### Extrapolation to n = 20736

- Max bits per L entry: ~4.1 × 20736 ≈ **84,000 bits** (~10 KB per entry)
- L entries: n²/2 ≈ 215 million
- Total data: **~2.3 TB** — infeasible
- LDL^T computation time (Python Fraction): ~6000 hours

## Approximate LDL^T: Data Is Feasible, Verification Is O(n³)

### Cholesky entries are bounded

Floating-point Cholesky factor entries satisfy `max |R_{ij}| ≈ 0.75`,
independent of n. This means bounded-precision certificates have reasonable
data sizes:

| Precision | Certificate size (n=20736) |
|-----------|---------------------------|
| 32-bit | 0.9 GB |
| 48-bit | 1.3 GB |
| 64-bit | 1.7 GB |

### The eigenvalue gap provides massive error tolerance

Rump's criterion: M is PSD if `||R̃⁻¹||² × ||M - R̃ R̃^T||₂ < 1`.

Experimental data (scaling analysis):

| n | λ_min | κ(R) | ||R⁻¹|| | Rump (B=32) | Rump (B=64) |
|------|------------|------|---------|-------------|-------------|
| 100 | 5.8e-2 | 4.3 | 4.2 | 2.2e-7 | 4.0e-15 |
| 500 | 1.4e-2 | 8.9 | 8.5 | 3.9e-6 | 1.8e-14 |
| 1000 | 1.0e-2 | 10.3 | 9.9 | 1.1e-5 | 2.5e-14 |
| 2000 | 5.6e-3 | 14.0 | 13.4 | 3.8e-5 | 4.7e-14 |

The Rump value must be < 1. Even 32-bit precision gives margin > 3000×.

At n = 20736 (extrapolated): `||R⁻¹|| ≈ 18` (from λ_min ≈ 0.003), giving
Rump value ≈ 3×10⁻⁴ for B=32. **Still 3000× below threshold.**

### But Cholesky fill-in is 100%

| n | Fill-in |
|------|---------|
| 100 | 100.0% |
| 500 | 100.0% |
| 1000 | 100.0% |
| 2000 | 100.0% |

Expanders have no good separators (that's what makes them expanders). The
Cholesky factor is completely dense regardless of elimination ordering.

### Verification requires O(n³) operations

Verifying `M = R̃ R̃^T` entry-by-entry: each of the n² entries is an inner
product of length n → **O(n³)** total multiplications. For n = 20736:
~1.5 × 10¹² multiplications. This is the fundamental bottleneck — the
eigenvalue gap helps with data size but not with verification complexity.

## Other Approaches Considered

### Freivalds' randomized verification

Pick random vector r. Check `M r = R̃ (R̃^T r)` in O(n²). Error probability 1/2
per trial; k trials gives 2^{-k}. State-of-the-art for PSD certification
(Dumas & Kaltofen, ISSAC 2014).

**Problem for Lean:** Probabilistic — unsatisfying for a formal mathematical proof.

### Lanczos/Krylov certificates

Full Lanczos gives a tridiagonal matrix T_n whose eigenvalues equal M's. LDL^T
of T_n is O(n) — no fill-in! But exact Lanczos has exponential coefficient
growth (~D^k bits at step k). Infeasible for n = 20736.

Also: λ_min(T_k) ≥ λ_min(M) for k < n (Cauchy interlacing), giving the wrong
direction for PSD certification.

### Trace method

Certificate: tr(A^{2k}). For tight bound: k ≈ 1060, requiring tr(A^{2120}).
Infeasible to compute.

### Modular arithmetic (CRT)

Store L mod p for ~1300 primes (product > 2^{84000}). Total: ~2.2 TB. Same as
exact approach.

### Sparse basis for 1⊥

The matrix M₀ = cI - A/d is sparse (d+1 nonzeros/row). On 1⊥, M₊ and M₀
have the same eigenvalues (J/n vanishes on 1⊥). A basis like {eₖ - eₖ₊₁}
gives a sparse representation of M₀|_{1⊥} (~2d nonzeros/row). But the
Cholesky of this sparse matrix is still dense — the underlying graph is an
expander with high treewidth.

### ValidSDP (Coq) / Rump's criterion

Compute floating-point Cholesky R, verify `||M - R^T R|| < σ_min(R)²` using
rigorous IEEE 754 rounding analysis. Verification is O(n³). Porting to Lean
requires formalizing: IEEE 754 rounding, matrix norms, Weyl's perturbation
theorem. ([ValidSDP](https://github.com/validsdp/validsdp))

## Remaining Viable Paths

### 1. Sharded parallel verification

Distribute the O(n³) work across ~20K independent shards (one per row of R̃):

- Each shard verifies `M[i,:] = Σ_k R̃[i,k] × R̃[:,k]`: ~4.3 × 10⁸ multiplications
- Certificate data: ~0.9 GB (32-bit entries)
- Shard data: ~166 KB per shard (one row of R̃ + diagonal)
- With 96 cores and `decide +kernel` on 32-bit Nat: wall time TBD
- Also need: one-time theoretical proof that Rump's criterion suffices, plus
  Lean formalization of ||R̃⁻¹|| bound

### 2. Algebraic base expander

Use a Cayley graph (e.g., SL₂(F_p) with generators) whose spectral gap follows
from representation theory. No numerical certificate needed. Requires
formalizing representation theory — substantial but well-understood.

### 3. Accept the axioms

Standard in formalization projects. Justified by numerical computation,
verifiable to arbitrary precision.

### 4. Probabilistic certificate

Formalize Freivalds' algorithm in Lean and prove the spectral gap bound holds
with probability > 1 - 2^{-256}. Rigorous but probabilistic.

## Reproduction

```bash
# Exact LDL^T entry growth experiments
uv run --with numpy --with networkx scripts/exact_ldlt_experiment.py

# Approximate LDL^T: error tolerance, Rump criterion, sharding analysis
uv run --with numpy --with networkx --with scipy scripts/approx_ldlt_experiment.py
```
