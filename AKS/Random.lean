/-
  # Base Expander for the Zig-Zag Construction

  The iterated zig-zag construction (`zigzagFamily` in `ZigZag.lean`) requires
  a concrete "seed" expander: a D-regular graph on D⁴ vertices with spectral
  gap bounded by some constant β < 1.

  The specific graph defined below was chosen by fair dice roll.
  It is guaranteed to be random.

  More precisely: a random D-regular graph on D⁴ vertices was generated
  via the configuration model (`scripts/random-graph`), its spectral gap
  was verified numerically, and it was exported as an explicit rotation map.
  The spectral gap bound is currently axiomatized (see § Certificate below
  for why verified certificates are impractical for random graphs).

  ## Certificate for Spectral Gap Verification

  We want to certify: `spectralGap G ≤ β`, i.e., all non-trivial eigenvalues
  λᵢ of A satisfy |λᵢ| ≤ βD. This is equivalent to `C|_{1⊥} ≽ 0` where
  `C = (βD)²·I - A²` (integer matrix when `βD ∈ ℤ`; e.g., β = 7/12, βD = 7).

  ### Certificate approaches considered

  **Dense certificates (O(n²) data, impractical for n = D⁴):**
  - LDL^T / sparse Cholesky of `C|_{1⊥}`: Random expanders have high treewidth
    (~O(n)), so Cholesky fill-in is O(n²) regardless of elimination ordering.
  - Eigenvector certificate: n rational eigenvectors × n entries each = O(n²).
  - Gram matrix: G^T G = C requires O(n²) entries in G.

  **Scaled diagonal dominance (SDD):** Find D such that DMD is diagonally
  dominant, proving M = αI - A ≽ 0. Fails because the diagonal dominance
  constraint sums to α ≥ D over all vertices (double-counting in D-regular
  graphs), but we need α = 7 < D = 12.

  **Edge-decomposable PSD:** Write M = Σ (2×2 PSD blocks on edges) + diag(u).
  Fails because AM-GM gives each edge cost ≥ 2 (from a_{ij}·a_{ji} ≥ 1),
  total ≥ 2|E| = nD, but the budget from the diagonal is only nα < nD.

  **Trace method (O(1) data, but infeasible verification):**
  - Certificate: `tr(A^{2k})` for k ≈ 91 (to get (n-1)^{1/(2k)} · max|λ| ≤ βD).
  - Verification requires computing tr(A^{2k}), which is O(n² · k) — infeasible in
    the Lean kernel for n = 20736, k = 91.
  - For small k (e.g., k = 2, walks of length 4), verification is ~n·D⁴ ≈ 4·10⁸
    comparisons (borderline feasible), but the bound is far too loose
    (gives max|λ| ≤ 40 instead of the needed ≤ 7).

  **Krylov / Lanczos (O(n) data, but exact arithmetic infeasible):**
  Full Lanczos (k = n-1 steps) from a starting vector produces a tridiagonal
  matrix T whose eigenvalues equal those of A|_{1⊥}. Certificate would be
  q₁ + tridiagonal T + LDL^T of βD·I ± T. Size O(n), no fill-in.
  Problem: exact integer Lanczos has exponential coefficient growth (~D^k bits
  at step k). Experimentally on n=24: integers reach 1.4M bits by step 12,
  with each step ~3.7× larger. Extrapolating to n=20736: infeasible.
  (See `scripts/krylov-cert` for experiments.)

  **Current approach: axioms.**
  Standard in formalization projects. The axioms are justified by numerical
  computation in Python (`scripts/random-graph`). The spectral gap can be
  verified to arbitrary precision using interval arithmetic (mpmath).

  ### Approaches under investigation

  **Parallel dense LDL^T via sharded subfiles.**
  The LDL^T of `C|_{1⊥}` is O(n²) ≈ 4·10⁸ entries, but verification can be
  split into thousands of independent files generated during `lake build`.
  Each subfile checks a few rows: verify that L[i,:] · D · L[j,:] = C[i,j].
  With `decide +kernel`, each shard might take seconds. The build system
  runs shards in parallel. Need to estimate: total data (~3 GB?), per-shard
  cost, and whether Lean/Lake can handle ~10K generated `.olean` files.

  **Eigenspace sparsity.**
  If the second eigenvalue of a random 12-regular graph has high multiplicity,
  the eigenspace could be described with sparse data (a few sparse eigenvectors).
  Certificate: sparse eigenvectors V, proof that AV = λV, and a spectral gap
  bound on the complement (via trace or Cauchy interlacing). Need numerical
  experiments: what are the eigenvalue multiplicities of random 12-regular
  graphs on 20736 vertices? Are the eigenvectors sparse in any basis?

  ### Open question: algebraic base expanders
  Cayley graphs of explicit groups (e.g., SL₂(𝔽_p) with generators) have
  spectral gaps provable from representation theory rather than numerical
  computation. This would replace the axioms with a purely algebraic proof,
  but requires substantial formalization of representation theory.
-/

import AKS.RegularGraph


/-! **Base Expander Axioms** -/

/-- A concrete base expander: 12-regular on 20736 = 12⁴ vertices.

    D = 12 is the minimum degree for which the precise RVW iteration converges
    (requires β² < 1/3, and Alon–Boppana gives β ≥ 2√(D−1)/D; solving
    4(D−1)/D² < 1/3 gives D > 10.9, and parity requires D even).

    Currently axiomatized. Generated by `scripts/random-graph -d 12`. -/
axiom baseExpander : RegularGraph 20736 12

/-- The spectral gap of the base expander is at most 5/9 ≈ 0.556.

    This is just above the Alon–Boppana bound 2√11/12 ≈ 0.553, so random
    12-regular graphs on 20736 vertices achieve this with high probability.
    The precise RVW fixed point with β = 5/9 gives c ≈ 0.928 < 1.

    Currently axiomatized; justified by numerical computation. -/
axiom baseExpander_gap : spectralGap baseExpander ≤ 5/9
