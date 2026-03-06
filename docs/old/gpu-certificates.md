> **OBSOLETE:** GPU certificate generation plan, not actively pursued.

# GPU-Accelerated Certificate Generation

Plan for generating PSD certificates for larger base expanders (up to n=65536, d=16)
using GPU-accelerated dense linear algebra.

## Motivation

We want a base expander on n=2^16=65536 vertices with degree d=16. The current
base expander (n=20736, d=12) was chosen to match D=12 in the zig-zag construction,
but n=2^16 with d=16 is a cleaner target: power-of-two vertex count, and degree 16
means the zig-zag family has degree D^2=256.

The certificate generator (`rust/certificate.rs`) is CPU-bound on two dense O(n^3)
operations: Cholesky factorization and triangular solve (TRSM). At n=20736 these are
feasible on a beefy CPU; at n=65536 they are not. GPUs provide 10-100x speedups
on exactly these operations.

## Current Pipeline (CPU)

The existing `certificate.rs` does:

1. **Graph generation** — random d-regular graph via configuration model + edge switching.
   O(n*d), negligible. Produces rotation map.

2. **M formation** — compute M = c1*I - c2*B^2 + c3*J as a dense f32 matrix.
   O(n^2*d), a few seconds even at n=65536. Sparse B is traversed row-by-row;
   output is dense n*n.

3. **Cholesky factorization** — in-place LLT of M via `faer`. O(n^3/3).
   **Dominant cost.** At n=20736 this takes ~minutes; at n=65536 it would take
   ~50 hours in f32.

4. **Streaming TRSM + pack** — for each block of 256 columns, solve L^T * X = I_block
   via `faer::triangular_solve`. O(n^2 * block_size) per block, O(n^3/2) total.
   Results are packed to i32 (multiply by L[j,j] and scale, round).

5. **Refinement** — two passes of greedy correction to reduce upper-triangular
   residuals in P = M * Z_int. O(n^2*d) total across all columns. Fast.

6. **Verification** — recompute P = M * Z_int column-by-column, check
   min_diag > eps_max * n*(n+1)/2 (Gershgorin condition). O(n^2*d) total. Fast.

7. **Base-85 encoding** — stream packed i32 blocks to `.b85` files. I/O bound.

Steps 3-4 are O(n^3) and dominate. Steps 5-6 are O(n^2*d) and are fast even on CPU.
Step 1 is trivially fast. Step 2 is O(n^2*d) — fast but produces a 16 GB matrix.

## Computational Budget at n=65536

| Step | FLOPs | CPU time (est.) | GPU time (est.) |
|------|-------|-----------------|-----------------|
| M formation | 7e10 | ~10s | (keep on CPU) |
| Cholesky (f32) | 9.4e13 | ~50h | ~80min (A100) |
| Cholesky (f64) | 9.4e13 | ~100h | ~160min (A100) |
| TRSM total | 1.4e14 | ~75h | ~2h (A100) |
| Refinement (2x) | 1.4e11 | ~2min | (keep on CPU) |
| Verification | 7e10 | ~1min | (keep on CPU) |

GPU estimates assume a single A100 at ~19.5 TFLOPS (f32) or ~9.7 TFLOPS (f64).
An H100 would be ~3x faster. Multi-GPU (4x) gives near-linear scaling for both
Cholesky (cuSOLVERMg) and TRSM (column-parallel).

## Memory Budget at n=65536

| Object | Size (f32) | Size (f64) |
|--------|-----------|-----------|
| Dense M (n*n) | 16 GB | 32 GB |
| TRSM block (n * 256) | 64 MB | 128 MB |
| Packed certificate (n*(n+1)/2 i32) | 8 GB | 8 GB |
| Certificate base-85 on disk | 10.7 GB | 10.7 GB |
| Rotation map | 32 MB | 32 MB |

Peak GPU memory: ~16 GB (f32) or ~32 GB (f64) for M alone. An 80 GB A100/H100
handles this comfortably. Even a 40 GB A100 works for f32.

Peak host memory: M is on GPU, so host needs only the TRSM block + packed output
buffer. Under 1 GB at any time (streaming).

## f32 vs f64 Precision

The current pipeline uses f32 for Cholesky, then refines the integer certificate
in i32/i64. This works at n=20736 because f32 has ~7 decimal digits of precision
and the entries of L^{-1} are moderate.

At n=65536, the risk is that accumulated f32 rounding in Cholesky degrades L enough
that the refinement step can't fix the residuals. Signs of trouble:

- `z_max_offdiag` grows (entries of L^{-1} get large)
- `global_eps_max` after refinement stays high
- Gershgorin margin drops below 1.0

**Strategy:** start with f32 (faster, less memory). If the Gershgorin margin is too
thin or verification fails, switch to f64. The code change is minimal — just swap
`Mat<f32>` to `Mat<f64>` for M and the TRSM solve. Everything downstream (packing,
refinement, verification) is already i32/i64 and unchanged.

f64 Cholesky halves GPU throughput and doubles memory, but at n=65536 it's still
well within a single 80 GB GPU.

## Proposed Architecture

The key insight: **only Cholesky and TRSM need the GPU.** Everything else stays
in the existing Rust code.

```
                        CPU                          GPU
                         │                            │
   1. Graph generation   │                            │
   2. M formation (sparse→dense)  ───upload M───►     │
                         │                     3. Cholesky (cuSOLVER potrf)
                         │                            │
   ┌─ for each block of 256 columns: ───────────────┐ │
   │  4a. Set up RHS identity block     ──upload──►  │ │
   │                                    4b. TRSM     │ │
   │  4c. Download solution  ◄──download──           │ │
   │  4d. Pack to i32 (CPU)                          │ │
   │  4e. Refine columns (CPU, i64)                  │ │
   │  4f. Verify columns (CPU, i64)                  │ │
   │  4g. Encode base-85, write to disk              │ │
   └─────────────────────────────────────────────────┘ │
                         │                            │
   7. Write rotation map │                            │
```

Steps 4d-4g remain on CPU because they use integer arithmetic and the existing
verified refinement/verification code. The GPU only handles floating-point dense
linear algebra where it has a massive advantage.

### Double-Buffering

The TRSM streaming loop can overlap GPU and CPU work. While the GPU solves
block k+1, the CPU packs/refines/verifies block k. With 256-column blocks,
there are n/256 = 256 blocks. Each GPU TRSM takes ~30s (A100 f32), and each
CPU pack+refine+verify takes a similar amount, so double-buffering roughly
halves the wall time.

```
GPU:  [TRSM block 0] [TRSM block 1] [TRSM block 2] ...
CPU:       idle       [pack/refine 0] [pack/refine 1] ...
```

Use two host-side buffers and two CUDA streams. Upload RHS for block k+1 while
downloading solution for block k.

### TRSM Block Size Tuning

The current block size of 256 columns was chosen for CPU cache efficiency. On GPU,
larger blocks may be better (cuBLAS TRSM is more efficient with wider matrices).
Experiment with 512, 1024, 2048. The memory cost is n * block_size * 4 bytes per
buffer, so even 2048 columns is only 512 MB (f32) — trivial on an 80 GB GPU.

Larger blocks also reduce the number of CPU-GPU synchronization points and improve
double-buffering efficiency.

## Rust Implementation

### Crate: `cudarc`

Use `cudarc` (v0.18+) for CUDA bindings. It provides:

- **cuSOLVER** `potrf` (Cholesky): safe-ish wrappers exist. Call
  `cusolverDnSpotrf` (f32) or `cusolverDnDpotrf` (f64).
- **cuBLAS** `trsm` (triangular solve): has `Gemm`/`Trsm` traits at the safe level.
  Call with `Side::Left`, `FillMode::Lower`, `Op::Transpose`, `Diag::NonUnit`.
- **Device memory management**: `CudaDevice::htod_copy` (host→device),
  `CudaDevice::dtoh_sync_copy` (device→host).
- **Multiple streams**: `CudaStream::new` for double-buffering.

`cudarc` is pre-alpha but functional for these well-established BLAS/LAPACK
operations. The API surface we need (potrf + trsm + memcpy) is small and stable.

### Code Structure

Keep `certificate.rs` as the CPU-only version (it still works for small graphs).
Create `certificate-gpu.rs` as a new cargo-script that:

1. Imports `cudarc` for GPU operations.
2. Reuses graph generation, rotation map, M formation from shared helper functions.
   (Extract these into a `certificate_common.rs` module, or just duplicate — the
   code is straightforward.)
3. Uploads M to GPU, calls `cusolverDnSpotrf` in-place.
4. Streams TRSM blocks: upload identity RHS, call `cublasStrsm`, download solution.
5. Packs, refines, verifies, and writes on CPU (identical to current code).

Since both scripts use `cargo +nightly -Zscript`, the GPU version just adds
`cudarc` as a dependency. No build system changes.

### Multi-GPU (Optional, for 4x+ speedup)

For multi-GPU Cholesky, use `cusolverMgPotrf` (cuSOLVER multi-GPU). This
distributes the matrix across GPUs in a 1D block-cyclic layout and runs
parallel Cholesky. `cudarc` has `sys`-level bindings for cuSOLVERMg.

For multi-GPU TRSM, simply assign different column blocks to different GPUs.
Each GPU holds a copy of L (or its portion) and solves its assigned columns
independently. No inter-GPU communication needed.

This is a second-phase optimization. Start with single-GPU.

## Certificate Size and Lean-Side Concerns

At n=65536, the certificate is ~10.7 GB of base-85 text. This creates downstream
challenges:

### Compilation Memory

The `bin_base85%` elaborator reads the `.b85` file into a `String` literal at
compile time. A 10.7 GB string literal will require significant memory during
Lean elaboration. The current 821 MB certificate for n=20736 already pushes
limits.

**Mitigation:** split the certificate into multiple chunks (e.g., 64 files of
~170 MB each). Each chunk is a separate `String` literal. The checker processes
chunks sequentially, never holding the full certificate in memory.

### `native_decide` Time

The Lean verifier (`checkCertificate`) runs via `native_decide`, which compiles
the checker + data to native code and runs it. At n=20736 this takes minutes
(dominated by the O(n^2*d) verification). At n=65536, the verification is
~10x more work ((65536/20736)^2 * (16/12) ≈ 13x), so maybe 30-60 minutes.
This is long but feasible as a one-time computation.

### Base Encoding

The current base-85 encoding uses 5 bytes per i32 value. Switching to base-128
encoding (codepoints 0-127, 1 byte each) would allow ~4.7 bytes per i32
(ceil(32/7) = 5 digits, same count — so no savings for i32). For the certificate
data, the encoding overhead is not the bottleneck. Stick with base-85.

### Disk and Git

10.7 GB of certificate data should NOT be checked into git. The current approach
(`.b85` files in `data/`, gitignored, regenerated on demand) scales fine.
`ensureCertificateData` checks for the files and tells the user to regenerate
if missing.

## Precision Safety Net

The certificate is self-verifying: after generation, the Rust code checks the
Gershgorin condition (min_diag > eps_max * n*(n+1)/2) using exact i64 arithmetic.
If this check fails, the certificate is invalid regardless of how it was generated.

This means GPU floating-point imprecision cannot produce a wrong certificate —
it can only produce a certificate that fails verification. The safety net is:

1. Generate with f32 GPU Cholesky.
2. Pack + refine on CPU (exact integer arithmetic).
3. Verify on CPU (exact integer arithmetic).
4. If verification fails, retry with f64 GPU Cholesky.
5. If f64 also fails, increase scale or adjust coefficients.

No trust is placed in the GPU's floating-point accuracy beyond "good enough to
produce a certificate that passes exact integer verification."

## Experimental Plan

### Phase 1: Single-GPU f32 (first day)

1. Install CUDA toolkit on the GPU instance.
2. Write `certificate-gpu.rs` with `cudarc` dependency.
3. Test at n=1728 (known-good baseline, seconds on GPU).
4. Test at n=20736 (compare output with CPU version — certificates should match
   or both pass verification).
5. Time the Cholesky and TRSM separately to validate performance estimates.

### Phase 2: Scale to n=65536 (second day)

1. Run at n=65536, d=16 with f32.
2. Check Gershgorin margin. If it passes, we're done.
3. If margin is thin or verification fails, switch to f64.
4. Tune TRSM block size (try 256, 512, 1024, 2048).
5. Implement double-buffering if TRSM streaming is the bottleneck.

### Phase 3: Lean Integration (third day)

1. Generate the certificate data files (`rot_map.b85`, `cert_z.b85`).
2. Create `Random/Random65536.lean` following the pattern of `Random20736.lean`.
3. Handle the large certificate: split into chunks if needed, or test whether
   a single 10.7 GB string works (it probably won't — split it).
4. Run `native_decide` for involution check and certificate verification.
5. Prove `spectralGap graph <= beta_n / d` via `certificate_bridge`.

### Phase 4: Multi-GPU (optional)

Only if single-GPU is too slow (>4 hours total). Use cuSOLVERMg for distributed
Cholesky. Assign TRSM column blocks to separate GPUs.

## Risks

1. **f32 precision at n=65536.** Cholesky condition number grows with n. The
   refinement step can fix moderate rounding errors, but if L is badly corrupted
   by f32 Cholesky, refinement won't save it. Fallback: f64. Cost: 2x memory,
   2x time.

2. **`cudarc` API stability.** The crate is pre-alpha. Pin a specific version
   in `Cargo.toml`. The API surface we need (potrf, trsm, memcpy) is unlikely
   to change.

3. **Lean compilation with 10+ GB data.** The `bin_base85%` elaborator may OOM
   or be extremely slow. Mitigation: chunk the certificate into multiple files.
   Worst case: modify the checker to process chunks, requiring a small change
   to `CertCheck.lean` and re-proving the bridge.

4. **`native_decide` wall time.** At n=65536, verification might take an hour.
   This is a one-time cost per certificate. Acceptable, but annoying during
   development. Consider adding a fast-path `#eval` check before committing
   to `native_decide`.

5. **Graph generation.** The configuration model + edge switching for a
   16-regular graph on 65536 vertices should be fast (seconds). But if edge
   switching gets unlucky, it could take many iterations. The current code
   has a 100*n_edges iteration cap. This has never been a problem in practice.
