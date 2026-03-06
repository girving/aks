# Certificate Bridge

Detailed architecture, conventions, and proof tactics for the certificate bridge subsystem.

## Overview

Base expander graphs are certified via davidad's triangular-inverse method + `native_decide`. Data is base-85 or base-128 encoded as `String` literals (compact `Expr` nodes visible to kernel). Pipeline: `Random/Cert.lean` (checker) → `Random/Bridge/WalkBound.lean` (abstract theory) → `Random/Bridge/Bridge.lean` (bridge) → `Random/Concrete/{Random16,Random1728,Random20736,Random65536}.lean` (per-size graphs). Data files in `data/{n}/` (`.b85`/`.b128`/`.b128x5` text, `.gitignore`d) — Rust writes encoded data directly so Lean just reads the text as-is.

See [`docs/bridge-proof-plan.md`](bridge-proof-plan.md) for the original design document.

## Architecture

### `Random/Bridge/WalkBound.lean` — Walk Bound → Spectral Gap (~89 lines)
Abstract operator theory connecting walk bounds to spectral gap bounds. Imports only `Graph/Regular.lean`:
1. **`spectralGap_le_of_walk_bound`** — quadratic walk bound on mean-zero vectors → `spectralGap G ≤ √(c₁/(c₂·d²))`
2. **`sqrt_coeff_le_frac`** — coefficient arithmetic: `c₁·βd² ≤ c₂·βn²` → `√(c₁/(c₂·d²)) ≤ βn/(βd·d)`

### `Random/Bridge/` — Certificate Bridge Infrastructure
Connects the decidable `checkCertificateSlow` predicate to spectral gap bounds:
- **`Defs.lean`** — proof-only pure recursive definitions (`adjMulPure`, `pEntryPure`, `kEntryPure`, etc.) (~100 lines)
- **`Bridge.lean`** — main bridge theorem chaining all layers (~870 lines)
- **`FastProof.lean`** — proves `checkCertificate = checkCertificateSlow` (~55 lines)
- **`SpectralMatrix.lean`** — Layer 1: spectral matrix M PSD → walk bound (~186 lines)
- **`DiagDominant.lean`** — Layer 2: Hermitian + strictly diag-dominant → PSD (~123 lines)
- **`ColumnNormBridge.lean`** — imperative column norm checker = pure recursive version (~1538 lines)
- **`Read.lean`** — `ascii_file%` elaborator (reads `.b85` text files), `loadBase85` (runtime), `ensureCertificateData` (~55 lines)

### `Random/Concrete/` — Base Expander Instances
Concrete base expander certified via davidad's triangular-inverse method:
1. **`Random65536.graph`** — concrete `RegularGraph 65536 16`, the production base expander (β = 17/32 = 0.53125)
2. **`Random65536.gap`** — spectral gap ≤ 17/32 via `certificate_bridge_b128x5` (fully proved, 6.4 GB b128x5 certificate with c₁=650, `native_decide`)
3. **`Specific.lean`** — concrete spectral gap conditions: β=17/32, c=7/8, 6-step squaring chain for c^64 ≤ 1/1000

### `Random/Bench/` — Benchmarks, Tests, and Profiles
Not part of the proof. Contains optimization variants (`CertFast`, `CertV2`, `CertV7`, `CertParallel`) and profiling tools. Run via `scripts/bench` or `lake exe cert-{bench,test,profile}`.

## Bridge Decomposition

Three lemmas (all proved, 0 sorry):
1. **`certificate_implies_walk_bound`**: certificate → walk bound on mean-zero vectors
2. **`spectralGap_le_of_walk_bound`** (in `Random/Bridge/WalkBound.lean`): walk bound → `spectralGap` bound
3. **`sqrt_coeff_le_frac`** (in `Random/Bridge/WalkBound.lean`): coefficient arithmetic

`certificate_bridge` chains all three.

## Conventions

**Do not use `@[csimp]` in `Random/Cert.lean`.** `Random.Cert` is a separate precompiled library (`precompileModules := true`) that contains only definitions, no proofs. `@[csimp]` requires a proof that the replacement equals the original, which would force proofs into the precompiled module and break modularity. Instead, prove the bridge theorem (`checkCertificate_eq_slow`) in a separate file (`Random/Bridge/FastProof.lean`) that imports both `Random.Cert` and Mathlib.

**Never change fast code to make proofs easier.** `Random/Cert.lean` contains optimized imperative code (`checkCertificate`, `checkColumnNormBound`, `mulAdjWith`, etc.) that must stay exactly as-is. The job is to PROVE the existing fast code correct via bridge theorems, not to modify it. When a proof about imperative code is hard, discuss the difficulty with the user — don't silently switch to "make the code easier to prove about" by adding `native_decide` calls, slowing down the fast path, or replacing imperative code with pure equivalents. The `native_decide` in `Random/Concrete/Random*.lean` should only be on `checkCertificate`; everything else must be derived via structural proofs.

## Proof Tactics

**Ghost state elimination for imperative buffer reuse.** When imperative code reuses buffers across loop iterations (e.g., `checkPSDColumnsFull` with `bz`/`zCol`): (1) define a "big state" including all mutable vars (visible + ghost), (2) show the ghost state is fully reset/overwritten at the start of each iteration, (3) prove `project(bigStep ghost_any) = smallStep(project input)` — ghost doesn't affect output, (4) by induction on the list, `project(foldl bigStep) = foldl smallStep (project init)`. Key helpers: `foldl_simulation` (generic projection through foldl), `foldl_mprod_to_prod` (MProd↔Prod swap).

**Involution-based symmetry for counting folds.** To prove `f(v,w) = f(w,v)` for graph-based counting: (1) flatten nested counting fold to flat fold over `{0,...,N-1}`, (2) apply `fold_sum_invol` (involution preserves counting folds, proved by strong induction + `fold_sum_replace`), (3) transform predicates using round-trip properties of the involution, close with `and_comm`. See `portCount_symm` in `ScatterBridge.lean`.

**Scatter = gather under `NeighborSymm`.** Scatter-based accumulation (loop over sources k, distribute `z[k]` to `bz[neighbors[k*d+p]]`) equals gather-based (`mulAdjPre`: loop over targets i, collect from `neighbors[i*d+p]`) when adjacency is symmetric. The bridge goes through `portCount_symm` (port counts are symmetric under rotation involution). See `scatterMulAdj_eq_mulAdjPre` in `ScatterBridge.lean`.

## Certificate Data and GCS

Certificate data lives in `data/{n}/` (gitignored). `scripts/download-certificates` fetches prebuilt certs from `gs://aks-cert/`. The `ensureCertificateData` Lean function (called via `#eval`) tries the download script first, then falls back to generating with `rust/certificate.rs`.

### Formats

- **b85** — base-85 encoded i32 (5 ASCII chars per entry, full symmetric matrix). Used for small sizes (n=16, n=1728).
- **b128** — base-128 encoded i32 (4 bytes per entry, off-diagonal only). ~20% more compact than b85. Used for medium sizes (n=20736). Requires `checkCertificateB128` / `certificate_bridge_b128`.
- **b128x5** — base-128 encoded i40 (5 bytes per entry, off-diagonal only). Range ±17 billion vs ±134 million for b128. Used for n=65536 with c₁=650 (large c₁ produces entries exceeding i32 range). Requires `checkCertificateB128x5` / `certificate_bridge_b128x5`.
- **rot_map.b85** — rotation map, standard b85 format (10 bytes per half-edge: 5-byte vertex + 5-byte port). Small (~2.4 MB for n=20736, ~10 MB for n=65536).
- **rot_map.b85c** / **Random/Concrete/Rot{n}{a,b,c}.lean** — compact rotation map (4 bytes per half-edge: 3 b85 vertex digits + 1 b85 port digit). 60% smaller than b85. Inlined as string literals in Lean source files, expanded to standard b85 by `compactToB85` at native-code evaluation time. Split into three files to stay under Lean's ~1 MB string literal limit. Regenerate with `scripts/gen-rot-lean`.

### GCS naming convention

`{type}-n{N}-d{D}[-key{val}]...{.ext}[.xz]`. Non-default params appended as `-key{val}`. Large certs are xz-compressed (`.b128.xz`).

### xz compression

Certificate data is low-entropy integer residuals (off-diagonal entries of Z = L⁻¹ after Cholesky). xz -9 gives ~31-35% size reduction:

| Size | Format | Raw | xz -9 | Ratio | Decompress (16 threads) |
|------|--------|-----|-------|-------|-------------------------|
| n=20736 | b128 | 821 MB | 532 MB | 65% | ~4s |
| n=65536 (c₁=650) | b128x5 | ~8.2 GB | 6.4 GB | ~78% | ~40s |

Compression is CPU-intensive (`xz -9 -T16`); decompression is fast (`xz -d -T0`). The download script checksums the `.xz` file, then decompresses in-place.

### Parameter reference

`c₃` (the J coefficient in M = c₁I - c₂B² + c₃J) is computed by `compute_j_coeff` in `rust/certificate.rs`, NOT set by `--refine`. `--refine` controls iterative refinement passes in Cholesky (improves certificate quality, doesn't affect the Lean checker params). For current sizes, `c₃ = 2`.

## c₁ Tuning and the β=17/32 Improvement

The spectral gap bound depends on c₁ (the diagonal dominance coefficient in M = c₁I - c₂B² + c₃J). The bound formula is `β ≤ √(c₁/(c₂·d²))`, so larger c₁ gives a tighter gap — but also produces larger certificate entries that require wider encoding.

### History

| c₁ | β bound | c (RVW fixed point) | Squarings | Encoding | Cert size |
|----|---------|---------------------|-----------|----------|-----------|
| 8·c₂·(d-1) = 1080 (default) | 23/40 = 0.575 | 124/125 = 0.992 | 10 | b128 (4-byte) | 8.0 GB |
| 650 | 17/32 = 0.53125 | 7/8 = 0.875 | 6 | b128x5 (5-byte) | 6.4 GB |

### Why c₁=650 works

The certificate proves `c₁·‖z‖² ≤ c₂·(Bz)²` for all mean-zero z, where B is the walk operator. The gap bound is `β ≤ √(c₁/(c₂·d²))`. With c₂=9, d=16:

- `√(650 / (9·256)) = √(650/2304) ≈ 0.5312`
- Rationalized: `650·4 = 2600 ≤ 2601 = 9·289 = c₂·(17)²`, so `β ≤ 17/(2·16) = 17/32`

The slack is just 1 integer unit (2600 ≤ 2601), making 17/32 essentially the tightest rational bound achievable at c₁=650.

### Impact on squarings

The dramatic improvement from 10 to 6 squarings comes from c being much further from 1:
- c = 124/125: need c^(2^p) ≤ 1/1000, so (124/125)^1024 via 10 squarings
- c = 7/8: need (7/8)^64 ≤ 1/1000 via 6 squarings

This reduces `halverDepth` from `2^(2048·a)·(2^(4a)+1)` to `2^(128·a)·(2^(4a)+1)`. For a=4: from `2^8192 · 65537` to `2^512 · 65537`.

### Why 5-byte encoding was needed

The default c₁ formula (`8·c₂·(d-1) = 1080`) is chosen so certificate entries (Cholesky residuals of L⁻¹) fit in i32 (±2.1 billion). At c₁=650, the diagonal dominance is weaker relative to off-diagonal terms, producing some entries exceeding i32 range. The b128x5 format uses 5 base-128 bytes per entry (range ±17.2 billion), adding 25% to per-entry size but the certificate is actually smaller overall (6.4 GB vs 8.0 GB) due to the `f64` precision option producing tighter residuals with `scale=2100000000`.

## Partition Benchmarks

Benchmarked 4 column partition strategies × 3 task counts on a 16-core machine (`Random/Bench/BenchDecomp.lean`). The PSD checker assigns columns to parallel tasks; each task processes its columns sequentially, computing Cholesky column norms. Work per column j is O(n − j), so naive contiguous partitions give severe load imbalance.

**Strategies tested:**
- **interleaved** — current `roundRobinPartition`: column j → task j % T
- **contiguous** — column j → task j·T/n (poor load balance, good locality)
- **balanced** — contiguous blocks with boundaries at n·√(t/T) for equal work
- **block-256** — blocks of 256 columns round-robin to tasks

### n=20736 (d=12, b128 certificate)

| Strategy | tasks=4 | tasks=8 | tasks=16 |
|----------|---------|---------|----------|
| **interleaved** | 16.0s | **11.6s** | 15.5s |
| contiguous | 27.2s | 16.5s | 14.8s |
| balanced | 16.5s | 11.9s | 15.5s |
| block-256 | 16.5s | 12.1s | 15.5s |

### n=65536 (d=16, b128 certificate)

| Strategy | tasks=4 | tasks=8 | tasks=16 |
|----------|---------|---------|----------|
| **interleaved** | 209.7s | **121.4s** | 156.4s |
| contiguous | 355.5s | 203.1s | 154.5s |
| **balanced** | 210.3s | **122.3s** | 156.5s |
| block-256 | 211.3s | 123.2s | 157.3s |

### Key findings

1. **tasks=8 is optimal** — ~1.7x faster than tasks=4, ~1.3x faster than tasks=16. The sweet spot is roughly cores/2, not cores.
2. **Partition strategy barely matters** once load is balanced. Interleaved ≈ balanced ≈ block-256 (within 2%).
3. **Naive contiguous is terrible at low task counts** (355s vs 210s at tasks=4) due to load imbalance, but converges at tasks=16.
4. **tasks=16 regresses 29% vs tasks=8** despite 16 cores being available. Per-task overhead (buffer zeroing: n writes per column) and cache contention dominate.

The current production default is `roundRobinPartition n 64` (set in `checkCertificate`), which would perform even worse than tasks=16. Tuning to tasks=8 would give a ~1.3–1.7x speedup on `native_decide` certificate checks.

## Proof Status

`Random/Bridge/ScatterBridge.lean`, `Random/Bridge/FusedBridge.lean`, `Random/Bridge/FastProof.lean` — all 0 sorry. Base expander gap fully proved (b128x5 PSD certificate with c₁=650 verified by `native_decide`, β ≤ 17/32).
