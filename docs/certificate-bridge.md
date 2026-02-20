# Certificate Bridge

Detailed architecture, conventions, and proof tactics for the certificate bridge subsystem.

## Overview

Base expander graphs are certified via davidad's triangular-inverse method + `native_decide`. Data is base-85 encoded as `String` literals (compact `Expr` nodes visible to kernel). Pipeline: `CertCheck.lean` (checker) → `Cert/WalkBound.lean` (abstract theory) → `Cert/Bridge.lean` (bridge) → `Random/{16,1728,20736}.lean` (per-size graphs). Data files in `data/{n}/` (`.b85` base-85 text, `.gitignore`d) — Rust writes base85 directly so Lean just reads the text as-is.

See [`docs/bridge-proof-plan.md`](bridge-proof-plan.md) for the original design document.

## Architecture

### `AKS/Cert/WalkBound.lean` — Walk Bound → Spectral Gap (~89 lines)
Abstract operator theory connecting walk bounds to spectral gap bounds. Imports only `Graph/Regular.lean`:
1. **`spectralGap_le_of_walk_bound`** — quadratic walk bound on mean-zero vectors → `spectralGap G ≤ √(c₁/(c₂·d²))`
2. **`sqrt_coeff_le_frac`** — coefficient arithmetic: `c₁·βd² ≤ c₂·βn²` → `√(c₁/(c₂·d²)) ≤ βn/(βd·d)`

### `AKS/Cert/` — Certificate Bridge Infrastructure
Connects the decidable `checkCertificateSlow` predicate to spectral gap bounds:
- **`Defs.lean`** — proof-only pure recursive definitions (`adjMulPure`, `pEntryPure`, `kEntryPure`, etc.) (~100 lines)
- **`Bridge.lean`** — main bridge theorem chaining all layers (~870 lines)
- **`FastProof.lean`** — proves `checkCertificateFast = checkCertificateSlow` (~55 lines)
- **`SpectralMatrix.lean`** — Layer 1: spectral matrix M PSD → walk bound (~186 lines)
- **`DiagDominant.lean`** — Layer 2: Hermitian + strictly diag-dominant → PSD (~123 lines)
- **`ColumnNormBridge.lean`** — imperative column norm checker = pure recursive version (~1538 lines)
- **`Read.lean`** — `bin_base85%` elaborator (reads `.b85` text files), `loadBase85` (runtime), `ensureCertificateData` (~55 lines)

### `AKS/Random/` — Base Expander Instances
Concrete base expander certified via davidad's triangular-inverse method:
1. **`Random20736.graph`** — concrete `RegularGraph 20736 12`, rotation map verified by `native_decide`
2. **`Random20736.gap`** — spectral gap ≤ 10/12 via `certificate_bridge` (fully proved, 821 MB PSD certificate verified by `native_decide`)

### `Bench/` — Benchmarks, Tests, and Profiles
Not part of the proof. Contains optimization variants (`CertFast`, `CertV2`, `CertV7`, `CertParallel`) and profiling tools. Run via `scripts/bench` or `lake exe cert-{bench,test,profile}`.

## Bridge Decomposition

Three lemmas (all proved, 0 sorry):
1. **`certificate_implies_walk_bound`**: certificate → walk bound on mean-zero vectors
2. **`spectralGap_le_of_walk_bound`** (in `Cert/WalkBound.lean`): walk bound → `spectralGap` bound
3. **`sqrt_coeff_le_frac`** (in `Cert/WalkBound.lean`): coefficient arithmetic

`certificate_bridge` chains all three.

## Conventions

**Do not use `@[csimp]` in `CertCheck.lean`.** `CertCheck` is a separate precompiled library (`precompileModules := true`) that contains only definitions, no proofs. `@[csimp]` requires a proof that the replacement equals the original, which would force proofs into the precompiled module and break modularity. Instead, prove the bridge theorem (`checkCertificateFast_eq_slow`) in a separate file (`AKS/Cert/FastProof.lean`) that imports both `CertCheck` and Mathlib.

**Never change fast code to make proofs easier.** `CertCheck.lean` contains optimized imperative code (`checkCertificateFast`, `checkColumnNormBound`, `mulAdjWith`, etc.) that must stay exactly as-is. The job is to PROVE the existing fast code correct via bridge theorems, not to modify it. When a proof about imperative code is hard, discuss the difficulty with the user — don't silently switch to "make the code easier to prove about" by adding `native_decide` calls, slowing down the fast path, or replacing imperative code with pure equivalents. The `native_decide` in `Random*.lean` should only be on `checkCertificateFast`; everything else must be derived via structural proofs.

## Proof Tactics

**Ghost state elimination for imperative buffer reuse.** When imperative code reuses buffers across loop iterations (e.g., `checkPSDColumnsFull` with `bz`/`zCol`): (1) define a "big state" including all mutable vars (visible + ghost), (2) show the ghost state is fully reset/overwritten at the start of each iteration, (3) prove `project(bigStep ghost_any) = smallStep(project input)` — ghost doesn't affect output, (4) by induction on the list, `project(foldl bigStep) = foldl smallStep (project init)`. Key helpers: `foldl_simulation` (generic projection through foldl), `foldl_mprod_to_prod` (MProd↔Prod swap).

**Involution-based symmetry for counting folds.** To prove `f(v,w) = f(w,v)` for graph-based counting: (1) flatten nested counting fold to flat fold over `{0,...,N-1}`, (2) apply `fold_sum_invol` (involution preserves counting folds, proved by strong induction + `fold_sum_replace`), (3) transform predicates using round-trip properties of the involution, close with `and_comm`. See `portCount_symm` in `ScatterBridge.lean`.

**Scatter = gather under `NeighborSymm`.** Scatter-based accumulation (loop over sources k, distribute `z[k]` to `bz[neighbors[k*d+p]]`) equals gather-based (`mulAdjPre`: loop over targets i, collect from `neighbors[i*d+p]`) when adjacency is symmetric. The bridge goes through `portCount_symm` (port counts are symmetric under rotation involution). See `scatterMulAdj_eq_mulAdjPre` in `ScatterBridge.lean`.

## Proof Status

`ScatterBridge.lean`, `FusedBridge.lean`, `FastProof.lean` — all 0 sorry. Base expander gap fully proved (821 MB PSD certificate verified by `native_decide`).
