# Trusted Codebase

This documents every mechanism in the AKS project that extends trust beyond the Lean kernel. The Lean kernel is the ultimate arbiter of proof correctness; anything outside it is part of the "trusted codebase" whose bugs could compromise soundness.

## Axiom inventory

The top-level theorem `Random65536.gap` (and transitively `seiferas_sorting_networks_exist_pow2`) depends on exactly these axioms:

```
propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound
```

Verified at compile time by `AKS/Seiferas.lean`:
```lean
#guard_msgs in #print axioms Random65536.gap
```

### Standard Lean/Mathlib axioms

- **`propext`** — Propositional extensionality: `(p ↔ q) → p = q`
- **`Classical.choice`** — Axiom of choice (used by Mathlib)
- **`Quot.sound`** — Quotient soundness: `a ~ b → Quot.mk a = Quot.mk b`

These are used by every non-trivial Mathlib-based project and are widely accepted.

### Native evaluation axioms

- **`Lean.ofReduceBool`** — Trusted boolean reduction via the native evaluator
- **`Lean.trustCompiler`** — Trust that the native compiler correctly implements Lean semantics

These are introduced by `native_decide`, which compiles a decidable proposition to native code, runs it, and accepts the result. In this project, `native_decide` is used in `Random/Concrete/Random65536.lean` for two proofs:

1. **`involution_check`** — The rotation map is an involution (`checkInvolutionSpec rotData 65536 16 = true`)
2. **`certificate_passes`** — The triangular certificate is valid (`checkCertificateB128 rotData certData 65536 16 760 9 2 2000000000 = true`)

The certificate checker (`Random/Cert.lean`) is pure Lean code with no `@[extern]`, `sorry`, or `axiom` declarations. The `native_decide` trust is that the Lean compiler correctly compiles this checker and the `cachedString` data loader, and that the CPU correctly executes the result.

## C FFI (`Random/Cert/mmap_string.c`)

Three functions bypass the Lean kernel via `@[extern]` (declared in `Random/Cert/ReadFFI.lean`):

| Function | Type | Purpose |
|---|---|---|
| `mmapReadAscii` | `String → IO String` | Read a file into a Lean `String` via mmap |
| `mmapPrepare` | `String → IO (Unit → String)` | Read + cache, return pure thunk |
| `cachedString` | `String → String` | Pure accessor with lazy mmap fallback |

### What the C code does

1. Opens the source file, validates every byte < 128 (ASCII)
2. Copies validated data to a private temporary file (`mkstemp` + immediate `unlink`)
3. Uses split mmap: anonymous page for `lean_string_object` header, tmpfile pages for data
4. Forges a persistent Lean string (`m_rc = 0`) backed by read-only mmap'd pages
5. Caches results by path (max 16 entries) for `cachedString`

### Why this is safe

- **Immutability:** Data pages are mapped read-only; header page is made read-only after initialization. Any accidental write causes SIGSEGV.
- **Isolation:** The tmpfile is unlinked immediately, so no other process can open or modify the validated data.
- **Validation:** Every byte is checked `< 128` in a streaming loop before being written to the tmpfile. Non-ASCII bytes cause an IO error.
- **Layout correctness:** A `_Static_assert` verifies that `lean_string_object` is exactly 32 bytes, matching our header layout assumptions.
- **Persistence:** `m_rc = 0` makes the string immortal — `lean_inc`/`lean_dec` are no-ops, preventing use-after-free.

### What could go wrong

- A bug in `mmap_string.c` (e.g., incorrect header field, wrong page size calculation) could corrupt the Lean runtime.
- A bug in `mkstemp`/`mmap`/`mprotect` implementations (kernel bugs) could violate isolation or immutability.
- `cachedString` presents an impure operation (file I/O) as a pure function. This is sound because the file contents are deterministic for a given path and the project never modifies data files during a build.

### Scope

The C code is ~150 lines of straightforward syscall wrapping. It is exercised by 19 unit tests in `Random/Bench/TestMmap.lean` covering happy paths, error conditions, edge cases (empty files, page-aligned sizes, non-ASCII bytes, permission denied, buffer boundaries).

## What is NOT in the trusted codebase

### Certificate bridge proofs

The bridge from `checkCertificateB128 ... = true` to `spectralGap graph ≤ β` is **fully proved** in Lean (0 `sorry`). The bridge is decomposed across:

- `Random/Bridge/SpectralMatrix.lean` — PSD matrix implies walk bound
- `Random/Bridge/DiagDominant.lean` — Diagonal dominance and invertibility
- `Random/Bridge/Bridge.lean` — Checker predicates to matrix PSD
- `Random/Bridge/WalkBound.lean` — Walk bounds to spectral gap

These are ordinary Lean proofs verified by the kernel. A bug here would be caught by the type checker.

### Random/Cert.lean

The certificate checker is pure Lean code compiled to a shared library via `precompileModules := true`. It contains no `@[extern]`, `sorry`, or trust-extending mechanisms. The precompilation is a performance optimization (avoids recompiling for each `native_decide`), not a trust extension — the same code runs whether precompiled or not.

### Zig-zag product, expander families, separator construction

All fully proved or sorry'd with correct statements. Sorry'd theorems are honest placeholders (the statement is the claim, the `sorry` acknowledges it's unproved). No trust extension is needed for sorry'd theorems — they are simply unfinished work.

### `ascii_file%` elaborator

The `ascii_file%` term elaborator (in `Random/Bridge/Read.lean`) runs at elaboration time, reads a file via `mmapReadAscii`, and produces a kernel-visible `String` literal via `Lean.mkStrLit`. Since the result is a literal that the kernel can inspect, this does not extend trust — the kernel sees the actual string value. Used only for small data files in `Random/Concrete/`.

## `sorry-gate` enforcement

`scripts/sorry-gate` blocks `sorry`, `#exit`, `native_decide`, and `axiom` in fully-proved directories. Protected paths are listed in `DENY_ALL` inside the script. The pre-commit hook runs `sorry-gate` automatically, preventing regressions in proved code.

## Trust summary

| Component | Trust level | Verified by |
|---|---|---|
| Lean 4 kernel (v4.27.0) | Foundation | Lean developers, community |
| Lean native evaluator | Axiom (`trustCompiler`) | `#guard_msgs` axiom checks |
| Mathlib (v4.27.0) | Kernel-checked | Lean kernel |
| `Random/Cert.lean` | Kernel-checked | Lean kernel, `native_decide` |
| Certificate bridge | Kernel-checked | Lean kernel (0 sorry) |
| `Random/Cert/mmap_string.c` | Manual review | 19 unit tests, `_Static_assert` |
| Data files (`data/*/`) | Deterministic | Generated by `rust/certificate.rs`, verified by `native_decide` |
