# Lean `module` System Guide

This documents how the AKS project uses Lean 4's `module` system (introduced in v4.27.0) to control `.olean` serialization and reduce build artifact sizes.

## Why modules?

Without `module`, Lean serializes all `def` bodies into `.olean` files. For `Random65536.lean`, this produced an **8.1 GB** `.olean` because the certificate data (~4 GB of base-85/base-128 encoded strings) was embedded as string literals via `ascii_file%`. Downstream files that imported `Random65536` had to read this 8 GB file at import time, causing OOM crashes on machines without swap.

With `module`, the `.olean` contains only public interfaces (48 KB), and private def bodies go to `.olean.private` (read only by same-package imports that need them). Combined with `cachedString` (which avoids embedding data in the IR), all build artifacts dropped from **16.2 GB to ~100 KB**.

## File structure

Every module file follows this pattern:

```lean
module
/-
  # Module Title
  Description...
-/

public import AKS.Foo
public import AKS.Bar

@[expose] public section

-- All definitions, theorems, lemmas go here

end
```

### Key elements

**`module`** must be the very first line, before doc comments and imports.

**`public import`** re-exports the imported module's public declarations. In module files, plain `import` is private (imported names are not visible to consumers). Use `public import` for all imports that downstream files need transitively.

**`@[expose] public section ... end`** makes all enclosed declarations both visible (public) and unfoldable (body available for reduction). This is equivalent to non-module behavior. Without `@[expose]`, `public def` exports the name and type but not the body.

**`meta import`** makes an imported module's declarations available in the meta phase (elaborators, tactics, `#eval`). Used in exactly one file: `Random/Bridge/Read.lean` imports `Random.Cert.ReadFFI` this way so the `ascii_file%` elaborator can call `mmapReadAscii`.

## Migration inventory

- **55 of 58 `.lean` files** use `module` (95%)
- **3 non-module files:**
  - `AKS.lean` — root import aggregator (plain `import` for all modules)
  - `AKS/Seiferas.lean` — hosts `#guard_msgs in #print axioms` (forbidden in module files)
  - `lakefile.lean` — Lake configuration, not a library module

The migration was done by `scripts/migrate-to-module.py` for bulk files, with manual per-def annotations for data files.

## Per-def annotations (data files)

Data-carrying modules like `Random/Concrete/Random65536.lean` use selective visibility instead of `@[expose] public section`:

```lean
module
public import Random.Bridge.Bridge
public import Random.Bridge.Read

namespace Random65536

-- Private: body not in .olean, not accessible to importers
def rotData : String := cachedString "data/65536/rot_map.b85"
theorem involution_check : ... := by native_decide

-- Public: name, type, and body visible to importers
public def graph : RegularGraph 65536 16 where ...
public theorem gap : spectralGap graph ≤ 46 / (5 * 16) := by ...

end Random65536
```

Only `graph` and `gap` are exported. The raw certificate data (`rotData`, `certData`) and intermediate theorems (`involution_check`, `certificate_passes`) stay private.

## Avoiding large `.ir` files with `cachedString`

The `.ir` file contains intermediate representation for code generation. Even with `module`, `def rotData := ascii_file% "big_file"` embeds the file contents as a string literal in the IR. For 65536-vertex certificates, this produced an 8.1 GB `.ir` file that downstream builds couldn't read.

**Solution:** `cachedString` is a pure `@[extern]` function that lazily loads files via mmap at native evaluation time:

```lean
-- IR stores just: cachedString "data/65536/rot_map.b85"  (tiny!)
def rotData : String := cachedString "data/65536/rot_map.b85"
```

The C implementation (`Random/Cert/mmap_string.c`) caches loaded strings by path. On first access, it calls `aks_mmap_read_ascii` to load, validate, and mmap the file. Subsequent accesses return the cached result. This keeps `.ir` files at ~8 KB regardless of data size.

`native_decide` works because it compiles to native code that calls the extern function directly, loading the data from disk at evaluation time.

## Lean-generated symbol aliases (`lp_` prefix)

In module mode, `native_decide` and `meta import` look for symbols with Lean-generated names (`lp_<package>_<functionName>`), not the `@[extern]` name. For each `@[extern]` function, `Random/Cert/mmap_string.c` exports aliases:

```c
// @[extern "aks_mmap_read_ascii"] → lp_aks_mmapReadAscii
LEAN_EXPORT lean_obj_res lp_aks_mmapReadAscii(b_lean_obj_arg path, lean_obj_arg w) {
    return aks_mmap_read_ascii(path, w);
}
// Boxed variant for reference-counted arguments
LEAN_EXPORT lean_obj_res lp_aks_mmapReadAscii___boxed(lean_obj_arg path, lean_obj_arg w) {
    lean_obj_res r = aks_mmap_read_ascii(path, w);
    lean_dec_ref(path);
    return r;
}
```

Without these aliases, `native_decide` fails with "Could not find native implementation of external declaration."

## Proof breakages from module migration

The module system changes definitional equality and visibility, causing some proofs to break:

### `rfl` failures on `Nat.fold`

In module mode, `Nat.fold`'s body is not imported from Mathlib (it's in a module file). Proofs using `rfl` for `Nat.fold 0 ... = ...` must use `rw [Nat.fold_zero]` or `simp [Nat.fold_zero]` instead.

### `private` inside `@[expose] public section`

Declarations marked `private` inside a public section become inaccessible to other public declarations in the same section. Fix: remove `private` (the module system handles visibility at the file level).

### `show` / definitional equality failures

Some tactics that relied on definitional unfolding of imported definitions may fail because module mode doesn't import def bodies by default. Fix: use `rw`/`simp` with explicit lemma names instead of relying on definitional reduction.

## `#guard_msgs` and axiom checks

`#print axioms` is forbidden inside module files. Move axiom checks to non-module files:

- `AKS/Seiferas.lean` (non-module) checks AKS proof axioms
- `Random/Concrete/Axioms.lean` (non-module) checks Random data modules

```lean
-- In a non-module file:
import Random.Concrete.Random65536

/-- info: 'Random65536.gap' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound] -/
#guard_msgs in #print axioms Random65536.gap
```

## ReadFFI / Read split pattern

`@[extern]` functions used in elaborators require a split:

1. **`Random/Cert/ReadFFI.lean`** (module, in `Random.Cert` lean_lib) — contains `@[extern]` declarations (`mmapReadAscii`, `mmapPrepare`, `cachedString`). Part of the precompiled `Random.Cert` lib, so `lp_` symbols are auto-generated in the shared library.
2. **`Random/Bridge/Read.lean`** (module) — does `meta import Random.Cert.ReadFFI` to access `mmapReadAscii` in the meta phase, defines the `ascii_file%` elaborator and `ensureCertificateData`

The split is necessary because elaborators in module files are implicitly `meta` and cannot call non-meta `@[extern]` functions directly. `meta import` bridges this gap.

## Build artifact sizes (Random65536)

| Artifact | Before modules | With `module` + `ascii_file%` | With `module` + `cachedString` |
|---|---|---|---|
| `.olean` | 8.1 GB | 48 KB | 48 KB |
| `.olean.private` | (N/A) | 8.1 GB | 44 KB |
| `.ir` | 8.1 GB | 8.1 GB | 8 KB |
| Build time | ~720s (OOM risk) | ~720s | ~123s |

## Constraints

- Within the same package, a module file can only import other module files.
- Non-module files can import module files freely.
- `initialize` actions in module files work normally (compiled to native code, run at module load time).
- `#eval` works in module files but is implicitly meta.
