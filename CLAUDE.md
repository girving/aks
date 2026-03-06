# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Lean formalization of the Ajtai–Komlós–Szemerédi (1983) O(n log n) sorting network construction. The project formalizes the proof architecture using the zig-zag product (Reingold–Vadhan–Wigderson 2002) as the route to explicit expander families, avoiding the heavy algebraic machinery (Margulis/LPS) that would require years of formalization effort.

Most theorems have `sorry` placeholders — this is intentional. The codebase is a structural skeleton demonstrating the complete proof architecture.

### Primary Sources

The key papers are checked into the repo:
- **`docs/aks.pdf`** — Ajtai, Komlós, Szemerédi (1983): the sorting network construction
- **`docs/rvw.pdf`** — Reingold, Vadhan, Wigderson (2002): the zig-zag product and spectral analysis
- **`docs/paterson.pdf`** — Paterson (1990): simplified AKS with (λ,ε)-separators, depth < 6100 log n
- **`docs/seiferas.pdf`** — Seiferas (2009): further simplified, single potential function, depth ≤ ~49 log n

**Always consult these PDFs first** when checking theorem statements, proof strategies, or definitions. Read the relevant section of the paper before doing web searches — the papers are the ground truth and web sources frequently get details wrong.

### Correctness Path: Seiferas (2009) Separator-Based

The correctness proof uses the **Paterson/Seiferas separator-based** approach (`AKS/Separator/`, `AKS/Bags/`): replaces ε-nearsorts with (γ,ε)-separators + outsider counting with Seiferas's single potential function. See `docs/bags.md` for the full design.

The original AKS ε-nearsort + tree-distance wrongness path (`Nearsort/`, `Tree/`) has been removed — the separator path has cleaner abstractions (outsider counting vs. tree-distance wrongness).

## Build Commands

Use the **MCP tools** for checking Lean code:

- **`mcp__lean__check`** — Check a `.lean` file via the persistent `lake serve` LSP. Fast incremental checking (~0.2-2s for warm edits). The MCP server (`.claude/mcp/lean.rs`) auto-starts `lake serve` and keeps it warm.
- **`mcp__lean__snippet`** — Run ad-hoc Lean snippets (`#check`, `#eval`, proof experiments) via `lake env lean --stdin`.

```bash
scripts/sorries                             # Audit sorry, #exit, native_decide, axiom across codebase
scripts/sorry-gate                          # Enforce sorry-free guarantees on protected files
```

**`sorry-gate`** blocks `sorry`, `#exit`, `native_decide`, and `axiom` across all of `AKS/` with no exceptions. `noncomputable` is allowed per-subdir (see `ALLOW_MARKER` in the script) but banned in `AKS/Seiferas.lean`. The `Random/` library bans `sorry`, `#exit`, and `axiom` (but allows `native_decide`). The pre-commit hook runs `sorry-gate` automatically.

**Always use `mcp__lean__check` for verifying changes.** It keeps Mathlib imports in memory via `lake serve` and re-elaborates from the change point forward. Most checks are sub-second after cold start. The MCP server detects file layout changes and automatically restarts `lake serve`. Use `close_after: true` to free LSP memory for files you won't re-check.

No tests or linters — correctness is verified through Lean's type checker.

### `lake build` (fallback only)

Use `lake build` only as a fallback when the MCP server has issues. For individual files, `mcp__lean__check` is much faster.

```bash
lake exe cache get    # Download prebuilt Mathlib oleans (run after lake clean or fresh clone)
lake build            # Build default target (AKS library only) — slow, use only as fallback
lake build AKS Random # Build all libraries including Random (certificates, benchmarks, etc.)
lake clean            # Clean build artifacts
```

**After `lake clean` or a fresh clone, run `lake exe cache get` before `lake build`.** The Mathlib cache avoids recompiling Mathlib from source (~30+ min → ~1 min). Lake automatically builds the Random shared library (`libaks_Random.so`) and passes `--load-dynlib` to modules that import it, thanks to `precompileModules := true` on the `Random` lean_lib.

### Temporary Files

Write temporary files (scratch scripts, test data, etc.) to `tmp/` within the repo (`~/aks/tmp/`), not `/tmp/`. The sandbox allows writes to the repo directory but not to `/tmp/`. The `tmp/` directory is in `.gitignore`.

### Python Scripts

Use `uv run` (not `pip install`) for Python scripts with dependencies:
```bash
uv run --with numpy --with networkx scripts/some_script.py
```

### Mathlib Searches

`rg` (ripgrep) through `.lake/packages/mathlib/Mathlib/` takes ~0.2s for any pattern. This is already fast. Example:
```bash
rg 'IsSelfAdjoint.norm_mul_self' .lake/packages/mathlib/Mathlib/
```

### Tool Speed Expectations

Track tool performance against these baselines. If a command exceeds its expected time by 2x+, investigate and record in `scripts/SLOW_COMMANDS.md`.

| Operation | Expected time | If slower, check |
|---|---|---|
| `rg` through Mathlib | ~0.2s | Disk I/O, cold cache |
| `mcp__lean__check` (warm) | 0.2-2s | MCP server issue? `/mcp` to reconnect |
| `mcp__lean__check` (cold, first file) | 2-5s | Normal — lake serve loading imports |
| `lake build` (all cached) | ~1.6s | Nothing changed? |
| `lake build` (one file changed) | ~20s | Normal; use `mcp__lean__check` instead |
| `git` operations | <1s | Large repo / network |

**Timeout protocol:** When any tool call times out, record it in `scripts/SLOW_COMMANDS.md` with context (what file, what operation, wall time). Then investigate root cause.

### Git

Use merge, not rebase: `git pull --no-rebase`.

**When the user says "commit", always push immediately after committing.** The standard workflow is: commit → pull if needed → push.

**Show a diffstat before committing.** Run `git diff --stat` (for staged+unstaged changes) so the user can see which files changed and how many lines were added/removed before the commit is created.

### URL Fetching

**When asked to fetch a URL that returns an error (403, timeout, etc.), ask the user for help** rather than silently falling back to searching local files or other sources. The user shared that URL for a reason — the content matters, and local files may contain outdated or different information.

### Resource Constraints

**Never increase numerical precision or memory usage without explicit permission.** OOM crashes waste more time than a tight margin. If you believe higher precision is truly needed, **ask first** — explain the tradeoff and let the user decide.

**Check for zombie processes on startup/resume.** Long-running Rust or Lean processes from previous sessions can linger and consume GB of memory. On session start: `ps aux | grep -E 'certificate|lake|lean' | grep -v grep` and kill stale ones with `pkill -f lean` / `pkill -f lake` before launching new heavy jobs.


### Proof Visualization (`docs/index.html`)

Interactive dependency graph served via GitHub Pages from `docs/`. To refresh: update `PROOF_DATA` JSON in `docs/index.html` with theorem names, statuses, and line numbers. Colors: green=proved, orange=sorry, red=axiom, blue=definition. Milestone theorems are larger with white border.

**Update the visualization every time you prove something.** When a `sorry` is resolved, change its status in `PROOF_DATA` from `"sorry"` to `"proved"` and update its description. Then run `scripts/update-viz-lines` to sync line numbers. Do this proactively — don't wait for the user to ask.

**Line number maintenance:** `scripts/update-viz-lines` auto-syncs line numbers from source files. Run it after any code changes. Use `--check` mode to verify without modifying. The script greps each node's source file for its declaration keyword and updates the `line:` field in `PROOF_DATA`.

**Visualization invariant:** If all nodes in a file are green, the file must have no `sorry`s. Private lemmas with `sorry`s must be included as nodes unless they fall under a larger `sorry` theorem.

## Architecture

**Entry point:** `AKS.lean` — imports all modules. Top-level theorem: `seiferas_sorting_networks_exist_pow2` in `AKS/Seiferas.lean`.

**Detailed subsystem docs** — per-section files with architecture, conventions, and proof tactics:
- [`docs/certificate-bridge.md`](docs/certificate-bridge.md) — Certificate bridge (`Random/Cert/`, `Random/Bridge/`, `Random/Concrete/`)
- [`docs/rvw-inequality.md`](docs/rvw-inequality.md) — RVW scalar inequality and operator bound (`AKS/ZigZag/RVWInequality.lean`, `RVWBound.lean`)
- [`docs/zigzag-spectral.md`](docs/zigzag-spectral.md) — Zig-zag product spectral analysis (`AKS/ZigZag/Operators.lean`, `Spectral.lean`, `Expanders.lean`)
- [`docs/halver-expander.md`](docs/halver-expander.md) — Halver/expander infrastructure (`AKS/Graph/`, `AKS/Halver/`)

**Modules with bottom-up dependency:**

### `AKS/Misc/Fin.lean` — `Fin` Arithmetic Helpers
Reusable encode/decode lemmas for `Fin n × Fin d` ↔ `Fin (n * d)` product indexing: `Fin.pair_lt`, `fin_encode_fst`, `fin_encode_snd`, `fin_div_add_mod`.

### `AKS/Graph/` — Core Regular Graph Theory, Squaring, Complete Graph
`RegularGraph`, `spectralGap`, graph squaring, complete graph. See [`docs/halver-expander.md`](docs/halver-expander.md).

### `AKS/MGG/` — Margulis-Gabber-Galil Expander
Direct 8-regular expander on `(Z/nZ)²` for any `n`. `mgg n : RegularGraph (n * n) 8` with fully proved involution. Spectral gap bound `≤ 5√2/8` (sorry'd). Alternative to the zig-zag product construction — simpler, better constants, no base expander certificate needed. See [`docs/mgg.md`](docs/mgg.md).

### `AKS/Halver/` — ε-Halver Theory, Tanner's Bound, Expander → Halver Bridge
`IsEpsilonHalver`, `tanner_bound`, `expander_gives_halver` (fully proved), expander mixing lemma. `halvers` builds a concrete `HalverFamily ε` using the MGG expander (8-regular, no `native_decide`). See [`docs/halver-expander.md`](docs/halver-expander.md).

### `Random/` — Base Expander Certificates and Benchmarks
Concrete base expanders certified via davidad's triangular-inverse method (uses `native_decide`). Also contains benchmarks, tests, and profiles for the certificate checker. See [`docs/certificate-bridge.md`](docs/certificate-bridge.md).

### `AKS/ZigZag/Operators.lean`, `Spectral.lean` — Zig-Zag Product and Spectral Properties
Zig-zag product, walk operators (B, Σ, Q), algebraic identities, spectral bounds. See [`docs/zigzag-spectral.md`](docs/zigzag-spectral.md).

### `AKS/ZigZag/RVWInequality.lean`, `RVWBound.lean` — RVW Inequality and Operator Bound
Fully proved. See [`docs/rvw-inequality.md`](docs/rvw-inequality.md).

### `AKS/Cert/` — Certificate Bridge Infrastructure
Walk bound theory, bridge proofs, and imperative checker equivalences. See [`docs/certificate-bridge.md`](docs/certificate-bridge.md).

### `Random/Misc/ForLoop.lean` — For-Loop Characterization (~105 lines)
Proves `for k in [:n] do` in `Id` monad equals `Nat.fold` + partition-fold lemmas.

### `Random/Cert/mmap_string.c` — mmap-based ASCII File Reader (FFI)
C implementation of `mmapReadAscii`. Reads a file into a Lean `String` via `memfd` + split mmap, validating all bytes < 128 in a single streaming pass. Compiled via `extern_lib «mmap»` in `lakefile.lean`. See the `@[extern]` exception note in Key Lean/Mathlib Conventions.

### `AKS/ZigZag/Expanders.lean` — Expander Families
`zigzag_spectral_bound`, `zigzagFamily`, `zigzagLevel` (computable minimum-level search), `contractedExpander`. See [`docs/zigzag-spectral.md`](docs/zigzag-spectral.md).

### `AKS/Separator/` — (γ, ε)-Separator Infrastructure
ε-approximate γ-separation (Seiferas 2009, Section 6).
1. **`Defs.lean`** — `SepInitial`, `SepFinal`, `IsApproxSep`, `IsSeparator`
2. **`Family.lean`** — `SeparatorFamily` structure (computable, no `γ ε : ℝ` params; separation property via `IsSepFamily` predicate)
3. **`FromHalver.lean`** — `halverToSeparator` computable construction, `halver_isSeparator_half` (proved), inductive separator correctness
For γ = 1/2 this reduces to `IsEpsilonHalver`. Uses Seiferas's two-parameter
(γ, ε) formulation, not Paterson's three-parameter (λ, ε, ε₀).
See `docs/separator-plan.md` for full design.

### `AKS/Bags/` — Bag-Tree Sorting
Seiferas's bag-based tree argument: separators → O(log n) depth sorting network.
All definitions validated by Rust simulation (`rust/test-bags.rs`).
1. **`Defs.lean`** — `Bag k`, `Placement k`, `Bag.Native`, `Bag.Strange`, `Bag.strangers`. Typed bag API with `hx : x < 2 ^ l` constraint.
2. **`Network.lean`** — `Params`, `BagSplit`, `split`, `separate`, `stage`, `stages`, `stageRegs`, `capacity`, `fringe`. Computable stage iteration via `Build` monad.
3. **`Sizes.lean`** — `bagCard` recurrence, `bagCard_eq_card` (sizes match recurrence), `bagCard_le_capacity`, `bagCard_root_even`.
4. **`Strange.lean`** — `stranger_bound` (main theorem: j-strangers ≤ γ·ε^(j-1)·cap). Proved by induction on stage number. Sorry'd: `parent_stranger_j2_le`, `parent_stranger_eq1_le` (separator-quality bridge).

### Data flow
```
Misc/Fin.lean → Graph/Regular.lean → Graph/Square.lean ─────→ ZigZag/Expanders.lean
                               → MGG/Defs.lean → MGG/Spectral.lean
                               → Graph/Complete.lean           ↓
                              → Halver/Mixing.lean ─→ Halver/Tanner.lean    Seiferas.lean
                              → Cert/WalkBound.lean ──→ Cert/Bridge.lean       ↑
                              → ZigZag/Operators.lean ──→                      ↑
                                  ZigZag/Spectral.lean ─↗ Sort/*.lean          ↑
           Random/*.lean ──────────────────────────↗          ↑                ↑
           ZigZag/RVWInequality.lean ─→ ZigZag/RVWBound.lean ─↗               ↑
           Random/Cert ────→ Cert/Defs.lean ──→ Cert/Bridge.lean               ↑
           Graph/Contract.lean ─────────────────────────────────────────→ Seiferas.lean
                                                                               ↑
           Halver/*.lean ──→ Halver/FromExpander.lean ─→ Separator/FromHalver.lean
                                                                    ↓
                                                         Separator/Defs.lean
                                                         Separator/Family.lean
                                                                    ↓
                                                         Bags/Defs.lean
                                                         Bags/Network.lean
                                                         Bags/Sizes.lean
                                                         Bags/Strange.lean ──→ Seiferas.lean
```

## Style

- **Remove unused hypotheses from proved theorems.** Don't prefix with `_` — delete the argument entirely and update all callers.
- Use `↦` (not `=>`) for lambda arrows: `fun x ↦ ...`
- In markdown/comments, backtick-quote Lean identifiers and filenames: `` `Fin` ``, not `Fin`; `` `ZigZag.lean` ``, not `ZigZag.lean`
- Use `/-! **Title** -/` for section headers, not numbered `§N.` or decorative `-- ═══` lines
- Move reusable helpers into their own files (e.g., `Fin` arithmetic → `AKS/Misc/Fin.lean`). Iterate in-file during development, extract before committing.
- Split files beyond ~300 lines for faster incremental checking. See [`docs/shrink.md`](docs/shrink.md) for systematic techniques to reduce lines, build time, and `.olean` size.
- **Use subdirectories for cohesive subsystems.** Group related files under `AKS/Name/*.lean`. Consumers import leaf modules directly. When moving files into a subdirectory: (1) `git mv` the files, (2) update imports in moved files and all dependents, (3) update `file:` paths in `docs/index.html` PROOF_DATA, (4) update CLAUDE.md architecture section, (5) run `scripts/update-viz-lines`.
- Prefer algebraic notation over explicit constructor names: `1` not `ContinuousLinearMap.id ℝ _`, `a * b` not `ContinuousLinearMap.comp a b`. Don't add type ascriptions when the other operand pins the type.
- **Parameterize theorems over abstract bounds, not hard-coded constants.** Take spectral gap bounds (β, c, etc.) as parameters with hypotheses, not baked-in fractions. Chain `.trans` through hypotheses, not `norm_num`. Prefer explicit types/degrees (`D * D`) over `∃ d`, and concrete objects as parameters over axioms in statements. Motivation: we want explicit, computable, extractable constants.
- **Parameterize families by a size function, not a validity predicate.** When a family (halvers, separators, etc.) only exists at certain sizes, make the type reflect that: parameterize by `size : ℕ → ℕ` and index the family by `k : ℕ`, so `net k` operates on `size k` wires. Don't define `net` for all `m : ℕ` with a `valid : ℕ → Prop` predicate — that creates junk values at invalid sizes and forces every caller to thread validity proofs. The family's type should make ill-formed indices unrepresentable.
- **Define constructions as computable `def`s, prove properties as separate theorems.** Never use `∃ (net : ComparatorNetwork n), ...` when the witness is known — define it as a `def` and prove properties about it. This gives: (1) computability, (2) composability (downstream code can refer to the object directly), (3) cleaner proofs (no `Exists.choose`/`noncomputable`). Example: `expanderHalver` is a `def` with `expanderHalver_isEpsilonHalver` and `expanderHalver_size` as theorems — not `∃ net, IsEpsilonHalver net β ∧ net.size ≤ m * d`. Similarly, bundle families as `structure`s with computable fields + proof fields (see `HalverFamily`).
- **Keep sorting network definitions computable.** Only use `noncomputable def` for functions that inherently require classical choice — those returning `ℝ`, CLMs, spectral gaps, or using `Exists.choose`. The entire data pipeline (`mgg` → `iterSquare` → `konigQuotientHalver` → `halvers` → `halverToSeparatorFamily'` → `separatorSortingNetwork`) is computable. Noncomputability is confined to Prop-valued fields (spectral gap bounds, ℝ inequalities) which are erased at compile time.
- **Use `ℚ` for type parameters of computable families; cast to `ℝ` internally in proof fields.** When a structure bundles computable data (networks, depths) with proof fields (separator/halver properties over `ℝ`), parameterize the structure by `ε : ℚ` and cast `↑ε` inside the proof fields — not `ε : ℝ` with casts at every construction site. This keeps the structure computable (`ℚ` is decidable), avoids `↑ε` clutter in signatures, and confines casts to proof fields that are erased at compile time. Example: `HalverFamily (ε : ℚ)` with `isHalver : ∀ m, IsEpsilonHalver (net m) ↑ε`, not `HalverFamily (ε : ℝ)` forcing callers to write `HalverFamily ↑ε`.
- **Prove depth bounds, not size bounds.** For comparator networks, depth (parallel rounds) is the fundamental complexity measure. Size ≤ n/2 · depth follows trivially from `size_le_half_n_mul_depth`. Always state the depth bound first; derive size as a corollary. This applies to `HalverFamily` (already correct: `depth_le` is fundamental, `size_le` derived), separator families, and the top-level sorting network theorem.
- **Avoid non-terminal `simp`** — use `simp only [specific, lemmas]` or `rw` instead. Non-terminal `simp` is fragile (new simp lemmas can break downstream tactics). Exception: acceptable if the alternative is much uglier, but document why.
- **Don't create import-only re-export files.** A file that just imports its children (e.g., `AKS/Sort.lean` importing `Sort.Defs`, `Sort.Monotone`, etc.) adds indirection with no value. Import leaf modules directly from the root `AKS.lean` or from consuming files.
- **Colocate files with their consumers, not their topic.** If a file has only one downstream user, move it into that subsystem's directory. E.g., `Mixing.lean` was used only by `Halver/Tanner.lean`, so it belongs in `AKS/Halver/`, not at the top level.
- **Cite proof sources.** When a proof idea, construction, or argument comes from a specific paper or exposition, cite it in both the `docs/` plan file and the Lean source (module docstring or theorem docstring). Use the format "Author (Year)" or "Author, *Title* (Year)" and include a URL or `docs/*.pdf` reference when available. This applies to proof strategies (e.g., "following Lee (2014), arXiv:1301.6296"), not just theorem statements. If you adapt an argument rather than follow it exactly, say so: "adapted from Author (Year)."

## Key Lean/Mathlib Conventions

- `autoImplicit` is **disabled** globally in `lakefile.lean` — do not add `set_option autoImplicit false` in individual files
- Depends on **Mathlib v4.27.0** — when updating, check import paths as they frequently change between versions (this has caused build breaks before)
- Lean toolchain: **v4.27.0** (pinned in `lean-toolchain`)
- **Avoid `native_decide`** — sidesteps the kernel's trust boundary. Prefer `decide +kernel` when `decide` is too slow. Only use `native_decide` as a last resort.
- **NEVER use `@[implemented_by]`, `@[extern]`, or `unsafePerformIO`** — these can make the kernel and native evaluator disagree, allowing proofs of `False`. **Exception:** The mmap-based file reader in `Random/Cert/ReadFFI.lean` uses `@[extern]` for three functions: `mmapReadAscii` (IO file reader), `mmapPrepare` (IO + thunk), and `cachedString` (pure lazy loader). C implementation in `Random/Cert/mmap_string.c`. These are intentional trust extensions — see [`docs/trust.md`](docs/trust.md) for the full trust analysis. `cachedString` is used for large certificate data (`Random65536.lean`) to avoid embedding multi-GB strings in build artifacts. Smaller data files in `Random/` use `ascii_file%` which embeds data as kernel-visible string literals.
- **Split string literals >1 MB across multiple files.** The Lean parser/elaborator chokes on string literals around ~2 MB (>600s timeout). At ~1 MB they compile in ~1.3s. For large inline data, split into ≤800 KB chunks in separate files (e.g., `Random/Rot38416{a,b,c}.lean`), import them, and concatenate with `++`. The `++` is not kernel-evaluated when the operands are opaque `def`s — only the native evaluator resolves it. See `Random/Random38416.lean` for the pattern.
- **Guard axiom sets with `#guard_msgs in #print axioms`.** For theorems that must not depend on `sorry` (or must use only specific axioms like `native_decide`), add a `#guard_msgs` check after the namespace close. This is a compile-time assertion that fails if the axiom set changes. Pattern:
  ```lean
  end MyNamespace
  /-- info: 'MyNamespace.myTheorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
  #guard_msgs in #print axioms MyNamespace.myTheorem
  ```
  See `Random/Random*.lean` for examples. Use this whenever a file graduates to sorry-free status.
  **Note:** `#print axioms` is forbidden inside `module` files — place checks in non-module files (`AKS/Seiferas.lean`, `Random/Axioms.lean`).

### Module system

All files use Lean's `module` system. See [`docs/modules.md`](docs/modules.md) for full documentation. Key rules:

- **`module`** is the first line of every `.lean` file (except `AKS.lean`, `AKS/Seiferas.lean`, `lakefile.lean`).
- **`public import`** for all imports (plain `import` is private in module files).
- **`@[expose] public section ... end`** wraps all declarations in standard files.
- **`cachedString "path"`** for large certificate data (keeps `.ir` files small). `ascii_file%` for small data.
- **`meta import`** only in `AKS/Cert/Read.lean` (for elaborator access to FFI).
- **Per-def `public`** annotations in data files (`Random/Random65536.lean`, `Random/Random*.lean`).
- **`@[extern]` FFI declarations live in `Random/Cert/ReadFFI.lean`** (part of the `Random` lean_lib with `precompileModules := true`), so `lp_` symbols are auto-generated in `libaks_Random.so`. No manual C aliases needed.
- **`rfl` may fail** on `Nat.fold 0` in module mode — use `rw [Nat.fold_zero]`.
- **Remove `private`** from declarations inside `@[expose] public section` — module-level visibility suffices.

## Proof Workflow

**Skeleton correctness takes priority over filling in sorries.** A sorry with a correct statement is valuable (it documents what remains to prove); a sorry with a wrong statement is actively harmful (it creates false confidence and wasted work downstream). When auditing reveals incorrect lemma statements, fix them before working on other tractable sorries — even in other files. An honest skeleton with more sorries beats a dishonest one with fewer.

**Verify theorem statements against the source paper early.** Before building infrastructure, read the primary source to confirm: (1) single application or repeated/recursive? (2) essential tree structures or bookkeeping? (3) definitions match exactly? Informal sources can mislead about the precise result. Read primary sources at the design stage.

**Formalization adds lemmas for implicit hypotheses.** When an informal proof says "X follows because the construction has property P," the formal proof needs an explicit predicate for P and a lemma proving the construction satisfies it. Having more intermediate lemmas than the paper is EXPECTED — the extra lemmas make implicit paper assumptions explicit. Don't conflate "fewer lemmas" with "closer to the paper"; the paper's argument structure matters more than its lemma count. E.g., the AKS paper's Lemma 3 implicitly assumes zig operates on even-level cherries; the formalization needs `HasImprovedBound` as an explicit predicate + `parity_nearsort_has_improved_bound` proving the construction satisfies it.

Before attempting a `sorry`, estimate the probability of proving it directly (e.g., 30%, 50%, 80%) and report this. If the probability is below ~50%, first factor the `sorry` into intermediate lemmas — smaller steps that are each individually likely to succeed. This avoids wasting long build-test cycles on proofs that need restructuring.

**Recognize thrashing and ask the user.** After 3+ failed approaches to the same goal, stop and ask for guidance. Signs: repeated restructuring, oscillating between approaches, growing helper count without progress. A 2-minute conversation is cheaper than 30 minutes of failed builds.

**Never silently abandon an agreed plan.** If a plan was approved and a step turns out harder than expected, do NOT silently switch to a shortcut (e.g., replacing a proof with `native_decide` or `sorry`). Always confirm radical plan changes with the user first — explain what's hard, what the alternatives are, and let them decide. A 2-minute conversation about changing course is far cheaper than discovering the change broke assumptions downstream.

**Never weaken the top-level asymptotic bounds.** The project goal is O(log n)-depth, O(n log n)-size sorting networks. If a definition or proof approach would change the top-level theorem to claim a weaker bound (e.g., O(n log² n)), STOP and ask the user before proceeding. Fix the definition to match the paper's construction rather than weakening the theorem to match a wrong definition. This applies to any change that cascades to `seiferas_sorting_networks_exist_pow2`.

**Assess proof risk before significant work.** Break non-trivial theorems into phases with risk levels: LOW (definition, direct proof), MEDIUM (standard argument, uncertain details), HIGH (novel connection, unclear if approach works). Identify the highest-risk phase, document fallback plans (axiomatize, defer, reformulate), and validate the critical bottleneck lemma before building dependencies. Escalate to user after 2-3 failed attempts on a MEDIUM+ phase.

**Analyze uncertain lemmas in natural language before formal proof attempts.** Work through the math with concrete examples BEFORE formalizing: (1) test the proof idea with specific numbers, (2) look for counterexamples, (3) verify each step informally, (4) only then formalize. Informal analysis is instant vs. 20s-2min build cycles. A careful analysis can reveal a lemma is unprovable (saving days) or clarify the exact proof structure needed.

**Test sorry'd theorem statements empirically with optimized Rust.** Before investing weeks proving a lemma, write a Rust program (`rust/test-*.rs`, run via `cargo +nightly -Zscript`) that implements the Lean construction and checks the property across many random inputs and parameter ranges. Key techniques: (1) mirror the Lean `def`s exactly in Rust (comparator networks, graph operations, recursive constructions), (2) build *families* of test inputs at every size the construction needs — e.g., random d-regular bipartite graphs as synthetic halvers, not just one concrete graph, (3) measure empirical bounds (ε, depth) across sub-sizes with a safety margin, (4) test the claimed bound at multiple parameter values (γ', t, etc.). This catches wrong theorem statements early — a false lemma will show violations immediately, while a true one will pass thousands of trials. The cost is a few hundred lines of Rust vs. weeks of wasted proof effort on a wrong statement.

**Build clean APIs before writing complex proofs.** When a proof involves repeated manipulation of the same concepts (bag indices, native intervals, stranger counts), invest in a typed API first: structures that bundle related data (`Bag k` instead of bare `level idx : ℕ`), derived operations (`lo`, `hi`, `parent`, `ancestor`), and characterization lemmas (`native_iff`, `Native.parent`). The upfront cost is small (each def/lemma is trivial), but downstream proofs become dramatically shorter and more readable — parameters that were threaded everywhere become fields, ad-hoc arithmetic becomes named lemmas, and wrong-argument bugs become type errors. Example: the old `isJStranger k rank level idx j` with five bare `ℕ` args became `b.Strange j r perm` after introducing `Bag k`; interval reasoning via `nativeBagIdx` division became `b.lo ≤ rank ∧ rank < b.hi` via `native_iff`.

**Keep proofs small and factored.** If a proof has more than ~3 intermediate `have` steps, factor them into standalone lemmas. Each lemma should have a small, independently testable interface — this avoids churning where fixing one step breaks steps below it.

**Prefer point-free (abstract) formulations over coordinate-based ones.** Before diving into a coordinate proof, ask whether an operator identity makes the key result fall out algebraically. Abstract identities compose cleanly; coordinate proofs each require their own index bookkeeping. **Exception:** when there's a canonical basis and the proof is naturally a finite computation (e.g., `adjMatrix_row_sum`).

**When a user suggests an approach or lesson, rephrase it for CLAUDE.md** rather than copying verbatim. Lessons should be concise, actionable, and fit the existing style.

**Work autonomously on low-risk tasks once the path is clear.** When reduced to well-understood engineering (Mathlib interfacing, type bridging, assembling existing components), continue autonomously. Check in when hitting unexpected obstacles, discovering the approach won't work, or completing major milestones. Progress over permission when risk is low.

**Review subtle definitions interactively before building downstream infrastructure.** Definitions that involve distinguishability (e.g., 0-1 values vs labeled elements) or quantifier structure (∀ permutations vs ∀ Boolean sequences) can be subtly wrong in ways that only surface when attempting proofs. When a definition is the foundation for multiple sorry'd lemmas, validate it with the user before committing to downstream work.

**"Easy to see" in papers is a red flag for formalization.** When a paper says "it is easy to see" without proof, validate the *proof strategy* — not just the statement — before investing in Lean infrastructure. The AKS paper's `error_set_bound` ("it is easy to see that |E_l| ≤ ε·k") passes empirical testing with 0 violations, but the natural per-chunk EIH/EFH decomposition is provably insufficient due to overflow (`f_c + t_c > hs` in some chunks). The statement is true; the proof requires a global argument the paper doesn't sketch. Always ask: "what is the proof, not just the claim?"

**Add diagnostic modes to Rust empirical tests.** Pass/fail testing catches wrong statements but not proof obstacles. When a theorem passes empirically but the proof is hard, add diagnostics that measure intermediate quantities in the proof strategy. E.g., for `error_set_bound`: testing `|E_l| ≤ ε·k` found 0 violations, but measuring `f_c + t_c` per chunk revealed overflow in ~111K chunks (max surplus 17) — explaining exactly why the per-chunk decomposition fails. Diagnosis: 10 lines of Rust, saves days of failed proof attempts.

**When local decomposition fails, compare alternative formalizations.** Bounding a global sum `Σ_c bound_c ≤ B` by per-unit bounds requires each unit's bound to be tight. When some units overflow (local bound exceeds budget), the slack from other units can't compensate without a cross-unit argument. Recognize this early by checking whether the per-unit bound holds universally. Reading alternative constructions (e.g., Seiferas's nested-prefix halvers vs. AKS's all-chunks halvers) can reveal that the difficulty is inherent to the construction, not the proof technique — suggesting a different formalization path may avoid the obstacle entirely.

## Proof Tactics

After completing each proof, reflect on what worked and what didn't. If there's a reusable lesson — a tactic pattern, a Mathlib gotcha, a refactoring that unlocked progress — add it here (not in auto memory). This file is the single source of truth for accumulated lessons, so they persist across machines.

**Extract defs from `where` blocks before proving properties.** Inline `where` blocks produce goals with fully-unfolded terms. Instead: extract as a standalone `private def` using `.1`/`.2` projections, prove properties as separate theorems, plug both into the `where` block. Then `simp only [my_def, ...]` works cleanly. See `square_rot`/`square_rot_involution` in `Graph/Regular.lean`.

**Generalize helper lemmas from the start.** Write `Fin` arithmetic helpers with the most general signature (e.g., `Fin n × Fin d`, not `Fin d × Fin d`). General versions cost nothing extra and prevent rework.

**`Fin` simp lemmas: quantify over proof terms.** When writing simp lemmas for `Fin` encode/decode, take the `isLt` proof as a parameter `(h : ... < d)` so the lemma matches any proof term Lean generates internally.

**`Fin` arithmetic: `omega` vs. specialized lemmas.** `omega` handles linear Nat but not nonlinear. Key lemmas: `Nat.add_lt_add_left`+`Nat.mul_le_mul_right` for `j*d+i < n*d`; `Nat.add_mul_div_right`/`Nat.add_mul_mod_self_right` for div/mod; `rw [Nat.mul_comm]; exact Nat.div_add_mod` for `(ij/d)*d + ij%d = ij`.

**`Fin.mk.injEq` to convert Fin equalities for omega.** When omega can't see through `Fin` structure projections, use `simp only [Fin.mk.injEq] at heq` to convert `⟨a, _⟩ = ⟨b, _⟩` to `a = b`. This is more reliable than `Fin.ext_iff` + `Fin.val_mk` when the Fin isn't yet in constructor form. Needed after `obtain ⟨x, _, rfl⟩` on `List.mem_map` results.

**Provide nonlinear `Nat.mul` facts to omega explicitly.** When goals involve products of variables (`k₁ * C`, `k₂ * C`), omega treats each product as an opaque atom. Provide key inequalities manually: e.g., `have : k₁ * C + C ≤ k₂ * C := by have := Nat.mul_le_mul_right C hlt; rw [Nat.succ_mul] at this; exact this`. Also provide `Nat.mul_div_le` for `2 * (C / 2) ≤ C`.

**`set` abbreviations create different omega atoms.** After `set C := n / 2 ^ level`, omega treats `↑C` and `↑(n / 2 ^ level)` as independent variables. When `heq` uses the raw expression but `hk` uses the abbreviation, omega can't connect them. Fix: provide auxiliary `have`s using the raw expression, not the `set` abbreviation, or avoid `set` entirely when omega will be the closer.

**Search Mathlib before writing custom helpers.** Existing helpers come with simp lemmas and composability. To search: (1) grep `.lake/packages/mathlib` for keywords, (2) `#check @Fin.someName` in a scratch file, (3) **LeanSearch** (https://leansearch.net/) for semantic queries. Reparameterize types to match Mathlib conventions (e.g., `Fin (n+1)` instead of `Fin d` with `hd : d ≥ 2`). Examples found: `Fin.succAbove`/`Fin.predAbove`, `Monotone.map_min`/`Monotone.map_max`.

**Avoid inline `⟨expr, by omega⟩` inside definitions.** Embedded proof terms create opaque terms that `omega`/`simp` can't see through after unfolding. Instead use Mathlib helpers or named functions with `.val` simp lemmas.

**Prefer `apply` over `exact` when arguments are inferrable.** `apply G.foo` when `v`, `i` are determined by unification. Common after `rw` rewrites.

**Nested if-then-else: manual `by_cases` over `split_ifs`.** `split_ifs` generates fragile hypothesis names. Instead: `by_cases h : condition` then `rw [if_pos h]`/`rw [if_neg h]` for each branch. Use `‹fact›` to reference anonymous `have` statements. Pattern: `by_cases h : a = c.i; · rw [if_pos h]; ...; · rw [if_neg h]; ...`.

**When stuck after 2-3 attempts, step back and reason mathematically** rather than trying more tactic variations on the same structure. (1) Write out what you're proving and why it's true, (2) identify key sublemmas, (3) implement as separate helper lemmas, (4) reassemble.

**Define CLMs in three layers: standalone function → LinearMap → CLM.** (1) Standalone `def` on `Fin n → ℝ` for easy `simp`/`unfold`. (2) Wrap as `→ₗ[ℝ]` using `WithLp.toLp 2`/`WithLp.ofLp`; prove `map_add'`/`map_smul'` via `apply PiLp.ext; intro v; simp [myFun, ...]`. (3) Promote to `→L[ℝ]` via `LinearMap.toContinuousLinearMap`. Add `@[simp]` lemma `myCLM_apply` (typically `rfl`). See `walkFun`/`walkLM`/`walkCLM` in `Graph/Regular.lean`.

**Triangle inequality for `|·|` via `dist_triangle`.** Convert to metric API: `|μ| = ‖μ‖ = dist μ 0` (via `Real.norm_eq_abs`, `dist_zero_right`), then `dist_triangle μ c 0`. Use `Real.dist_eq` for `dist x y = |x - y|`.

**`List` membership API.** `List.not_mem_nil` has ALL arguments implicit: `@List.not_mem_nil : ∀ {α} {a}, a ∉ []` — use `List.not_mem_nil` not `List.not_mem_nil _`. For `a ∈ a :: l`, use `List.mem_cons.mpr (.inl rfl)` (not `List.mem_cons_self a l`). For `b ∈ a :: l` given `hb : b ∈ l`, use `List.mem_cons_of_mem a hb`.

**`↑(Finset.univ)` ≠ `Set.univ` in `MapsTo` proofs.** `card_eq_sum_card_fiberwise` needs `(s : Set ι).MapsTo f ↑t`. The coercion `↑(Finset.univ)` is `Finset.univ.toSet`, not `Set.univ`. Use `Finset.mem_coe.mpr (Finset.mem_univ _)` to prove `x ∈ ↑univ`.

**Matrix product entries via fiber decomposition.** Reduce entry-wise to Nat: partition LHS by intermediate vertex via `Finset.card_eq_sum_card_fiberwise`, biject each fiber via `Finset.card_nbij'` with div/mod encoding (`fin_encode_fst`/`fin_encode_snd`/`fin_div_add_mod` from `Misc/Fin.lean`). For ℝ-level: `simp only [adjMatrix_apply, sq, Matrix.mul_apply, div_mul_div_comm]` + `congr 1` reduces to Nat identity, then `exact_mod_cast`.

**Connecting `eigenvalues₀` to `spectrum` and bridging `eigenvalues₀` ↔ `eigenvalues`.** For `hA.eigenvalues₀ j ∈ spectrum ℝ A`: `rw [hA.spectrum_real_eq_range_eigenvalues]`, construct witness via `Fintype.equivOfCardEq`. Key: `eigenvalues i = eigenvalues₀ (equiv.symm i)`. To lift from `eigenvalues j` to `eigenvalues₀ k`: prove `eigenvalues₀ k ∈ Set.range eigenvalues`, then `obtain ⟨j, hj⟩`. For sums: `change ∑ j, eigenvalues₀ (equiv.symm j) = _; exact Equiv.sum_comp _ _`.

**`set` + external lemmas: use `rw [hA_def]`.** After `set hA := ... with hA_def`, external lemmas won't match the `set` binding. Use `rw [hA_def]` to convert, or define derived hypotheses with `intro k; rw [hA_def]; exact external_lemma k`.

**Star instance diamond on CLMs.** `IsSelfAdjoint` for CLMs uses a different `Star` instance than `IsSelfAdjoint.sub`/`.norm_mul_self` expect (propositionally but not definitionally equal). **Workaround for `.sub`:** go through `LinearMap.IsSymmetric.sub` via `isSelfAdjoint_iff_isSymmetric` + `ContinuousLinearMap.coe_sub`. **Workaround for `.norm_mul_self`:** use `rw` instead of `exact` — `rw` is more lenient about instance matching.

**`Finset.sum_comm` loops in `simp`/`simp_rw`.** `sum_comm` is symmetric, so `simp` applies it back and forth forever. NEVER use `simp only [Finset.sum_comm]` or `simp_rw [Finset.sum_comm]`. Always use `rw [Finset.sum_comm]` (applies exactly once) or `conv_rhs => rw [Finset.sum_comm]` for positional control.

**`Finset.sum_const` produces `#univ •`, not `Fintype.card •`.** After `rw [Finset.sum_const]`, the goal contains `Finset.univ.card • c` (displayed as `#univ • c`), but `Fintype.card_fin` expects `Fintype.card (Fin d₁)`. Bridge with `Finset.card_univ`: chain `rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`.

**`set` abbreviations hide names from `rw`.** After `set Q := someOp`, `rw [lemma_about_someOp]` fails because the goal shows `Q`, not `someOp`. Lean's `rw` can't see through `set` abbreviations to match patterns. **Fix:** Create function-level helpers that work with the abbreviation: `have hQ_app : ∀ x, Q (Q x) = Q x := by intro x; change (Q * Q) x = Q x; rw [idempotent_lemma]`. The `change` tactic converts function application `Q (Q x)` back to operator form `(Q * Q) x` where `rw` can match. This is essential when proofs use `set` for readability but need to apply external operator algebra lemmas.

**Non-CLM definitions and `map_sub`.** When a definition like `clusterLift` is a plain `def` (not a `ContinuousLinearMap`), `map_sub` won't work for `lift(a) - lift(b) = lift(a - b)`. Go pointwise instead: `apply PiLp.ext; intro vk; simp only [myDef_apply, WithLp.ofLp_sub, Pi.sub_apply]`. The key lemma is `WithLp.ofLp_sub` which distributes `.ofLp` over `PiLp` subtraction.

**CLM self-adjointness via inner products.** (1) `rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]; intro f g; change @inner ℝ _ _ (A f) g = @inner ℝ _ _ f (A g)` (2) `simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, myCLM_apply]` (3) rearrange sums. Handle d=0 separately. For `IsSelfAdjoint (A - B)`: use the Star diamond workaround (`IsSymmetric.sub`).

**`ext f v` on `EuclideanSpace` CLM equalities produces `.ofLp` goals.** Simp lemmas matching `f v` form won't fire on `.ofLp v` wrapping. **Fix:** `refine ContinuousLinearMap.ext (fun f ↦ ?_); apply PiLp.ext; intro v; show A f v = B f v` — the `show` converts from `ofLp` to plain function application.

**`Fin n` has no `OfNat 0` or `OfNat 1` when `n` is variable.** Use `⟨0, by omega⟩ : Fin n` (with proof that `n > 0`) instead of `(0 : Fin n)`. Same for `1`. Bind with `set v0 : Fin n := ⟨0, by omega⟩` for reuse.

**`field_simp` leaves `↑(1 + n)` and `↑n` as separate atoms.** `ring` can't close the goal because it treats them as independent variables. Fix: add `push_cast` between `field_simp` and `ring` to normalize `↑(1 + n)` to `1 + ↑n`.

**Lifting Nat inequalities to ℝ: `Nat.cast_le` then `push_cast`.** When `h : a ≤ b` is a Nat inequality and you need the same fact over ℝ, `push_cast at h` alone fails (it expects the hypothesis to already involve casts). Instead: `have h' := Nat.cast_le (α := ℝ).mpr h; push_cast at h'`. This correctly distributes casts through products and powers: `↑(a * b ^ 2)` becomes `↑a * ↑b ^ 2`.

**`split_ifs` on nested ifs creates impossible branch combinations.** Handle with `exact absurd (h1.symm.trans h2) hne`. Alternatively, decompose nested ifs into sums of single ifs via a helper, then use `Finset.sum_add_distrib` + `Finset.sum_ite_eq'`.

**`linarith` can't handle division.** `1/↑n > 0` doesn't follow from `↑n > 0` in `linarith`'s linear fragment. Provide it as `have : (0:ℝ) < 1 / ↑n := by positivity`. Similarly, `(↑n + 1)/↑n = 1 + 1/↑n` needs `field_simp` to make `linarith`-accessible.

**Make helper definitions public when downstream proofs need them.** Remove `private` and add `@[simp]` lemmas.

**`omega` can't see through Fin literal `.val`.** `omega` treats `(⟨x, proof⟩ : Fin n).val` as an opaque atom, not as `x`. Fixes: (1) `show x - y < z; omega` forces Lean to check definitional equality, reducing the Fin val; (2) for Fin equalities `⟨a, _⟩ = ⟨b, _⟩`, use `ext; show a = b; omega`; (3) for nested Fin terms like `(M - n) + (v ⟨n + (M + j - M), _⟩).val`, use `congr 3; ext; show n + (M + j - M) = n + j; omega` — `congr` peels through `+`, `.val`, function application to reach the Fin constructor.

**`rw` fails on dependent Fin proof terms; use `congr` instead.** `rw [show M + j - M = j ...]` fails when the rewritten Nat expression appears inside a Fin literal `⟨n + (M + j - M), proof⟩` because `proof` depends on `M + j - M`, making the motive ill-typed. Fix: use `congr n; ext; show <nat-eq>; omega` to reach the Fin constructor level where `ext` produces a pure Nat goal.

**`Fin.mk.injEq` for injection proofs.** When proving injectivity of `fun pos => ⟨f pos.val, _⟩`, the hypothesis `hab` has un-beta-reduced form. Use `simp only [Fin.mk.injEq] at hab` to reduce to `f a.val = f b.val`, then `exact Fin.ext hab` or omega.

**Region-based `dite` definitions: extract val-level lemmas per region.** For definitions with multiple `if/dite` branches (e.g., `padFun` with 4 regions), write separate `*_val_rt`, `*_val_pt`, etc. lemmas with explicit negation hypotheses. Proofs then use `have h := lemma_val_region ... (show ¬... by omega) ...; rw [h]; <close>`, avoiding fragile `split_ifs` where branch counts can vary.

**MProd ordering is reversed.** Lean desugars `let mut a; let mut b; let mut c` into `MProd c (MProd b a)` — reversed from declaration order. The final `return (a, b)` becomes `match ⟨c, b, a⟩ with | ⟨c, b, a⟩ => (a, b)`. Always use `trace_state` after `unfold` to check the actual MProd layout before writing proofs about desugared do-blocks.

**`Array.set!` doesn't parse outside do-blocks.** `.set! v 0` is parsed as `(.set) (! v) 0`, causing `SDiff Bool` errors. Use `.setIfInBounds v 0` instead. Similarly, the size preservation lemma is `Array.size_setIfInBounds` (not `Array.size_set!`).

**Converting imperative loops to foldl.** Chain: `Array.forIn_toList` (array→list forIn) → `list_forIn_yield_foldl` (forIn with yield→foldl) → `forIn_range_eq_fold` / `forIn_range'_eq_fold` (range-based for→`Nat.fold`). For nested mutable state, use `foldl_mprod_to_prod` to swap MProd to Prod after conversion.

**WithLp/EuclideanSpace subtraction doesn't distribute through evaluation syntactically.** `(A - B) u` and `A u - B u` are definitionally equal but `simp`/`rw` can't see through the WithLp wrapping. `Pi.sub_apply` won't fire, nor will `ContinuousLinearMap.sub_apply`. Fix: use CLM-form LHS like `((C.walkCLM - meanCLM m) f) u` in your lemma statement, then inside the proof write `show C.walkCLM f u - meanCLM m f u = ...` to bridge via definitional equality.

**`Fintype.sum_prod_type'` and `Equiv.sum_comp` need explicit function arguments.** These lemmas get stuck on typeclass resolution (`AddCommMonoid ?m`) when the function is `_`. Always provide the explicit lambda: `(Fintype.sum_prod_type' (fun u k ↦ f u k)).symm` and `(fiberEquiv hm hdvd).sum_comp (fun v ↦ g v)`.

**`sq_sum_le_card_mul_sum_sq` has all implicit args.** Use `@sq_sum_le_card_mul_sum_sq _ ℝ _ _ _ _ Finset.univ (fun k ↦ h k)` to apply Jensen/Cauchy-Schwarz for `(∑ k, h k) ^ 2 ≤ card · ∑ k, (h k) ^ 2`.

**When a theorem is mathematically false, delete it rather than trying harder.** The irregular graph halver theorem (`graph_exists_halver_depth_le`) was sorry'd for months. Numerical testing revealed the r² factor in the Tanner bound makes ε < 3/4 impossible for degree ratio > 1. The fix wasn't a better proof technique — it was recognizing that power-of-2 targets give equal fibers (regular contracted graphs), sidestepping the degree ratio entirely. When a sorry resists proof, test the statement empirically before investing more effort.

## Mathlib API Reference

### Spectral Theorem
- Import: `Mathlib.Analysis.Matrix.Spectrum` (transitively imports eigenspace)
- `IsHermitian.eigenvalues₀ : Fin (Fintype.card n) → ℝ` — eigenvalues in decreasing order
- `eigenvalues₀_antitone : Antitone hA.eigenvalues₀`
- For real matrices: `conjTranspose_eq_transpose_of_trivial` converts `IsHermitian` ↔ `IsSymm`
- `Fintype.card (Fin n)` is NOT definitionally `n`; use `rw [Fintype.card_fin]; omega` for index proofs

### Gershgorin Circle Theorem
- Import: `Mathlib.LinearAlgebra.Matrix.Gershgorin`
- `eigenvalue_mem_ball`: needs `HasEigenvalue (toLin' A) μ`; gives `∃ k, μ ∈ closedBall (A k k) (∑ j ∈ univ.erase k, ‖A k j‖)`
- Chain: `spectrum_toLin'` (bridge matrix ↔ linear map spectra) → `HasEigenvalue.of_mem_spectrum` → `eigenvalue_mem_ball`

### Fin Sums
- `Fin.sum_univ_succAbove (f : Fin (n+1) → M) (x : Fin (n+1)) : ∑ i, f i = f x + ∑ i, f (x.succAbove i)` — decompose sum by separating one index; import `Mathlib.Algebra.BigOperators.Fin`

### Finset Counting
- `Finset.card_nbij'` takes `Set.MapsTo`/`Set.LeftInvOn`/`Set.RightInvOn` args
- `card_eq_sum_card_fiberwise` needs `Set.MapsTo` proof (see `↑univ` note above)
- `Finset.sum_ite_eq' (s : Finset α) (a : α) (b : α → β) : ∑ x ∈ s, (if x = a then b x else 0) = if a ∈ s then b a else 0`

### ContinuousLinearMap / C*-Algebra (spectral gap infrastructure)
- Import: `Mathlib.Analysis.CStarAlgebra.Matrix` (provides `Matrix.toEuclideanCLM`)
- `Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)` — star algebra equiv (Matrix ≃⋆ₐ CLM). Preserves `star`, `*`, `+`, `1`: use `map_sub`, `map_mul`, etc. Explicit type params required.
- `star` on CLMs = Hilbert adjoint; on real matrices = transpose
- `CStarRing.norm_star_mul_self : ‖x⋆ * x‖ = ‖x‖ * ‖x‖`; `IsSelfAdjoint.norm_mul_self : ‖x * x‖ = ‖x‖ ^ 2`
- With idempotency (`p * p = p`): `‖p‖ = ‖p‖²` → `‖p‖ ∈ {0, 1}`

## Architectural Direction: CLM-First Definitions

**Goal:** define graph operators natively as CLMs on `EuclideanSpace`, not as matrices. `walkCLM`/`meanCLM` use three-layer pattern. `spectralGap` = `‖walkCLM - meanCLM‖`.

No files have `#exit`. Halver/expander infrastructure fully proved, see [`docs/halver-expander.md`](docs/halver-expander.md). `zigzag_spectral_bound` proved (assembly), see [`docs/zigzag-spectral.md`](docs/zigzag-spectral.md). Base expander: fully proved, see [`docs/certificate-bridge.md`](docs/certificate-bridge.md). The correctness proof uses the Seiferas separator-based approach (`Separator/`, `Bags/`, `Seiferas.lean`).

## Proof Status by Difficulty

**Done:** `zero_one_principle`, `RegularGraph.square`, `RegularGraph.zigzag`, `completeGraph.rot_involution`, `spectralGap_nonneg`, `spectralGap_le_one`, `adjMatrix_square_eq_sq`, `spectralGap_square`, `spectralGap_complete`, `zigzagFamily`, `zigzagFamily_gap`, `expander_mixing_lemma`, `zigzag_spectral_bound` (assembly), `rvw_operator_norm_bound`, `rvw_quadratic_ineq` (core scalar inequality, in `ZigZag/RVWInequality.lean`), all ZigZag/Operators + ZigZag/Spectral sublemmas (0 sorry each), `tanner_bound` (Tanner's vertex expansion), `expander_gives_halver` (expander → ε-halver bridge), `halver_isSeparator_half` (halver → separator bridge), `scatterEmbed` + `depth_scatterEmbed_le` (scatter embedding), `separatorStage_depth_le` (depth ≤ d_sep via scatter embedding), `halvers` (MGG-based halver family for all sizes, fully proved — no `native_decide`)

**Deleted:** The original AKS ε-nearsort + tree-distance wrongness path (`Nearsort/`, `Tree/`, `Main.lean`) has been removed in favor of the Seiferas separator-based approach. The non-pow2 assembly path (`explicit_expanders_exist_zigzag`, `expanderToHalverFamily`, `seiferas_implies_sorting_network`, `seiferas_sorting_networks_exist`) has been deleted — it depended on a sorry'd theorem with a wrong statement (claiming `RegularGraph` at every size). The pow2 path (`seiferas_sorting_networks_exist_pow2`) is the sole assembly route.

**Achievable (weeks each):** The 16 sublemmas of `zigzag_spectral_bound` (11/16 done, 5 medium). See [`docs/zigzag-spectral.md`](docs/zigzag-spectral.md) for decomposition.

**Substantial (months):** Separator-quality bridge: `parent_stranger_j2_le` and `parent_stranger_eq1_le` (`Bags/Strange.lean`). Seiferas assembly (`Seiferas.lean`, blocked by `#exit` until Bags/ pipeline complete).

**Engineering (weeks, fiddly):** `wire_maps_exist` (IPS construction for scatter embedding disjointness)

### Base expander certificate pipeline (fully proved)

See [`docs/certificate-bridge.md`](docs/certificate-bridge.md) for architecture and bridge decomposition.

### Certificate GCS filenames

Certificate files uploaded to Google Cloud Storage use hyphen-separated key-value pairs, always including `-n` and `-d`, with non-default parameters appended:
```
cert-n20736-d12.b85                          # all defaults
cert-n20736-d12-seed7.b85                    # non-default seed
cert-n20736-d12-seed7-scale1048576-f64.b85   # several overrides
```
Parameters and their defaults (omit from filename when default):
- `seed` (default 42), `scale` (default 2^30 = 1073741824), `c1` (default 8·c2·(d-1)), `c2` (default 9), `refine` (default 2), `f64` (default f32; omit flag when f32)

## RVW Quadratic Inequality (fully proved)

See [`docs/rvw-inequality.md`](docs/rvw-inequality.md) for proof chain and lessons.
