# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Lean formalization of the Ajtai–Komlós–Szemerédi (1983) O(n log n) sorting network construction. The project formalizes the proof architecture using the zig-zag product (Reingold–Vadhan–Wigderson 2002) as the route to explicit expander families, avoiding the heavy algebraic machinery (Margulis/LPS) that would require years of formalization effort.

Most theorems have `sorry` placeholders — this is intentional. The codebase is a structural skeleton demonstrating the complete proof architecture.

## Build Commands

```bash
scripts/lean-check AKS/RegularGraph.lean    # Check a file (~0.2-2s for edits near end)
scripts/lean-check --all                    # Check all project files (use before committing)
scripts/lean-check --stop                   # Stop daemon (when done)
scripts/sorries                             # Audit sorry, #exit, native_decide, axiom across codebase
```

**Always use `lean-check` for verifying changes.** It keeps Mathlib imports in memory and re-elaborates from the change point forward. Most checks are sub-second. Daemon auto-starts on first use (~5s).

**Before committing, run `scripts/lean-check --all`** to catch cross-file breakage.

No tests or linters — correctness is verified through Lean's type checker.

### `lake build` (fallback only)

Use `lake build` only when debugging the `lean-check` daemon (e.g., if you suspect stale state). For checking all files, prefer `scripts/lean-check --all` — it uses the daemon cache and is much faster.

```bash
lake exe cache get    # Download prebuilt Mathlib oleans (run after lake clean or fresh clone)
lake build CertChecker  # Build precompiled certificate checker (must run before lake build)
lake build            # Full rebuild — slow, use only as fallback
lake clean            # Clean build artifacts
```

**After `lake clean` or a fresh clone, run `lake exe cache get` then `lake build CertChecker` before `lake build`.** The Mathlib cache avoids recompiling Mathlib from source (~30+ min → ~1 min). The CertChecker build produces a precompiled shared library that the AKS lib loads via `--load-dynlib` for fast `native_decide` (130s → 2s). Without it, `lake build` fails on files that need the shared lib. The `lean-check` daemon handles this automatically.

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
| `lean-check` (warm, edit near end) | 0.2-2s | Daemon crashed? Restart |
| `lean-check` (cold, first open) | 20-30s | Normal for large files |
| `lake build` (all cached) | ~1.6s | Nothing changed? |
| `lake build` (one file changed) | ~20s | Normal; use `lean-check` instead |
| `git` operations | <1s | Large repo / network |

**Timeout protocol:** When any tool call times out, record it in `scripts/SLOW_COMMANDS.md` with context (what file, what operation, wall time). Then investigate root cause.

### Git

Use merge, not rebase: `git pull --no-rebase`. Never use `git pull --rebase`.

**When the user says "commit", always push immediately after committing.** The standard workflow is: commit → pull if needed → push. Don't wait for explicit permission to push.

### Resource Constraints

**Never increase precision or memory usage without explicit permission.** If the user asks for f32, use f32. If they ask for low memory, keep it low. Do not silently switch from f32 to f64 or allocate larger buffers "because the margin is better." OOM crashes waste more time than a tight margin. If you believe higher precision is truly needed, **ask first** — explain the tradeoff and let the user decide.

**Check for zombie processes on startup/resume.** Long-running Rust or Lean processes from previous sessions can linger and consume GB of memory. On session start: `ps aux | grep -E 'compute-certificate|lake build' | grep -v grep` and kill any stale ones before launching new heavy jobs.

### Proof Visualization (`docs/index.html`)

Interactive dependency graph served via GitHub Pages from `docs/`. To refresh: update `PROOF_DATA` JSON in `docs/index.html` with theorem names, statuses, and line numbers. Colors: green=proved, orange=sorry, red=axiom, blue=definition. Milestone theorems are larger with white border.

**Update the visualization every time you prove something.** When a `sorry` is resolved, change its status in `PROOF_DATA` from `"sorry"` to `"proved"` and update its description. Then run `scripts/update-viz-lines` to sync line numbers. Do this proactively — don't wait for the user to ask.

**Line number maintenance:** `scripts/update-viz-lines` auto-syncs line numbers from source files. Run it after any code changes. Use `--check` mode to verify without modifying. The script greps each node's source file for its declaration keyword and updates the `line:` field in `PROOF_DATA`.

**Visualization invariant:** If all nodes in a file are green, the file must have no `sorry`s. Private lemmas with `sorry`s must be included as nodes unless they fall under a larger `sorry` theorem.

## Architecture

**Entry point:** `AKS.lean` — imports all modules and states the top-level theorem `zigzag_implies_aks_network` connecting expander existence to sorting networks.

**Modules with bottom-up dependency:**

### `AKS/Fin.lean` — `Fin` Arithmetic Helpers
Reusable encode/decode lemmas for `Fin n × Fin d` ↔ `Fin (n * d)` product indexing: `Fin.pair_lt`, `fin_encode_fst`, `fin_encode_snd`, `fin_div_add_mod`.

### `AKS/ComparatorNetwork.lean` — Comparator Network Theory
Foundational theory of comparator networks:
1. **Comparator networks** — `Comparator`, `ComparatorNetwork` (flat list of comparators), execution model
2. **Monotonicity preservation** — helper lemmas for comparator operations
3. **0-1 principle** — reduces sorting correctness to Boolean inputs
4. **Complexity notation** — `IsBigO` for stating asymptotic bounds

### `AKS/AKSNetwork.lean` — AKS Sorting Network Construction
The Ajtai–Komlós–Szemerédi construction and analysis:
1. **AKS construction** — recursive build: split → recurse → merge with halvers
2. **Size analysis** — `AKS.size_nlogn` (O(n log n) comparators)
3. **Correctness** — `AKS.sorts` (network correctly sorts all inputs)

### `AKS/Halver.lean` — ε-Halver Theory
ε-halvers and the expander → halver bridge. Imports `RegularGraph.lean` and `Mixing.lean`:
1. **Sorted version** — `countOnes`, `sortedVersion`, `sortedVersion_monotone`
2. **ε-halvers** — `IsEpsilonHalver` (segment-wise, AKS Section 3), `expander_gives_halver` (sorry — needs vertex expansion), `epsHalverMerge`
3. **Sortedness infrastructure** — `IsEpsilonSorted`, `Monotone.bool_pattern`
Note: The tree-based AKS correctness proof is in `TreeSorting.lean`, not here.

### `AKS/RegularGraph.lean` — Core Regular Graph Theory (~335 lines)
Core definitions and spectral gap, independent of specific constructions:
1. **Regular graphs and adjacency matrices** — `RegularGraph` (rotation map representation), `adjMatrix`, symmetry proofs
2. **Walk and mean operators** — `walkCLM` (CLM-first), `meanCLM`, `walkFun`/`walkLM`/`meanFun`/`meanLM` (three-layer pattern)
3. **Spectral gap** — `spectralGap` := `‖walkCLM - meanCLM‖` (operator norm), `spectralGap_nonneg`, `spectralGap_le_one`

### `AKS/Square.lean` — Graph Squaring (~225 lines)
Graph squaring and the spectral gap squaring identity:
1. **Graph squaring** — `G.square`, `adjMatrix_square_eq_sq`
2. **CLM identities** — self-adjointness, idempotency, `WP = PW = P`
3. **Spectral gap squaring** — `spectralGap_square`: λ(G²) = λ(G)²

### `AKS/CompleteGraph.lean` — Complete Graph (~108 lines)
The complete graph as a concrete example:
1. **Complete graph** — `completeGraph` via `Fin.succAbove`/`Fin.predAbove`
2. **Spectral gap** — `spectralGap_complete`: λ(K_{n+1}) = 1/n

### `AKS/Mixing.lean` — Expander Mixing Lemma
Fully proved expander mixing lemma via indicator vectors + Cauchy-Schwarz + operator norm.

### `AKS/Random.lean` + `AKS/Random20736.lean` — Base Expander for Zig-Zag Construction
Concrete base expander certified via davidad's triangular-inverse method:
1. **`Random20736.graph`** — concrete `RegularGraph 20736 12`, rotation map verified by `native_decide`
2. **`Random20736.gap`** — spectral gap ≤ 10/12 via `certificate_bridge` (sorry: 821 MB PSD certificate too large to embed on 16 GB machine)

### `AKS/ZigZagOperators.lean` — Zig-Zag Product and Walk Operators (~230 lines)
Defines the zig-zag product and the three CLM operators for its spectral analysis:
1. **Zig-zag product** — `G₁.zigzag G₂`, the three-step walk (zig-step-zag)
2. **Cluster encoding** — `cluster`/`port`/`encode` helpers for `Fin (n₁ * d₁)` ↔ `Fin n₁ × Fin d₁`
3. **Within-cluster walk** — `withinClusterCLM` (`B = I ⊗ W_{G₂}`)
4. **Step permutation** — `stepPermCLM` (`Σ`: permutes via `G₁.rot`)
5. **Cluster mean** — `clusterMeanCLM` (`Q`: averages within each cluster)
6. **Walk factorization** — `zigzag_walkCLM_eq`: `W_Z = B · Σ · B`

### `AKS/ZigZagSpectral.lean` — Zig-Zag Operator Properties (~130 lines)
Algebraic identities and spectral bounds for the zig-zag operators:
1. **Algebraic properties** — `Q² = Q`, `Q* = Q`, `B* = B`, `Σ² = 1`, `Σ* = Σ`, `BQ = QB = Q`
2. **Tilde contraction** — `‖B(I-Q)‖ ≤ spectralGap G₂`
3. **Hat block norm** — `‖QΣQ - P‖ ≤ spectralGap G₁`
4. **Global mean decomposition** — `P·Q = Q·P = P`

### `AKS/RVWBound.lean` — Abstract RVW Operator Bound (~85 lines)
Pure operator theory, no graph imports:
1. **`rvwBound`** — the precise RVW bound function
2. **Monotonicity** — `rvwBound_mono_left`, `rvwBound_mono_right`
3. **Abstract bound** — `rvw_operator_norm_bound`: `‖W - P‖ ≤ rvwBound(λ₁, λ₂)` from operator axioms

### `AKS/WalkBound.lean` — Walk Bound → Spectral Gap (~89 lines)
Abstract operator theory connecting walk bounds to spectral gap bounds. Imports only `RegularGraph.lean`:
1. **`spectralGap_le_of_walk_bound`** — quadratic walk bound on mean-zero vectors → `spectralGap G ≤ √(c₁/(c₂·d²))`
2. **`sqrt_coeff_le_frac`** — coefficient arithmetic: `c₁·βd² ≤ c₂·βn²` → `√(c₁/(c₂·d²)) ≤ βn/(βd·d)`

### `AKS/ZigZag.lean` — Expander Families (~115 lines)
Assembles the spectral bound and builds the iterated construction:
1. **Spectral composition theorem** — `zigzag_spectral_bound` (assembles sublemmas)
2. **Iterated construction** — `zigzagFamily`: square → zig-zag → repeat
3. **Main result** — `explicit_expanders_exist_zigzag`

### Data flow
```
Fin.lean → RegularGraph.lean → Square.lean ──────────────→ ZigZag.lean
                              → CompleteGraph.lean              ↓
                              → Mixing.lean               AKS.lean
                              → WalkBound.lean ──→ CertificateBridge.lean
                              → ZigZagOperators.lean ──→      ↑
                                  ZigZagSpectral.lean ─↗  ComparatorNetwork.lean ─→ AKSNetwork.lean ─→ Halver.lean
           Random.lean ────────────────────────────↗          ↑
           RVWBound.lean ─────────────────────────↗  RegularGraph.lean
           Certificate.lean ──→ CertificateBridge.lean
```

## Style

- Use `↦` (not `=>`) for lambda arrows: `fun x ↦ ...`
- In markdown/comments, backtick-quote Lean identifiers and filenames: `` `Fin` ``, not `Fin`; `` `ZigZag.lean` ``, not `ZigZag.lean`
- Use `/-! **Title** -/` for section headers, not numbered `§N.` or decorative `-- ═══` lines
- Move reusable helpers into their own files (e.g., `Fin` arithmetic → `AKS/Fin.lean`). Iterate in-file during development, extract before committing.
- Split files beyond ~300 lines. Smaller files = faster incremental checking (imports are precompiled; only the current file re-elaborates from the change point).
- Prefer algebraic notation over explicit constructor names: `1` not `ContinuousLinearMap.id ℝ _`, `a * b` not `ContinuousLinearMap.comp a b`. Don't add type ascriptions when the other operand pins the type.
- **Parameterize theorems over abstract bounds, not hard-coded constants.** Take spectral gap bounds (β, c, etc.) as parameters with hypotheses, not baked-in fractions. Chain `.trans` through hypotheses, not `norm_num`. Prefer explicit types/degrees (`D * D`) over `∃ d`, and concrete objects as parameters over axioms in statements. Motivation: we want explicit, computable, extractable constants.
- **Avoid non-terminal `simp`** — use `simp only [specific, lemmas]` or `rw` instead. Non-terminal `simp` is fragile (new simp lemmas can break downstream tactics). Exception: acceptable if the alternative is much uglier, but document why.

## Key Lean/Mathlib Conventions

- `autoImplicit` is **disabled** globally in `lakefile.lean` — do not add `set_option autoImplicit false` in individual files
- Depends on **Mathlib v4.27.0** — when updating, check import paths as they frequently change between versions (this has caused build breaks before)
- Lean toolchain: **v4.27.0** (pinned in `lean-toolchain`)
- **Avoid `native_decide`** — sidesteps the kernel's trust boundary. Prefer `decide +kernel` when `decide` is too slow. Only use `native_decide` as a last resort.
- **NEVER use `@[implemented_by]`, `@[extern]`, or `unsafePerformIO`** — these can make the kernel and native evaluator disagree, allowing proofs of `False`. If the kernel sees `def x := #[]` but `@[implemented_by]` provides real data, `native_decide` can prove things the kernel can't verify, creating a soundness hole. There is no safe use of `@[implemented_by]` in a proof-carrying codebase. If you need large data, encode it as a compact literal (e.g., `String` or `Nat`) that the kernel can see. **Use `@[csimp]` instead** — it requires a proof that the replacement function equals the original, so soundness is preserved. The compiler and `native_decide` use the fast version; proofs reference the simple one.

## Proof Workflow

**Skeleton correctness takes priority over filling in sorries.** A sorry with a correct statement is valuable (it documents what remains to prove); a sorry with a wrong statement is actively harmful (it creates false confidence and wasted work downstream). When auditing reveals incorrect lemma statements, fix them before working on other tractable sorries — even in other files. An honest skeleton with more sorries beats a dishonest one with fewer. See `docs/treesorting-audit.md` for the case study.

**Verify theorem statements against the source paper early.** Before building infrastructure, read the primary source to confirm: (1) single application or repeated/recursive? (2) essential tree structures or bookkeeping? (3) definitions match exactly? Informal sources can mislead about the precise result. E.g., the original single-halver composition approach was mis-formulated from informal understanding; reading AKS (1983) revealed the tree structure is essential (now in `TreeSorting.lean`). Read primary sources at the design stage.

Before attempting a `sorry`, estimate the probability of proving it directly (e.g., 30%, 50%, 80%) and report this. If the probability is below ~50%, first factor the `sorry` into intermediate lemmas — smaller steps that are each individually likely to succeed. This avoids wasting long build-test cycles on proofs that need restructuring.

**Recognize thrashing and ask the user.** After 3+ failed approaches to the same goal, stop and ask for guidance. Signs: repeated restructuring, oscillating between approaches, growing helper count without progress. A 2-minute conversation is cheaper than 30 minutes of failed builds.

**Assess proof risk before significant work.** Break non-trivial theorems into phases with risk levels: LOW (definition, direct proof), MEDIUM (standard argument, uncertain details), HIGH (novel connection, unclear if approach works). Identify the highest-risk phase, document fallback plans (axiomatize, defer, reformulate), and validate the critical bottleneck lemma before building dependencies. Escalate to user after 2-3 failed attempts on a MEDIUM+ phase.

**Analyze uncertain lemmas in natural language before formal proof attempts.** Work through the math with concrete examples BEFORE formalizing: (1) test the proof idea with specific numbers, (2) look for counterexamples, (3) verify each step informally, (4) only then formalize. Informal analysis is instant vs. 20s-2min build cycles. A careful analysis can reveal a lemma is unprovable (saving days) or clarify the exact proof structure needed.

**Keep proofs small and factored.** If a proof has more than ~3 intermediate `have` steps, factor them into standalone lemmas. Each lemma should have a small, independently testable interface — this avoids churning where fixing one step breaks steps below it.

**Prefer point-free (abstract) formulations over coordinate-based ones.** Before diving into a coordinate proof, ask whether an operator identity makes the key result fall out algebraically. Abstract identities compose cleanly; coordinate proofs each require their own index bookkeeping. **Exception:** when there's a canonical basis and the proof is naturally a finite computation (e.g., `adjMatrix_row_sum`).

**When a user suggests an approach or lesson, rephrase it for CLAUDE.md** rather than copying verbatim. Lessons should be concise, actionable, and fit the existing style. This also applies to self-generated lessons: distill the insight before recording it.

**Work autonomously on low-risk tasks once the path is clear.** When reduced to well-understood engineering (Mathlib interfacing, type bridging, assembling existing components), continue autonomously. Check in when hitting unexpected obstacles, discovering the approach won't work, or completing major milestones. Progress over permission when risk is low.

## Proof Tactics

After completing each proof, reflect on what worked and what didn't. If there's a reusable lesson — a tactic pattern, a Mathlib gotcha, a refactoring that unlocked progress — add it here (not in auto memory). This file is the single source of truth for accumulated lessons, so they persist across machines.

**Extract defs from `where` blocks before proving properties.** Inline `where` blocks produce goals with fully-unfolded terms. Instead: extract as a standalone `private def` using `.1`/`.2` projections, prove properties as separate theorems, plug both into the `where` block. Then `simp only [my_def, ...]` works cleanly. See `square_rot`/`square_rot_involution` in `RegularGraph.lean`.

**Generalize helper lemmas from the start.** Write `Fin` arithmetic helpers with the most general signature (e.g., `Fin n × Fin d`, not `Fin d × Fin d`). General versions cost nothing extra and prevent rework.

**`Fin` simp lemmas: quantify over proof terms.** When writing simp lemmas for `Fin` encode/decode, take the `isLt` proof as a parameter `(h : ... < d)` so the lemma matches any proof term Lean generates internally.

**`Fin` arithmetic: `omega` vs. specialized lemmas.** `omega` handles linear Nat but not nonlinear. Key lemmas: `Nat.add_lt_add_left`+`Nat.mul_le_mul_right` for `j*d+i < n*d`; `Nat.add_mul_div_right`/`Nat.add_mul_mod_self_right` for div/mod; `rw [Nat.mul_comm]; exact Nat.div_add_mod` for `(ij/d)*d + ij%d = ij`.

**Search Mathlib before writing custom helpers.** Existing helpers come with simp lemmas and composability. To search: (1) grep `.lake/packages/mathlib` for keywords, (2) `#check @Fin.someName` in a scratch file, (3) **LeanSearch** (https://leansearch.net/) for semantic queries. Reparameterize types to match Mathlib conventions (e.g., `Fin (n+1)` instead of `Fin d` with `hd : d ≥ 2`). Examples found: `Fin.succAbove`/`Fin.predAbove`, `Monotone.map_min`/`Monotone.map_max`.

**Avoid inline `⟨expr, by omega⟩` inside definitions.** Embedded proof terms create opaque terms that `omega`/`simp` can't see through after unfolding. Instead use Mathlib helpers or named functions with `.val` simp lemmas.

**Prefer `apply` over `exact` when arguments are inferrable.** `apply G.foo` when `v`, `i` are determined by unification. Common after `rw` rewrites.

**Nested if-then-else: manual `by_cases` over `split_ifs`.** `split_ifs` generates fragile hypothesis names. Instead: `by_cases h : condition` then `rw [if_pos h]`/`rw [if_neg h]` for each branch. Use `‹fact›` to reference anonymous `have` statements. Pattern: `by_cases h : a = c.i; · rw [if_pos h]; ...; · rw [if_neg h]; ...`.

**When stuck after 2-3 attempts, step back and refactor** rather than trying more tactic variations on the same structure. Repeated `omega`/`simp` failures usually indicate the definitions need restructuring, not a cleverer tactic combination.

**Define CLMs in three layers: standalone function → LinearMap → CLM.** (1) Standalone `def` on `Fin n → ℝ` for easy `simp`/`unfold`. (2) Wrap as `→ₗ[ℝ]` using `WithLp.toLp 2`/`WithLp.ofLp`; prove `map_add'`/`map_smul'` via `apply PiLp.ext; intro v; simp [myFun, ...]`. (3) Promote to `→L[ℝ]` via `LinearMap.toContinuousLinearMap`. Add `@[simp]` lemma `myCLM_apply` (typically `rfl`). See `walkFun`/`walkLM`/`walkCLM` in `RegularGraph.lean`.

**Triangle inequality for `|·|` via `dist_triangle`.** Convert to metric API: `|μ| = ‖μ‖ = dist μ 0` (via `Real.norm_eq_abs`, `dist_zero_right`), then `dist_triangle μ c 0`. Use `Real.dist_eq` for `dist x y = |x - y|`.

**`↑(Finset.univ)` ≠ `Set.univ` in `MapsTo` proofs.** `card_eq_sum_card_fiberwise` needs `(s : Set ι).MapsTo f ↑t`. The coercion `↑(Finset.univ)` is `Finset.univ.toSet`, not `Set.univ`. Use `Finset.mem_coe.mpr (Finset.mem_univ _)` to prove `x ∈ ↑univ`.

**Matrix product entries via fiber decomposition.** Reduce entry-wise to Nat: partition LHS by intermediate vertex via `Finset.card_eq_sum_card_fiberwise`, biject each fiber via `Finset.card_nbij'` with div/mod encoding (`fin_encode_fst`/`fin_encode_snd`/`fin_div_add_mod` from `Fin.lean`). For ℝ-level: `simp only [adjMatrix_apply, sq, Matrix.mul_apply, div_mul_div_comm]` + `congr 1` reduces to Nat identity, then `exact_mod_cast`.

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

**`split_ifs` on nested ifs creates impossible branch combinations.** Handle with `exact absurd (h1.symm.trans h2) hne`. Alternatively, decompose nested ifs into sums of single ifs via a helper, then use `Finset.sum_add_distrib` + `Finset.sum_ite_eq'`.

**`Equiv.sum_comp` for rotation-bijection sum swaps.** Reindex via `G.rotEquiv.sum_comp`, then `simp only [show ∀ p, (G.rotEquiv p : _) = G.rot p from fun _ ↦ rfl, G.rot_involution]`. The `show` bridges `Equiv` coercion with `rot`. Don't use inside `calc` — unification fails when the coercion differs.

**`linarith` can't handle division.** `1/↑n > 0` doesn't follow from `↑n > 0` in `linarith`'s linear fragment. Provide it as `have : (0:ℝ) < 1 / ↑n := by positivity`. Similarly, `(↑n + 1)/↑n = 1 + 1/↑n` needs `field_simp` to make `linarith`-accessible.

**`spectralGap_le_one` proof pattern: contraction + WP = P.** (1) `‖W‖ ≤ 1` via `opNorm_le_bound` + Cauchy-Schwarz + `rotEquiv.sum_comp`; (2) `WP = P`; (3) `‖f - Pf‖ ≤ ‖f‖` via `field_simp`+`nlinarith`; (4) factor `(W-P)f = W(f - Pf)` and chain. Handle d=0 separately. Pitfall: `Nat.cast_ne_zero.mpr` has type-class issues; use `by positivity` instead.

**Indicator vector pattern for combinatorial-spectral bridges.** (1) Define `indicatorVec S` via `(WithLp.equiv 2 _).symm (fun v ↦ if v ∈ S then 1 else 0)` with `@[simp]` apply lemma; (2) `‖indicatorVec S‖ = √↑S.card` via `EuclideanSpace.norm_sq_eq` + `sum_boole`; (3) express edge count as `⟨1_S, A(1_T)⟩` using `ite_mul`/`sum_filter`/`sum_boole`; (4) apply `abs_real_inner_le_norm` + `le_opNorm`. Key: `simp_rw [ite_mul, one_mul, zero_mul]; rw [← Finset.sum_filter]; have : univ.filter (· ∈ S) = S := by ext; simp`.

**Algebraic CLM identities via `ext + simp + field_simp`.** For operator equalities (Q² = Q, BQ = Q, QP = P): (1) `ext f vk`, (2) `simp only [operator_apply, ...]`, (3) `field_simp`. For complex cases, insert `rw [Finset.sum_div]` between simp and field_simp. See `ZigZagSpectral.lean`.

**Sum bijection helpers for reorganizing double sums.** For `Fin n₁ × Fin d₁ ≃ Fin (n₁ * d₁)`: use `Finset.sum_bij'` helpers (see `sum_encode_eq_sum`, `sum_over_cluster` in `ZigZagOperators.lean`). Apply via `conv_lhs => rw [bijection_lemma]` in calc-style proofs.

**Make helper definitions public when downstream proofs need them.** Remove `private` and add `@[simp]` lemmas when multiple files need encode/decode helpers. The larger API surface is outweighed by enabling downstream `simp`.

**Rotation bijection for walk/neighbor sum equality.** Use `RegularGraph.sum_neighbor_eq G (fun v => f v)` to show `∑ v ∑ i, f(G.neighbor v i) = ∑ v ∑ i, f v` (from `G.rot` involution). Chain with `Finset.sum_const` + `Finset.card_fin` for the d₂ factor.

**Block-diagonal operator norms via calc + per-block bounds.** (1) `opNorm_le_bound` → show `‖Bf‖ ≤ ‖f‖`, (2) expand `‖·‖²` via `EuclideanSpace.norm_sq_eq`, (3) regroup by blocks via bijection helpers, (4) `Finset.sum_le_sum` per-block, (5) connect to per-block norm bound. Use `Real.sqrt_le_sqrt` once. See `withinClusterCLM_norm_le_one` in `ZigZagSpectral.lean`.

**When hitting technical obstacles, step back and reason mathematically first.** After 2-3 failed tactic attempts, don't revert to `sorry`. Instead: (1) write out what you're proving and why it's true, (2) identify key sublemmas, (3) implement as separate helper lemmas, (4) reassemble. Helpers are reusable and make the main proof readable.

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

No files have `#exit`. `IsEpsilonHalver` uses segment-wise bounds (AKS Section 3): excess elements in initial/end segments bounded by `ε·k`. `expander_gives_halver` is sorry'd (needs vertex expansion for segment-wise bound; was previously proved for weaker one-sided midpoint definition). `expander_mixing_lemma` is fully proved. `zigzag_spectral_bound` is proved (assembly): chains all ZigZagSpectral sublemmas through `rvw_operator_norm_bound`. ZigZagOperators.lean: 0 sorry. ZigZagSpectral.lean: 0 sorry. RVWBound.lean: 2 sorry's (`rayleigh_quotient_bound` and `rvw_quadratic_ineq`). Base expander: `Random20736.graph` is a concrete `RegularGraph 20736 12` (D=12, verified by `native_decide`); gap sorry'd pending larger machine for PSD certificate. The old single-halver composition approach (`halver_composition`, `halver_convergence`, `wrongness`) has been deleted — the correct AKS proof uses the tree-based approach in `TreeSorting.lean`.

## Proof Status by Difficulty

**Done:** `zero_one_principle`, `RegularGraph.square`, `RegularGraph.zigzag`, `completeGraph.rot_involution`, `spectralGap_nonneg`, `spectralGap_le_one`, `adjMatrix_square_eq_sq`, `spectralGap_square`, `spectralGap_complete`, `zigzagFamily`, `zigzagFamily_gap`, `expander_mixing_lemma`, `zigzag_spectral_bound` (assembly), `rvw_operator_norm_bound`, all ZigZagOperators + ZigZagSpectral sublemmas (0 sorry each), `displacement_from_wrongness`, `zigzag_decreases_wrongness_v2`

**Deleted (orphaned by tree-based approach):** `halver_composition`, `halver_convergence`, `halver_decreases_wrongness`, `wrongness`, `displaced`, `wrongHalfTop`/`wrongHalfBottom` — the single-halver composition approach was superseded by the tree-based AKS Section 8 proof in `TreeSorting.lean`. Also deleted: `HasCherryShiftDamage`, `cherry_shift_implies_bounded_tree`, `cherry_shift_damage_gives_zigzag` (not in AKS paper; `r→r+1` comes from partition offset in Lemma 3)

**Achievable (weeks each):** The 16 sublemmas of `zigzag_spectral_bound`, decomposed as follows:
- *Done (11/16):* `clusterMeanCLM_idempotent` (Q² = Q), `stepPermCLM_sq_eq_one` (Σ² = 1), `withinCluster_comp_clusterMean` (BQ = Q), `clusterMean_comp_meanCLM` (QP = P), `clusterMean_comp_withinCluster` (QB = Q), `meanCLM_eq_clusterMean_comp` (PQ = P), `withinClusterCLM_norm_le_one` (‖B‖ ≤ 1), `rvwBound_mono_left`, `rvwBound_mono_right`, `hat_block_norm` (‖QΣQ - P‖ ≤ spectralGap G₁), `withinCluster_tilde_contraction` (‖B(I-Q)‖ ≤ spectralGap G₂, 1 sorry in d₂=0 degenerate case)
- *Medium (1-2 weeks):* `clusterMeanCLM_isSelfAdjoint` (sum reorganization), `withinClusterCLM_isSelfAdjoint` (rotation bijection), `stepPermCLM_isSelfAdjoint` (involution → self-adjoint, needs bijection reindexing lemma), `zigzag_walkCLM_eq`, assembly of `zigzag_spectral_bound`
- *Hard (2-4 weeks):* `rvw_quadratic_ineq` — the sole remaining `sorry` in `rvw_operator_norm_bound`. See **RVW Quadratic Inequality** section below for detailed analysis. `rayleigh_quotient_bound` is also sorry'd but currently unused.

**Substantial (months):** Halver.lean sorry (1): `expander_gives_halver` (sorry — needs vertex expansion for segment-wise `IsEpsilonHalver`). TreeSorting.lean sorrys (3). **Proved:** `zigzag_decreases_wrongness_v2` (from `HasBoundedZigzagDamage`). **Sorry:** `nearsort_has_bounded_tree_damage` (Lemma 2: recursive nearsort → `HasBoundedTreeDamage`), `bounded_tree_damage_pair_gives_zigzag` (Lemma 3: two `HasBoundedTreeDamage` → `HasBoundedZigzagDamage`), `aks_tree_sorting` (top-level assembly with halver family). Full audit: [`docs/treesorting-audit.md`](docs/treesorting-audit.md).

**Engineering (weeks, fiddly):** embedding 821 MB PSD certificate for `Random20736.gap` (needs machine with more RAM), reformulating `explicit_expanders_exist_zigzag` (current statement claims d-regular graph at every size, which is wrong)

### Base expander certificate pipeline (implemented)

Base expander graphs are certified via davidad's triangular-inverse method + `native_decide`. Data is base-85 encoded as `String` literals (compact `Expr` nodes visible to kernel). Pipeline: `Certificate.lean` (checker) → `WalkBound.lean` (abstract theory) → `CertificateBridge.lean` (bridge) → `Random{16,1728,20736}.lean` (per-size graphs). Data files in `data/{n}/` (binary, `.gitignore`d). See `docs/bridge-proof-plan.md` for background.

**Bridge decomposition (implemented):** Three lemmas: (1) `certificate_implies_walk_bound`: certificate → walk bound on mean-zero vectors [sorry'd, needs Gershgorin formalization], (2) `spectralGap_le_of_walk_bound` (in `WalkBound.lean`): walk bound → `spectralGap` bound [proved], (3) `sqrt_coeff_le_frac` (in `WalkBound.lean`): coefficient arithmetic [proved]. `certificate_bridge` chains all three and is fully proved — the only remaining sorry is `certificate_implies_walk_bound`.

## RVW Quadratic Inequality (`rvw_quadratic_ineq`)

The sole remaining `sorry` in `rvw_operator_norm_bound` (`AKS/RVWBound.lean`, ~line 814). This is the scalar core of the RVW spectral bound: after the operator-level proof reduces to a scalar inequality via reflection structure and Cauchy-Schwarz, we need:

```
X² ≤ (1 - μ₂²) · μ₁ · |X| + μ₂²
```

After clearing denominators: `G = AC + (B-C)·|p|·|X| - AB·X² ≥ 0` where `A = a²`, `B = 1-A`, `C = c²`, `X = p + 2q + r`, with constraints `|p| ≤ A`, `|r| ≤ C`, `q² ≤ (A±p)(C±r)`.

### What has been proven impossible

**`nlinarith` (diagonal Positivstellensatz) is structurally infeasible.** The inequality is tight on a 1D manifold `{C = B, p = A, r = C}` where `G = AB(1 - (A+C)²) = 0`. This forces every diagonal certificate term `h_i · m²` to vanish on the manifold, leaving too few degrees of freedom. Proven via LP at degrees 4-8, with multiple variable substitutions and constraint sets (158 Python scripts tested). **Do not attempt further LP/nlinarith variations** — the obstruction is structural, not a matter of finding the right hints or reparameterization.

**Full-matrix SOS certificates exist but can't be extracted.** SDP solvers (SCS, CLARABEL) find near-feasible degree-6 certificates, confirming the Putinar representation exists. But first-order solvers achieve only ~0.003 primal residual — insufficient for rational reconstruction (~1e-10 needed). Rounding and LP-fitting the numerical certificate also fails.

### What is already proved in Lean

The scaffold in `RVWBound.lean` (lines 765-813) already handles:
- Clearing denominators (`suffices h : A * B * X ^ 2 ≤ ...`)
- Derived bounds: `q² ≤ AC + pr` (sum CS), `A·q² ≤ C·(A²-p²)` (weighted CS)
- `concave_quad_min_boundary` helper lemma (concavity reduction)

### Viable proof paths (in order of preference)

**Path A: High-precision SDP → exact certificate → `nlinarith` hints.** Install MOSEK (free academic license) or SDPA-GMP (arbitrary precision). These achieve 1e-15+ precision, making rational reconstruction trivial. Extract the PSD matrix entries as exact rationals, decompose into squared linear combinations, and feed to `nlinarith` as `sq_nonneg (c₁·A + c₂·C + c₃·u + c₄·t + ...)` hints. This is mechanical once the solver is available. The SOS certificate uses the `(A,C,u,t)` variables where `u = √(A-p)`, `t = √(C-r)`.

**Path B: Trigonometric proof (RVW paper Section 4.2, Claim 4.4).** Formalize the paper's geometric proof: (1) recognize Σ̃ as a reflection → `⟨Σ̃v,v⟩ = cos(2θ)·‖v‖²`, (2) bound `|cos(2θ)| · cos²φ/cos²φ'` by case-splitting on angle ranges, (3) optimize over φ direction → yields `rvwBound(μ₁,μ₂)`. Risk: trig identity manipulation is laborious in Lean, but mathematically guaranteed to work.

**Path C: Axiomatize and move on.** Leave the `sorry` and work on other parts. Come back when a high-precision solver is available.

### Lessons learned (for future hard inequalities)

1. **When an LP is proven infeasible, do not try LP-like variations.** Reparameterizing variables, adding derived constraints, or increasing degree cannot fix a structural obstruction (tight manifold forcing diagonal terms to vanish). One clear infeasibility proof is sufficient.

2. **Distinguish diagonal SOS (LP) from full-matrix SOS (SDP) early.** `nlinarith` uses diagonal Positivstellensatz — each certificate term is `(single constraint product) × (single monomial)²`. Full-matrix SOS allows cross-terms `(constraint) × (linear combination of monomials)²`. When the LP is infeasible but the inequality is true, the proof requires cross-terms, which means either `nlinarith` with explicit `sq_nonneg` hints (if you know the right linear combinations) or a fundamentally different proof technique.

3. **SDP solver precision matters.** First-order solvers (SCS, CLARABEL) are fine for optimization but inadequate for exact certificate extraction. For proof-carrying code, use interior-point solvers (MOSEK, SDPA-GMP) that achieve 1e-12+ precision.

4. **Algebraic rearrangements of a hard inequality are an infinite trap.** When you have a degree-6 inequality in 4+ variables, there are infinitely many decompositions, substitutions, and case splits. Each feels like progress but they all reduce to the same core difficulty. After ~5 failed decompositions, the probability of the next one working is negligible — switch to a fundamentally different approach.

5. **Count your scripts.** If you've written 10+ analysis scripts for the same lemma without converging, you are thrashing. Stop, document what's been tried, and escalate.

### Reference

- Status document: `scripts/RVW_QUADRATIC_PROOF_STATUS.md`
- Analysis scripts: `scripts/rvw/` (saved) and `/tmp/rvw_*.py` (ephemeral, 158 scripts from Feb 2026 sessions)
