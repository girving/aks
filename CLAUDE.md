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

### Two Paths to Tree-Based Sorting

The project explores two parallel approaches for the tree-based correctness proof (halvers → sorting network):

1. **AKS original** (`TreeSorting.lean`, `Nearsort/Defs.lean`): ε-nearsorts + four-lemma tree-distance wrongness argument (AKS Sections 5–8). Extensive infrastructure (~2600 lines), several sorry's remaining.

2. **Paterson/Seiferas separator-based** (`AKS/Separator/`): replaces ε-nearsorts with (γ,ε)-separators + outsider counting with Seiferas's single potential function. Definitions in place; downstream files not yet implemented. See `docs/separator-plan.md` for the full design.

Both paths share: `IsEpsilonHalver` (halver definition), expander infrastructure (`RegularGraph.lean`, `ZigZag/Expanders.lean`), and `ComparatorNetwork.lean`. The separator path may be simpler to complete due to cleaner abstractions (outsider counting vs. tree-distance wrongness).

## Build Commands

```bash
scripts/lean-check AKS/RegularGraph.lean    # Check a file (~0.2-2s for edits near end)
scripts/lean-check --all                    # Check all project files (use before committing)
scripts/lean-check --stop                   # Stop daemon (when done)
scripts/sorries                             # Audit sorry, #exit, native_decide, axiom across codebase
```

**Always use `lean-check` for verifying changes.** It keeps Mathlib imports in memory and re-elaborates from the change point forward. Most checks are sub-second. Daemon auto-starts on first use (~5s). **Do not manually restart the daemon when files are added, moved, or deleted** — the daemon detects file layout changes and automatically restarts `lake serve` on the next check.

**Before committing, run `scripts/lean-check --all`** to catch cross-file breakage.

No tests or linters — correctness is verified through Lean's type checker.

### Exploratory Lean snippets

Use `scripts/lean-test` to run ad-hoc Lean snippets (checking types, `#print`, `#check`, proof experiments). **Use `echo ... | scripts/lean-test`** (pipe form), not `<<<` heredoc — the `<<<` syntax doesn't match the allowed-command pattern in `.claude/settings.json` and triggers a permission prompt:
```bash
echo '#check @Finset.card_union_le' | scripts/lean-test
echo 'import AKS.Bags.Defs
#check @jStrangerCount_union_le' | scripts/lean-test
```

### `lake build` (fallback only)

Use `lake build` only when debugging the `lean-check` daemon (e.g., if you suspect stale state). For checking all files, prefer `scripts/lean-check --all` — it uses the daemon cache and is much faster.

```bash
lake exe cache get    # Download prebuilt Mathlib oleans (run after lake clean or fresh clone)
lake build            # Full rebuild — slow, use only as fallback
lake clean            # Clean build artifacts
```

**After `lake clean` or a fresh clone, run `lake exe cache get` before `lake build`.** The Mathlib cache avoids recompiling Mathlib from source (~30+ min → ~1 min). Lake automatically builds the CertCheck shared library (`libaks_CertCheck.so`) and passes `--load-dynlib` to modules that import it, thanks to `precompileModules := true` on the CertCheck lean_lib. The `lean-check` daemon also pre-builds `CertCheck:shared` on startup.

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

**Show a diffstat before committing.** Run `git diff --stat` (for staged+unstaged changes) so the user can see which files changed and how many lines were added/removed before the commit is created.

### URL Fetching

**When asked to fetch a URL that returns an error (403, timeout, etc.), ask the user for help** rather than silently falling back to searching local files or other sources. The user shared that URL for a reason — the content matters, and local files may contain outdated or different information.

### Resource Constraints

**Never increase precision or memory usage without explicit permission.** If the user asks for f32, use f32. If they ask for low memory, keep it low. Do not silently switch from f32 to f64 or allocate larger buffers "because the margin is better." OOM crashes waste more time than a tight margin. If you believe higher precision is truly needed, **ask first** — explain the tradeoff and let the user decide.

**Check for zombie processes on startup/resume.** Long-running Rust or Lean processes from previous sessions can linger and consume GB of memory. On session start: `ps aux | grep -E 'certificate|lake|lean' | grep -v grep` and kill stale ones with `pkill -f lean` / `pkill -f lake` before launching new heavy jobs.

### Proof Visualization (`docs/index.html`)

Interactive dependency graph served via GitHub Pages from `docs/`. To refresh: update `PROOF_DATA` JSON in `docs/index.html` with theorem names, statuses, and line numbers. Colors: green=proved, orange=sorry, red=axiom, blue=definition. Milestone theorems are larger with white border.

**Update the visualization every time you prove something.** When a `sorry` is resolved, change its status in `PROOF_DATA` from `"sorry"` to `"proved"` and update its description. Then run `scripts/update-viz-lines` to sync line numbers. Do this proactively — don't wait for the user to ask.

**Line number maintenance:** `scripts/update-viz-lines` auto-syncs line numbers from source files. Run it after any code changes. Use `--check` mode to verify without modifying. The script greps each node's source file for its declaration keyword and updates the `line:` field in `PROOF_DATA`.

**Visualization invariant:** If all nodes in a file are green, the file must have no `sorry`s. Private lemmas with `sorry`s must be included as nodes unless they fall under a larger `sorry` theorem.

## Architecture

**Entry point:** `AKS.lean` — imports all modules and states the top-level theorem `zigzag_implies_aks_network` connecting expander existence to sorting networks.

**Modules with bottom-up dependency:**

### `AKS/Misc/Fin.lean` — `Fin` Arithmetic Helpers
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
4. **Main theorem** — `aks_tree_sorting` (sorry — assembly), `zigzag_implies_aks_network`

### `AKS/TreeDamageStability.lean` — Lemma 2a (Parallel Work Target)
`parity_nearsort_has_bounded_tree_damage` (sorry): parity-restricted nearsort → `HasBoundedTreeDamage`. Stability property. Imports only `TreeSorting.lean`.

### `AKS/TreeDamageImprovement.lean` — Lemma 2b (Parallel Work Target)
`parity_nearsort_has_improved_bound` (sorry): even-level nearsort → `HasImprovedBound`. Cherry-parity improvement property. Imports only `TreeSorting.lean`.

### `AKS/Halver.lean` — ε-Halver Theory
ε-halvers and the expander → halver bridge. Imports `Graph/Regular.lean` and `Mixing.lean`:
1. **Sorted version** — `countOnes`, `sortedVersion`, `sortedVersion_monotone`
2. **ε-halvers** — `rank`, `EpsilonInitialHalved`, `EpsilonHalved`, `IsEpsilonHalver` (permutation-based, AKS Section 3), `epsHalverMerge`
3. **Sortedness infrastructure** — `IsEpsilonSorted`, `Monotone.bool_pattern`
Note: The tree-based AKS correctness proof is in `TreeSorting.lean`, not here. The `expander_gives_halver` proof is in `Halver/ExpanderToHalver.lean`.

### `AKS/Halver/Tanner.lean` — Tanner's Vertex Expansion Bound (~270 lines)
Tanner's bound and supporting lemmas. Imports `Mixing.lean` and `Square.lean`:
1. **Neighborhood/codegree** — `neighborSet`, `codeg`, `codeg_eq_zero_of_not_mem`
2. **Codegree sum** — `codeg_sum`: Σ codeg(v) = d·|T| (via rotation bijection)
3. **Walk-codegree identity** — `walkCLM_indicatorVec`, `norm_sq_walkCLM_indicatorVec`
4. **Orthogonal decomposition** — `norm_sq_walk_indicatorVec_le`: ‖W·1_T‖² ≤ |T|·(|T| + β²(n-|T|))/n
5. **Tanner's bound** — `tanner_bound`: |N(T)|·(|T| + β²(n-|T|)) ≥ |T|·n (fully proved)

### `AKS/Halver/ExpanderToHalver.lean` — Expander → ε-Halver Bridge (~650 lines)
Proves `expander_gives_halver` via Tanner's bound. Imports `Halver.lean`, `Halver/Tanner.lean`, `TreeSorting.lean`:
1. **Bipartite construction** — `bipartiteComparators G` (compare position v with m + G.neighbor(v,p))
2. **Edge monotonicity** — generalized to `LinearOrder α`: `exec_bipartite_edge_mono`
3. **Permutation counting** — `exec_perm_card_lt`: exactly k positions have output val < k
4. **Tanner-based proof** — `bipartite_epsilon_initial_halved`, `bipartite_epsilon_final_halved`
5. **Main theorem** — `expander_gives_halver` (fully proved, 0 sorry)

### `AKS/Graph/Regular.lean` — Core Regular Graph Theory (~335 lines)
Core definitions and spectral gap, independent of specific constructions:
1. **Regular graphs and adjacency matrices** — `RegularGraph` (rotation map representation), `adjMatrix`, symmetry proofs
2. **Walk and mean operators** — `walkCLM` (CLM-first), `meanCLM`, `walkFun`/`walkLM`/`meanFun`/`meanLM` (three-layer pattern)
3. **Spectral gap** — `spectralGap` := `‖walkCLM - meanCLM‖` (operator norm), `spectralGap_nonneg`, `spectralGap_le_one`

### `AKS/Graph/Square.lean` — Graph Squaring (~225 lines)
Graph squaring and the spectral gap squaring identity:
1. **Graph squaring** — `G.square`, `adjMatrix_square_eq_sq`
2. **CLM identities** — self-adjointness, idempotency, `WP = PW = P`
3. **Spectral gap squaring** — `spectralGap_square`: λ(G²) = λ(G)²

### `AKS/Graph/Complete.lean` — Complete Graph (~108 lines)
The complete graph as a concrete example:
1. **Complete graph** — `completeGraph` via `Fin.succAbove`/`Fin.predAbove`
2. **Spectral gap** — `spectralGap_complete`: λ(K_{n+1}) = 1/n

### `AKS/Halver/Mixing.lean` — Expander Mixing Lemma
Fully proved expander mixing lemma via indicator vectors + Cauchy-Schwarz + operator norm.

### `AKS/Random/` — Base Expander for Zig-Zag Construction
Concrete base expander certified via davidad's triangular-inverse method:
1. **`Random20736.graph`** — concrete `RegularGraph 20736 12`, rotation map verified by `native_decide`
2. **`Random20736.gap`** — spectral gap ≤ 10/12 via `certificate_bridge` (fully proved, 821 MB PSD certificate verified by `native_decide`)

### `AKS/ZigZag/Operators.lean` — Zig-Zag Product and Walk Operators (~230 lines)
Defines the zig-zag product and the three CLM operators for its spectral analysis:
1. **Zig-zag product** — `G₁.zigzag G₂`, the three-step walk (zig-step-zag)
2. **Cluster encoding** — `cluster`/`port`/`encode` helpers for `Fin (n₁ * d₁)` ↔ `Fin n₁ × Fin d₁`
3. **Within-cluster walk** — `withinClusterCLM` (`B = I ⊗ W_{G₂}`)
4. **Step permutation** — `stepPermCLM` (`Σ`: permutes via `G₁.rot`)
5. **Cluster mean** — `clusterMeanCLM` (`Q`: averages within each cluster)
6. **Walk factorization** — `zigzag_walkCLM_eq`: `W_Z = B · Σ · B`

### `AKS/ZigZag/Spectral.lean` — Zig-Zag Operator Properties (~130 lines)
Algebraic identities and spectral bounds for the zig-zag operators:
1. **Algebraic properties** — `Q² = Q`, `Q* = Q`, `B* = B`, `Σ² = 1`, `Σ* = Σ`, `BQ = QB = Q`
2. **Tilde contraction** — `‖B(I-Q)‖ ≤ spectralGap G₂`
3. **Hat block norm** — `‖QΣQ - P‖ ≤ spectralGap G₁`
4. **Global mean decomposition** — `P·Q = Q·P = P`

### `AKS/ZigZag/RVWInequality.lean` — Core RVW Scalar Inequality (~400 lines)
Pure polynomial inequality, no operator imports. Fully proved (0 sorry):
1. **`rvw_reduced_ineq`** — V1' inequality via a-quadratic case analysis
2. **`rvw_cleared_ineq`** — cleared form via concavity + boundary reparameterization
3. **`rvw_quadratic_ineq`** — division form via `p·X ≤ |p|·|X|`

### `AKS/ZigZag/RVWBound.lean` — Abstract RVW Operator Bound
Operator theory importing `RVWInequality.lean`:
1. **`rvwBound`** — the precise RVW bound function
2. **Monotonicity** — `rvwBound_mono_left`, `rvwBound_mono_right`
3. **Abstract bound** — `rvw_operator_norm_bound`: `‖W - P‖ ≤ rvwBound(λ₁, λ₂)` from operator axioms

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

### `AKS/Misc/ForLoop.lean` — For-Loop Characterization (~105 lines)
Proves `for k in [:n] do` in `Id` monad equals `Nat.fold` + partition-fold lemmas.

### `Bench/` — Benchmarks, Tests, and Profiles
Not part of the proof. Contains optimization variants (`CertFast`, `CertV2`, `CertV7`, `CertParallel`) and profiling tools. Run via `scripts/bench` or `lake exe cert-{bench,test,profile}`.

### `AKS/ZigZag/Expanders.lean` — Expander Families (~115 lines)
Assembles the spectral bound and builds the iterated construction:
1. **Spectral composition theorem** — `zigzag_spectral_bound` (assembles sublemmas)
2. **Iterated construction** — `zigzagFamily`: square → zig-zag → repeat
3. **Main result** — `explicit_expanders_exist_zigzag`

### `AKS/Separator/Defs.lean` — (γ, ε)-Separator Definitions (~50 lines)
ε-approximate γ-separation (Seiferas 2009, Section 6). Alternative to the
ε-nearsort path in `Nearsort/Defs.lean`; both paths share `IsEpsilonHalver`.
1. **`SepInitial`**, **`SepFinal`** — one-sided separation (initial/final via `αᵒᵈ`)
2. **`IsApproxSep`** — both-sided ε-approximate γ-separation
3. **`IsSeparator`** — network-level property (quantified over permutations)
For γ = 1/2 this reduces to `IsEpsilonHalver`. Uses Seiferas's two-parameter
(γ, ε) formulation, not Paterson's three-parameter (λ, ε, ε₀).

### `AKS/Separator/` — Remaining Files (Planned)
See `docs/separator-plan.md` for full design. Planned files:
1. **`Family.lean`** — `SeparatorFamily` structure (analogous to `HalverFamily`)
2. **`FromHalver.lean`** — `halverToSeparator` computable construction (Seiferas Section 6)

### `AKS/Bags/` — Bag-Tree Sorting (~450 lines)
Seiferas's bag-based tree argument: separators → O(log n) depth sorting network.
All definitions validated by Rust simulation (`rust/test-bags.rs`).
1. **`Defs.lean`** (~125 lines) — `bagSize`, `nativeBagIdx`, `isJStranger`, `jStrangerCount`. Basic lemmas proved. `isJStranger_antitone` sorry'd.
2. **`Invariant.lean`** (~215 lines) — `SeifInvariant` (four-clause structure), `SatisfiesC3`/`SatisfiesC4_gt1`/`SatisfiesC4_eq1` (parameter constraints), `initialInvariant` (proved), maintenance theorems (sorry'd). Critical bottleneck: `stranger_bound_maintained_eq1` (j=1 case).
3. **`Stage.lean`** (~55 lines) — `separatorStage`, `active_bags_disjoint` (sorry'd), `separatorStage_depth_le` (sorry'd).
4. **`TreeSort.lean`** (~80 lines) — `separatorSortingNetwork`, `separatorSortingNetwork_depth_bound` (proved via calc), `separatorSortingNetwork_sorts` (sorry'd).

### Data flow
```
Misc/Fin.lean → Graph/Regular.lean → Graph/Square.lean ─────→ ZigZag/Expanders.lean
                               → Graph/Complete.lean           ↓
                              → Halver/Mixing.lean ─→ Halver/Tanner.lean  AKS.lean
                              → Cert/WalkBound.lean ──→ Cert/Bridge.lean
                              → ZigZag/Operators.lean ──→     ↑
                                  ZigZag/Spectral.lean ─↗ Sort/*.lean ─→ Tree/AKSNetwork.lean
           Random/*.lean ──────────────────────────↗          ↑
           ZigZag/RVWInequality.lean ─→ ZigZag/RVWBound.lean ─↗  Halver/*.lean ─→ Halver/ExpanderToHalver.lean
           CertCheck.lean ──→ Cert/Defs.lean ──→ Cert/Bridge.lean  Halver/Tanner.lean ─↗
                                                                    ↓
                                                         Separator/Defs.lean
                                                         Separator/Family.lean
                                                         Separator/FromHalver.lean
                                                                    ↓
                                                         Bags/Defs.lean
                                                         Bags/Invariant.lean
                                                         Bags/Stage.lean
                                                         Bags/TreeSort.lean ──→ Tree/AKSNetwork.lean
```

## Style

- **Remove unused hypotheses from proved theorems.** Don't prefix with `_` — delete the argument entirely and update all callers. Unused arguments are dead weight that obscures what a theorem actually needs.
- Use `↦` (not `=>`) for lambda arrows: `fun x ↦ ...`
- In markdown/comments, backtick-quote Lean identifiers and filenames: `` `Fin` ``, not `Fin`; `` `ZigZag.lean` ``, not `ZigZag.lean`
- Use `/-! **Title** -/` for section headers, not numbered `§N.` or decorative `-- ═══` lines
- Move reusable helpers into their own files (e.g., `Fin` arithmetic → `AKS/Misc/Fin.lean`). Iterate in-file during development, extract before committing.
- Split files beyond ~300 lines. Smaller files = faster incremental checking (imports are precompiled; only the current file re-elaborates from the change point).
- **Use subdirectories for cohesive subsystems.** Group related files under `AKS/Name/*.lean`. Consumers import leaf modules directly. When moving files into a subdirectory: (1) `git mv` the files, (2) update imports in moved files and all dependents, (3) update `file:` paths in `docs/index.html` PROOF_DATA, (4) update CLAUDE.md architecture section, (5) run `scripts/update-viz-lines`.
- Prefer algebraic notation over explicit constructor names: `1` not `ContinuousLinearMap.id ℝ _`, `a * b` not `ContinuousLinearMap.comp a b`. Don't add type ascriptions when the other operand pins the type.
- **Parameterize theorems over abstract bounds, not hard-coded constants.** Take spectral gap bounds (β, c, etc.) as parameters with hypotheses, not baked-in fractions. Chain `.trans` through hypotheses, not `norm_num`. Prefer explicit types/degrees (`D * D`) over `∃ d`, and concrete objects as parameters over axioms in statements. Motivation: we want explicit, computable, extractable constants.
- **Define constructions as computable `def`s, prove properties as separate theorems.** Never use `∃ (net : ComparatorNetwork n), ...` when the witness is known — define it as a `def` and prove properties about it. This gives: (1) computability, (2) composability (downstream code can refer to the object directly), (3) cleaner proofs (no `Exists.choose`/`noncomputable`). Example: `expanderHalver` is a `def` with `expanderHalver_isEpsilonHalver` and `expanderHalver_size` as theorems — not `∃ net, IsEpsilonHalver net β ∧ net.size ≤ m * d`. Similarly, bundle families as `structure`s with computable fields + proof fields (see `HalverFamily`).
- **Prove depth bounds, not size bounds.** For comparator networks, depth (parallel rounds) is the fundamental complexity measure. Size ≤ n/2 · depth follows trivially from `size_le_half_n_mul_depth`. Always state the depth bound first; derive size as a corollary. This applies to `HalverFamily` (already correct: `depth_le` is fundamental, `size_le` derived), separator families, and the top-level sorting network theorem.
- **Avoid non-terminal `simp`** — use `simp only [specific, lemmas]` or `rw` instead. Non-terminal `simp` is fragile (new simp lemmas can break downstream tactics). Exception: acceptable if the alternative is much uglier, but document why.
- **Don't create import-only re-export files.** A file that just imports its children (e.g., `AKS/Sort.lean` importing `Sort.Defs`, `Sort.Monotone`, etc.) adds indirection with no value. Import leaf modules directly from the root `AKS.lean` or from consuming files.
- **Colocate files with their consumers, not their topic.** If a file has only one downstream user, move it into that subsystem's directory. E.g., `Mixing.lean` was used only by `Halver/Tanner.lean`, so it belongs in `AKS/Halver/`, not at the top level.

## Key Lean/Mathlib Conventions

- `autoImplicit` is **disabled** globally in `lakefile.lean` — do not add `set_option autoImplicit false` in individual files
- Depends on **Mathlib v4.27.0** — when updating, check import paths as they frequently change between versions (this has caused build breaks before)
- Lean toolchain: **v4.27.0** (pinned in `lean-toolchain`)
- **Avoid `native_decide`** — sidesteps the kernel's trust boundary. Prefer `decide +kernel` when `decide` is too slow. Only use `native_decide` as a last resort.
- **NEVER use `@[implemented_by]`, `@[extern]`, or `unsafePerformIO`** — these can make the kernel and native evaluator disagree, allowing proofs of `False`. If the kernel sees `def x := #[]` but `@[implemented_by]` provides real data, `native_decide` can prove things the kernel can't verify, creating a soundness hole. There is no safe use of `@[implemented_by]` in a proof-carrying codebase. If you need large data, encode it as a compact literal (e.g., `String` or `Nat`) that the kernel can see.
- **Do not use `@[csimp]` in `CertCheck.lean`** — `CertCheck` is a separate precompiled library (`precompileModules := true`) that contains only definitions, no proofs. `@[csimp]` requires a proof that the replacement equals the original, which would force proofs into the precompiled module and break modularity. Instead, prove the bridge theorem (`checkCertificateFast_eq_slow`) in a separate file (`AKS/Cert/FastProof.lean`) that imports both `CertCheck` and Mathlib.

## Proof Workflow

**Skeleton correctness takes priority over filling in sorries.** A sorry with a correct statement is valuable (it documents what remains to prove); a sorry with a wrong statement is actively harmful (it creates false confidence and wasted work downstream). When auditing reveals incorrect lemma statements, fix them before working on other tractable sorries — even in other files. An honest skeleton with more sorries beats a dishonest one with fewer. See `docs/treesorting-audit.md` for the case study.

**Verify theorem statements against the source paper early.** Before building infrastructure, read the primary source to confirm: (1) single application or repeated/recursive? (2) essential tree structures or bookkeeping? (3) definitions match exactly? Informal sources can mislead about the precise result. E.g., the original single-halver composition approach was mis-formulated from informal understanding; reading AKS (1983) revealed the tree structure is essential (now in `TreeSorting.lean`). Read primary sources at the design stage.

**Formalization adds lemmas for implicit hypotheses.** When an informal proof says "X follows because the construction has property P," the formal proof needs an explicit predicate for P and a lemma proving the construction satisfies it. Having more intermediate lemmas than the paper is EXPECTED — the extra lemmas make implicit paper assumptions explicit. Don't conflate "fewer lemmas" with "closer to the paper"; the paper's argument structure matters more than its lemma count. E.g., the AKS paper's Lemma 3 implicitly assumes zig operates on even-level cherries; the formalization needs `HasImprovedBound` as an explicit predicate + `parity_nearsort_has_improved_bound` proving the construction satisfies it.

Before attempting a `sorry`, estimate the probability of proving it directly (e.g., 30%, 50%, 80%) and report this. If the probability is below ~50%, first factor the `sorry` into intermediate lemmas — smaller steps that are each individually likely to succeed. This avoids wasting long build-test cycles on proofs that need restructuring.

**Recognize thrashing and ask the user.** After 3+ failed approaches to the same goal, stop and ask for guidance. Signs: repeated restructuring, oscillating between approaches, growing helper count without progress. A 2-minute conversation is cheaper than 30 minutes of failed builds.

**Never silently abandon an agreed plan.** If a plan was approved and a step turns out harder than expected, do NOT silently switch to a shortcut (e.g., replacing a proof with `native_decide` or `sorry`). Always confirm radical plan changes with the user first — explain what's hard, what the alternatives are, and let them decide. A 2-minute conversation about changing course is far cheaper than discovering the change broke assumptions downstream.

**Never change fast code to make proofs easier.** `CertCheck.lean` contains optimized imperative code (`checkCertificateFast`, `checkColumnNormBound`, `mulAdjWith`, etc.) that must stay exactly as-is. The job is to PROVE the existing fast code correct via bridge theorems, not to modify it. When a proof about imperative code is hard, discuss the difficulty with the user — don't silently switch to "make the code easier to prove about" by adding `native_decide` calls, slowing down the fast path, or replacing imperative code with pure equivalents. The `native_decide` in `Random*.lean` should only be on `checkCertificateFast`; everything else must be derived via structural proofs.

**Assess proof risk before significant work.** Break non-trivial theorems into phases with risk levels: LOW (definition, direct proof), MEDIUM (standard argument, uncertain details), HIGH (novel connection, unclear if approach works). Identify the highest-risk phase, document fallback plans (axiomatize, defer, reformulate), and validate the critical bottleneck lemma before building dependencies. Escalate to user after 2-3 failed attempts on a MEDIUM+ phase.

**Analyze uncertain lemmas in natural language before formal proof attempts.** Work through the math with concrete examples BEFORE formalizing: (1) test the proof idea with specific numbers, (2) look for counterexamples, (3) verify each step informally, (4) only then formalize. Informal analysis is instant vs. 20s-2min build cycles. A careful analysis can reveal a lemma is unprovable (saving days) or clarify the exact proof structure needed.

**Test sorry'd theorem statements empirically with optimized Rust.** Before investing weeks proving a lemma, write a Rust program (`rust/test-*.rs`, run via `cargo +nightly -Zscript`) that implements the Lean construction and checks the property across many random inputs and parameter ranges. Key techniques: (1) mirror the Lean `def`s exactly in Rust (comparator networks, graph operations, recursive constructions), (2) build *families* of test inputs at every size the construction needs — e.g., random d-regular bipartite graphs as synthetic halvers, not just one concrete graph, (3) measure empirical bounds (ε, depth) across sub-sizes with a safety margin, (4) test the claimed bound at multiple parameter values (γ', t, etc.). This catches wrong theorem statements early — a false lemma will show violations immediately, while a true one will pass thousands of trials. The cost is a few hundred lines of Rust vs. weeks of wasted proof effort on a wrong statement.

**Keep proofs small and factored.** If a proof has more than ~3 intermediate `have` steps, factor them into standalone lemmas. Each lemma should have a small, independently testable interface — this avoids churning where fixing one step breaks steps below it.

**Prefer point-free (abstract) formulations over coordinate-based ones.** Before diving into a coordinate proof, ask whether an operator identity makes the key result fall out algebraically. Abstract identities compose cleanly; coordinate proofs each require their own index bookkeeping. **Exception:** when there's a canonical basis and the proof is naturally a finite computation (e.g., `adjMatrix_row_sum`).

**When a user suggests an approach or lesson, rephrase it for CLAUDE.md** rather than copying verbatim. Lessons should be concise, actionable, and fit the existing style. This also applies to self-generated lessons: distill the insight before recording it.

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

**When stuck after 2-3 attempts, step back and refactor** rather than trying more tactic variations on the same structure. Repeated `omega`/`simp` failures usually indicate the definitions need restructuring, not a cleverer tactic combination.

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

**`split_ifs` on nested ifs creates impossible branch combinations.** Handle with `exact absurd (h1.symm.trans h2) hne`. Alternatively, decompose nested ifs into sums of single ifs via a helper, then use `Finset.sum_add_distrib` + `Finset.sum_ite_eq'`.

**`Equiv.sum_comp` for rotation-bijection sum swaps.** Reindex via `G.rotEquiv.sum_comp`, then `simp only [show ∀ p, (G.rotEquiv p : _) = G.rot p from fun _ ↦ rfl, G.rot_involution]`. The `show` bridges `Equiv` coercion with `rot`. Don't use inside `calc` — unification fails when the coercion differs.

**`linarith` can't handle division.** `1/↑n > 0` doesn't follow from `↑n > 0` in `linarith`'s linear fragment. Provide it as `have : (0:ℝ) < 1 / ↑n := by positivity`. Similarly, `(↑n + 1)/↑n = 1 + 1/↑n` needs `field_simp` to make `linarith`-accessible.

**`spectralGap_le_one` proof pattern: contraction + WP = P.** (1) `‖W‖ ≤ 1` via `opNorm_le_bound` + Cauchy-Schwarz + `rotEquiv.sum_comp`; (2) `WP = P`; (3) `‖f - Pf‖ ≤ ‖f‖` via `field_simp`+`nlinarith`; (4) factor `(W-P)f = W(f - Pf)` and chain. Handle d=0 separately. Pitfall: `Nat.cast_ne_zero.mpr` has type-class issues; use `by positivity` instead.

**Indicator vector pattern for combinatorial-spectral bridges.** (1) Define `indicatorVec S` via `(WithLp.equiv 2 _).symm (fun v ↦ if v ∈ S then 1 else 0)` with `@[simp]` apply lemma; (2) `‖indicatorVec S‖ = √↑S.card` via `EuclideanSpace.norm_sq_eq` + `sum_boole`; (3) express edge count as `⟨1_S, A(1_T)⟩` using `ite_mul`/`sum_filter`/`sum_boole`; (4) apply `abs_real_inner_le_norm` + `le_opNorm`. Key: `simp_rw [ite_mul, one_mul, zero_mul]; rw [← Finset.sum_filter]; have : univ.filter (· ∈ S) = S := by ext; simp`.

**Algebraic CLM identities via `ext + simp + field_simp`.** For operator equalities (Q² = Q, BQ = Q, QP = P): (1) `ext f vk`, (2) `simp only [operator_apply, ...]`, (3) `field_simp`. For complex cases, insert `rw [Finset.sum_div]` between simp and field_simp. See `ZigZag/Spectral.lean`.

**Sum bijection helpers for reorganizing double sums.** For `Fin n₁ × Fin d₁ ≃ Fin (n₁ * d₁)`: use `Finset.sum_bij'` helpers (see `sum_encode_eq_sum`, `sum_over_cluster` in `ZigZag/Operators.lean`). Apply via `conv_lhs => rw [bijection_lemma]` in calc-style proofs.

**Make helper definitions public when downstream proofs need them.** Remove `private` and add `@[simp]` lemmas when multiple files need encode/decode helpers. The larger API surface is outweighed by enabling downstream `simp`.

**Rotation bijection for walk/neighbor sum equality.** Use `RegularGraph.sum_neighbor_eq G (fun v => f v)` to show `∑ v ∑ i, f(G.neighbor v i) = ∑ v ∑ i, f v` (from `G.rot` involution). Chain with `Finset.sum_const` + `Finset.card_fin` for the d₂ factor.

**Block-diagonal operator norms via calc + per-block bounds.** (1) `opNorm_le_bound` → show `‖Bf‖ ≤ ‖f‖`, (2) expand `‖·‖²` via `EuclideanSpace.norm_sq_eq`, (3) regroup by blocks via bijection helpers, (4) `Finset.sum_le_sum` per-block, (5) connect to per-block norm bound. Use `Real.sqrt_le_sqrt` once. See `withinClusterCLM_norm_le_one` in `ZigZag/Spectral.lean`.

**When hitting technical obstacles, step back and reason mathematically first.** After 2-3 failed tactic attempts, don't revert to `sorry`. Instead: (1) write out what you're proving and why it's true, (2) identify key sublemmas, (3) implement as separate helper lemmas, (4) reassemble. Helpers are reusable and make the main proof readable.

**`omega` can't see through Fin literal `.val`.** `omega` treats `(⟨x, proof⟩ : Fin n).val` as an opaque atom, not as `x`. Fixes: (1) `show x - y < z; omega` forces Lean to check definitional equality, reducing the Fin val; (2) for Fin equalities `⟨a, _⟩ = ⟨b, _⟩`, use `ext; show a = b; omega`; (3) for nested Fin terms like `(M - n) + (v ⟨n + (M + j - M), _⟩).val`, use `congr 3; ext; show n + (M + j - M) = n + j; omega` — `congr` peels through `+`, `.val`, function application to reach the Fin constructor.

**`rw` fails on dependent Fin proof terms; use `congr` instead.** `rw [show M + j - M = j ...]` fails when the rewritten Nat expression appears inside a Fin literal `⟨n + (M + j - M), proof⟩` because `proof` depends on `M + j - M`, making the motive ill-typed. Fix: use `congr n; ext; show <nat-eq>; omega` to reach the Fin constructor level where `ext` produces a pure Nat goal.

**`Fin.mk.injEq` for injection proofs.** When proving injectivity of `fun pos => ⟨f pos.val, _⟩`, the hypothesis `hab` has un-beta-reduced form. Use `simp only [Fin.mk.injEq] at hab` to reduce to `f a.val = f b.val`, then `exact Fin.ext hab` or omega.

**Region-based `dite` definitions: extract val-level lemmas per region.** For definitions with multiple `if/dite` branches (e.g., `padFun` with 4 regions), write separate `*_val_rt`, `*_val_pt`, etc. lemmas with explicit negation hypotheses. Proofs then use `have h := lemma_val_region ... (show ¬... by omega) ...; rw [h]; <close>`, avoiding fragile `split_ifs` where branch counts can vary.

**Ghost state elimination for imperative buffer reuse.** When imperative code reuses buffers across loop iterations (e.g., `checkPSDColumnsFull` with `bz`/`zCol`): (1) define a "big state" including all mutable vars (visible + ghost), (2) show the ghost state is fully reset/overwritten at the start of each iteration, (3) prove `project(bigStep ghost_any) = smallStep(project input)` — ghost doesn't affect output, (4) by induction on the list, `project(foldl bigStep) = foldl smallStep (project init)`. Key helpers: `foldl_simulation` (generic projection through foldl), `foldl_mprod_to_prod` (MProd↔Prod swap).

**MProd ordering is reversed.** Lean desugars `let mut a; let mut b; let mut c` into `MProd c (MProd b a)` — reversed from declaration order. The final `return (a, b)` becomes `match ⟨c, b, a⟩ with | ⟨c, b, a⟩ => (a, b)`. Always use `trace_state` after `unfold` to check the actual MProd layout before writing proofs about desugared do-blocks.

**`Array.set!` doesn't parse outside do-blocks.** `.set! v 0` is parsed as `(.set) (! v) 0`, causing `SDiff Bool` errors. Use `.setIfInBounds v 0` instead. Similarly, the size preservation lemma is `Array.size_setIfInBounds` (not `Array.size_set!`).

**Involution-based symmetry for counting folds.** To prove `f(v,w) = f(w,v)` for graph-based counting: (1) flatten nested counting fold to flat fold over `{0,...,N-1}`, (2) apply `fold_sum_invol` (involution preserves counting folds, proved by strong induction + `fold_sum_replace`), (3) transform predicates using round-trip properties of the involution, close with `and_comm`. See `portCount_symm` in `ScatterBridge.lean`.

**Converting imperative loops to foldl.** Chain: `Array.forIn_toList` (array→list forIn) → `list_forIn_yield_foldl` (forIn with yield→foldl) → `forIn_range_eq_fold` / `forIn_range'_eq_fold` (range-based for→`Nat.fold`). For nested mutable state, use `foldl_mprod_to_prod` to swap MProd to Prod after conversion.

**Scatter = gather under `NeighborSymm`.** Scatter-based accumulation (loop over sources k, distribute `z[k]` to `bz[neighbors[k*d+p]]`) equals gather-based (`mulAdjPre`: loop over targets i, collect from `neighbors[i*d+p]`) when adjacency is symmetric. The bridge goes through `portCount_symm` (port counts are symmetric under rotation involution). See `scatterMulAdj_eq_mulAdjPre` in `ScatterBridge.lean`.

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

No files have `#exit`. `IsEpsilonHalver` uses a permutation-based definition (AKS Section 3): for every permutation input, segment-wise bounds on displaced elements via `rank`. `expander_gives_halver` is fully proved (in `Halver/ExpanderToHalver.lean`) via Tanner's vertex expansion bound (`Halver/Tanner.lean`) + edge monotonicity + permutation counting. `expander_mixing_lemma` is fully proved. `zigzag_spectral_bound` is proved (assembly): chains all ZigZag/Spectral sublemmas through `rvw_operator_norm_bound`. ZigZag/Operators.lean: 0 sorry. ZigZag/Spectral.lean: 0 sorry. ZigZag/RVWBound.lean: 0 sorry (scalar inequality proved in `ZigZag/RVWInequality.lean`). Base expander: `Random20736.graph` is a concrete `RegularGraph 20736 12` (D=12, verified by `native_decide`); gap fully proved (821 MB PSD certificate verified by `native_decide`). The old single-halver composition approach (`halver_composition`, `halver_convergence`, `wrongness`) has been deleted — the correct AKS proof uses the tree-based approach in `TreeSorting.lean`.

## Proof Status by Difficulty

**Done:** `zero_one_principle`, `RegularGraph.square`, `RegularGraph.zigzag`, `completeGraph.rot_involution`, `spectralGap_nonneg`, `spectralGap_le_one`, `adjMatrix_square_eq_sq`, `spectralGap_square`, `spectralGap_complete`, `zigzagFamily`, `zigzagFamily_gap`, `expander_mixing_lemma`, `zigzag_spectral_bound` (assembly), `rvw_operator_norm_bound`, `rvw_quadratic_ineq` (core scalar inequality, in `ZigZag/RVWInequality.lean`), all ZigZag/Operators + ZigZag/Spectral sublemmas (0 sorry each), `displacement_from_wrongness`, `zigzag_decreases_wrongness_v2`, `tanner_bound` (Tanner's vertex expansion), `expander_gives_halver` (expander → ε-halver bridge)

**Deleted (orphaned by tree-based approach):** `halver_composition`, `halver_convergence`, `halver_decreases_wrongness`, `wrongness`, `displaced`, `wrongHalfTop`/`wrongHalfBottom` — the single-halver composition approach was superseded by the tree-based AKS Section 8 proof in `TreeSorting.lean`. Also deleted: `HasCherryShiftDamage`, `cherry_shift_implies_bounded_tree`, `cherry_shift_damage_gives_zigzag` (not in AKS paper; `r→r+1` comes from partition offset in Lemma 3)

**Achievable (weeks each):** The 16 sublemmas of `zigzag_spectral_bound`, decomposed as follows:
- *Done (11/16):* `clusterMeanCLM_idempotent` (Q² = Q), `stepPermCLM_sq_eq_one` (Σ² = 1), `withinCluster_comp_clusterMean` (BQ = Q), `clusterMean_comp_meanCLM` (QP = P), `clusterMean_comp_withinCluster` (QB = Q), `meanCLM_eq_clusterMean_comp` (PQ = P), `withinClusterCLM_norm_le_one` (‖B‖ ≤ 1), `rvwBound_mono_left`, `rvwBound_mono_right`, `hat_block_norm` (‖QΣQ - P‖ ≤ spectralGap G₁), `withinCluster_tilde_contraction` (‖B(I-Q)‖ ≤ spectralGap G₂, 1 sorry in d₂=0 degenerate case)
- *Medium (1-2 weeks):* `clusterMeanCLM_isSelfAdjoint` (sum reorganization), `withinClusterCLM_isSelfAdjoint` (rotation bijection), `stepPermCLM_isSelfAdjoint` (involution → self-adjoint, needs bijection reindexing lemma), `zigzag_walkCLM_eq`, assembly of `zigzag_spectral_bound`
- *Done:* `rvw_quadratic_ineq` (proved in `ZigZag/RVWInequality.lean` via a-quadratic case analysis)

**Substantial (months):** **Proved:** `expander_gives_halver` (in `Halver/ExpanderToHalver.lean`, via Tanner's bound), `tanner_bound` (in `Halver/Tanner.lean`), `zigzag_decreases_wrongness_v2` (from `HasBoundedZigzagDamage`), `bounded_tree_damage_pair_gives_zigzag` (Lemma 3: `HasImprovedBound` + `HasBoundedTreeDamage` → `HasBoundedZigzagDamage`, algebraic). **Sorry (in separate files for parallel work):** `parity_nearsort_has_bounded_tree_damage` (Lemma 2a, `TreeDamageStability.lean`), `parity_nearsort_has_improved_bound` (Lemma 2b, `TreeDamageImprovement.lean`), `aks_tree_sorting` (assembly, `AKSNetwork.lean`). Full audit: [`docs/treesorting-audit.md`](docs/treesorting-audit.md).

**Engineering (weeks, fiddly):** reformulating `explicit_expanders_exist_zigzag` (current statement claims d-regular graph at every size, which is wrong)

### Base expander certificate pipeline (implemented)

Base expander graphs are certified via davidad's triangular-inverse method + `native_decide`. Data is base-85 encoded as `String` literals (compact `Expr` nodes visible to kernel). Pipeline: `CertCheck.lean` (checker) → `Cert/WalkBound.lean` (abstract theory) → `Cert/Bridge.lean` (bridge) → `Random/{16,1728,20736}.lean` (per-size graphs). Data files in `data/{n}/` (`.b85` base-85 text, `.gitignore`d) — Rust writes base85 directly so Lean just reads the text as-is. See `docs/bridge-proof-plan.md` for background.

**Bridge decomposition (implemented):** Three lemmas: (1) `certificate_implies_walk_bound`: certificate → walk bound on mean-zero vectors [sorry'd, needs Gershgorin formalization], (2) `spectralGap_le_of_walk_bound` (in `Cert/WalkBound.lean`): walk bound → `spectralGap` bound [proved], (3) `sqrt_coeff_le_frac` (in `Cert/WalkBound.lean`): coefficient arithmetic [proved]. `certificate_bridge` chains all three and is fully proved — the only remaining sorry is `certificate_implies_walk_bound`.

## RVW Quadratic Inequality (proved)

`rvw_quadratic_ineq` is fully proved in `AKS/ZigZag/RVWInequality.lean`. The proof chain:
1. **`rvw_reduced_ineq`** — core V1' inequality in 4 variables (α, wh, zh, a). Proved by treating as a quadratic in `a` and case-splitting: disc ≤ 0 (no real roots), vertex ≥ 1 (f(1) ≥ 0 suffices), or vertex ≤ 0 (f(0) ≥ 0 suffices).
2. **`rvw_cleared_ineq`** — cleared polynomial form, via concavity reduction + boundary reparameterization.
3. **`rvw_quadratic_ineq`** — original form with spectral gap parameters, via `p·X ≤ |p|·|X|`.

### Lesson: when `nlinarith` is structurally infeasible, try algebraic case analysis

Direct `nlinarith` (diagonal Positivstellensatz) was proven infeasible for this inequality. SOS certificates exist but couldn't be extracted at sufficient precision. The successful approach was mathematical: reparameterize to expose a quadratic in one variable, then case-split on discriminant sign and vertex location. Each case reduces to elementary `nlinarith` with explicit ring identity hints.
