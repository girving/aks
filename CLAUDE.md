# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Lean 4 formalization of the Ajtai–Komlós–Szemerédi (1983) O(n log n) sorting network construction. The project formalizes the proof architecture using the zig-zag product (Reingold–Vadhan–Wigderson 2002) as the route to explicit expander families, avoiding the heavy algebraic machinery (Margulis/LPS) that would require years of formalization effort.

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
lake build          # Full rebuild — slow, use only as fallback
lake clean          # Clean build artifacts
```

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

### Proof Visualization (`docs/index.html`)

Interactive dependency graph served via GitHub Pages from `docs/`. To refresh: update `PROOF_DATA` JSON in `docs/index.html` with theorem names, statuses, line numbers. Colors: green=proved, orange=sorry, red=axiom, blue=definition. Milestone theorems are larger with white border.

**Visualization invariant:** If all nodes in a file are green, the file must have no `sorry`s. Private lemmas with `sorry`s must be included as nodes unless they fall under a larger `sorry` theorem.

## Architecture

**Entry point:** `AKS.lean` — imports all modules and states the top-level theorem `zigzag_implies_aks_network` connecting expander existence to sorting networks.

**Modules with bottom-up dependency:**

### `AKS/Fin.lean` — `Fin` Arithmetic Helpers
Reusable encode/decode lemmas for `Fin n × Fin d` ↔ `Fin (n * d)` product indexing: `Fin.pair_lt`, `fin_encode_fst`, `fin_encode_snd`, `fin_div_add_mod`.

### `AKS/Basic.lean` — Sorting Network Theory
Sections build on each other sequentially:
1. **Comparator networks** — `Comparator`, `ComparatorNetwork` (flat list of comparators), execution model
2. **0-1 principle** — reduces sorting correctness to Boolean inputs
3. **AKS construction** — recursive build: split → recurse → merge with halvers
4. **Complexity analysis** — `IsBigO` notation, O(n log n) size
5. **Correctness** — `AKS.sorts`

### `AKS/Halver.lean` — ε-Halver Theory
ε-halvers and their composition properties, the engine driving AKS correctness.
Imports `RegularGraph.lean` for the expander → halver bridge:
1. **ε-halvers** — `IsEpsilonHalver`, `expander_gives_halver` (takes `RegularGraph`), `epsHalverMerge`
2. **Halver composition** — `IsEpsilonSorted`, `halver_composition` (geometric decrease), `halver_convergence`

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

### `AKS/Random.lean` — Base Expander for Zig-Zag Construction
Axiomatized base expander (chosen by fair dice roll, guaranteed to be random):
1. **`baseExpander`** — axiom: 12-regular graph on 20736 = 12⁴ vertices
2. **`baseExpander_gap`** — axiom: spectral gap ≤ 5/9 ≈ 0.556 (just above Alon–Boppana 2√11/12 ≈ 0.553)
3. **Certificate analysis** — all O(n)-data approaches (SDD, edge PSD, Krylov) are infeasible; see file header

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
                              → ZigZagOperators.lean ──→      ↑
                                  ZigZagSpectral.lean ─↗  Basic.lean ─→ Halver.lean
           Random.lean ────────────────────────────↗          ↑
           RVWBound.lean ─────────────────────────↗  RegularGraph.lean
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

## Proof Workflow

**Verify theorem statements against the source paper early.** Before building infrastructure, read the primary source to confirm: (1) single application or repeated/recursive? (2) essential tree structures or bookkeeping? (3) definitions match exactly? Informal sources can mislead about the precise result. E.g., `halver_composition` was mis-formulated from informal understanding; reading AKS (1983) revealed the tree structure is essential. Read primary sources at the design stage.

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

No files have `#exit`. `expander_gives_halver` takes `RegularGraph` directly (no `BipartiteExpander`). `IsEpsilonHalver` uses `onesInTop ≤ totalOnes/2 + ε·(n/2)`. `expander_mixing_lemma` is fully proved. `zigzag_spectral_bound` is decomposed into 16 sublemmas across `ZigZagOperators.lean` (1 sorry), `ZigZagSpectral.lean` (1 sorry — only d₂=0 degenerate case in `withinCluster_tilde_contraction`), `RVWBound.lean` (3 sorry's). Mathematical core: `reflection_quadratic_bound` in `RVWBound.lean` (RVW Section 4.2, cos(2θ) geometry, NOT triangle inequality). **Key:** tilde contraction hypothesis is `∀ x ∈ ker Q, ‖Bx‖ ≤ λ₂·‖x‖` (not `‖B(I-Q)‖ ≤ λ₂`). Base expander: D=12, 20736 vertices, β ≤ 5/9.

## Proof Status by Difficulty

**Done:** `zero_one_principle`, `RegularGraph.square`, `RegularGraph.zigzag`, `completeGraph.rot_involution`, `spectralGap_nonneg`, `spectralGap_le_one`, `adjMatrix_square_eq_sq`, `spectralGap_square`, `spectralGap_complete`, `zigzagFamily`, `zigzagFamily_gap` (both cases), `expander_mixing_lemma`

**Achievable (weeks):** `halver_convergence`

**Achievable (weeks each):** The 16 sublemmas of `zigzag_spectral_bound`, decomposed as follows:
- *Done (11/16):* `clusterMeanCLM_idempotent` (Q² = Q), `stepPermCLM_sq_eq_one` (Σ² = 1), `withinCluster_comp_clusterMean` (BQ = Q), `clusterMean_comp_meanCLM` (QP = P), `clusterMean_comp_withinCluster` (QB = Q), `meanCLM_eq_clusterMean_comp` (PQ = P), `withinClusterCLM_norm_le_one` (‖B‖ ≤ 1), `rvwBound_mono_left`, `rvwBound_mono_right`, `hat_block_norm` (‖QΣQ - P‖ ≤ spectralGap G₁), `withinCluster_tilde_contraction` (‖B(I-Q)‖ ≤ spectralGap G₂, 1 sorry in d₂=0 degenerate case)
- *Medium (1-2 weeks):* `clusterMeanCLM_isSelfAdjoint` (sum reorganization), `withinClusterCLM_isSelfAdjoint` (rotation bijection), `stepPermCLM_isSelfAdjoint` (involution → self-adjoint, needs bijection reindexing lemma), `zigzag_walkCLM_eq`, assembly of `zigzag_spectral_bound`
- *Hard (2-4 weeks):* `rvw_operator_norm_bound` (mathematical core — uses reflection structure of Σ, NOT triangle inequality; see `reflection_quadratic_bound`)

**Achievable (weeks):** `expander_gives_halver` (bipartite monotonicity + mixing lemma algebra; no bridge needed since it takes `RegularGraph` directly)

**Substantial (months):** `halver_composition` (combinatorial witness construction for approximate sortedness)

**Engineering (weeks, fiddly):** replacing `baseExpander` axiom with a concrete verified graph, all-sizes interpolation in `explicit_expanders_exist_zigzag`

### Base expander certificate: open approaches

Certifying a specific 12-regular graph on 20736 vertices has spectral gap ≤ 5/9. All O(n)-data approaches are infeasible (see `Random.lean`). Ideas: (1) **Sharded LDL^T** — O(n²) data, but verification parallelizable across ~10K subfiles with `decide +kernel`. (2) **Eigenspace sparsity** — if second eigenvalue has high multiplicity, sparse eigenvectors + complement bound. Both need feasibility analysis.
