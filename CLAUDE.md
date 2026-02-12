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

**Always use `lean-check` for verifying changes.** It keeps Mathlib imports in memory and re-elaborates only from the change point forward. Since proof iteration typically happens at the end of a file, most checks are sub-second. The daemon auto-starts on first use (~5s).

**Before committing, run `scripts/lean-check --all`** to verify all project files type-check. This catches cross-file breakage (e.g., a changed signature in one file breaking a downstream import) that single-file checks miss.

There are no tests or linter configurations. Correctness is verified through Lean's type checker — if `lean-check` reports no errors, all type-checked proofs are valid.

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

## Architecture

**Entry point:** `AKS.lean` — imports all modules and states the top-level theorem `zigzag_implies_aks_network` connecting expander existence to sorting networks.

**Modules with bottom-up dependency:**

### `AKS/Fin.lean` — `Fin` Arithmetic Helpers
Reusable encode/decode lemmas for `Fin n × Fin d` ↔ `Fin (n * d)` product indexing: `Fin.pair_lt`, `fin_encode_fst`, `fin_encode_snd`, `fin_div_add_mod`.

### `AKS/Basic.lean` — Sorting Network Theory
Sections build on each other sequentially:
1. **Comparator networks** — `Comparator`, `ComparatorNetwork` (flat list of comparators), execution model
2. **0-1 principle** — reduces sorting correctness to Boolean inputs
3. **Expander graphs** — `BipartiteExpander`, spectral gap, existence
4. **AKS construction** — recursive build: split → recurse → merge with halvers
5. **Complexity analysis** — `IsBigO` notation, O(n log n) size
6. **Correctness** — `AKS.sorts`

### `AKS/Halver.lean` — ε-Halver Theory
ε-halvers and their composition properties, the engine driving AKS correctness:
1. **ε-halvers** — `IsEpsilonHalver`, `expander_gives_halver`, `epsHalverMerge`
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
                                  ZigZagSpectral.lean ─↗  Basic.lean → Halver.lean
           Random.lean ────────────────────────────↗
           RVWBound.lean ─────────────────────────↗
```

## Style

- Use `↦` (not `=>`) for lambda arrows: `fun x ↦ ...`
- In markdown/comments, backtick-quote Lean identifiers and filenames: `` `Fin` ``, not `Fin`; `` `ZigZag.lean` ``, not `ZigZag.lean`
- Use `/-! **Title** -/` for section headers, not numbered `§N.` or decorative `-- ═══` lines
- Keep mathematically high-level files (e.g., `ZigZag.lean`) clean by moving reusable helpers (e.g., `Fin` arithmetic lemmas) into their own files (e.g., `AKS/Fin.lean`). Iterate with helpers in the same file during development, then extract as a final pass before committing.
- Split files that grow beyond ~300 lines. Smaller files mean faster incremental checking (the Lean server re-elaborates from the change point, but only within the current file — imports are precompiled). The optimal split point for tooling-assisted development is smaller than for human-authored files.
- Prefer algebraic notation over explicit constructor names when a typeclass instance exists: `1` not `ContinuousLinearMap.id ℝ _`, `a * b` not `ContinuousLinearMap.comp a b`, `0` not `ContinuousLinearMap.zero`, etc. The algebraic forms are shorter, more readable, and match how mathematicians write. Don't add type ascriptions — if the other operand pins the type (e.g., `1 - meanCLM n`), bare `1` suffices.
- **Parameterize theorems over abstract bounds, not hard-coded constants.** Theorem statements should take spectral gap bounds (β, c, etc.) as parameters with hypotheses encoding the required inequalities, rather than baking in specific fractions like `1/5` or `1/2`. Proofs should chain `.trans` through these hypotheses, not `norm_num` specific arithmetic. Similarly, prefer explicit types/degrees (e.g., `D * D`) over existential quantification (`∃ d`), and take concrete objects (like base expanders) as parameters rather than using axioms directly in theorem statements. The motivation: we eventually want explicit sorting network code with explicit constants (even if those constants are galactic), which requires every bound to be computable and extractable — not hidden inside an existential or baked into a proof term.

## Key Lean/Mathlib Conventions

- `autoImplicit` is **disabled** globally in `lakefile.lean` — do not add `set_option autoImplicit false` in individual files
- Depends on **Mathlib v4.27.0** — when updating, check import paths as they frequently change between versions (this has caused build breaks before)
- Lean toolchain: **v4.27.0** (pinned in `lean-toolchain`)
- **Avoid `native_decide`** — it compiles to native code, which sidesteps the kernel's trust boundary. Prefer `decide +kernel` (a faster variant of `decide` that uses the kernel evaluator) when `decide` alone is too slow. Only use `native_decide` as a last resort for computations that are truly infeasible in the kernel.

## Proof Workflow

Before attempting a `sorry`, estimate the probability of proving it directly (e.g., 30%, 50%, 80%) and report this. If the probability is below ~50%, first factor the `sorry` into intermediate lemmas — smaller steps that are each individually likely to succeed. This avoids wasting long build-test cycles on proofs that need restructuring.

**Recognize thrashing and ask the user.** If you attempt 3+ substantially different approaches to the same goal without progress (especially if you catch yourself thinking "I'm overcomplicating this"), stop and ask the user for guidance. They may see a cleaner mathematical reformulation or an alternative approach to the theory. A 2-minute conversation is cheaper than 30 minutes of failed build cycles. Signs of thrashing: repeated restructuring of the same proof, oscillating between approaches, or growing helper lemma counts without the main goal getting closer.

**Keep proofs small and factored.** If a proof has more than ~3 intermediate `have` steps that later steps depend on, factor the intermediates into standalone lemmas. Long proofs with deep dependency chains cause churning: fixing one step breaks steps below it, and each build-test cycle is expensive. Each lemma should have a small, independently testable interface. Concretely: if you're building `C` from `B` from `A` all inside one proof, extract `A` and `B` as lemmas so you can iterate on each in isolation.

**Prefer point-free (abstract) formulations over coordinate-based ones.** Proofs about linear algebra, spectral theory, or similar can be dramatically cleaner when stated in terms of operator identities (e.g., `(M-P)² = M²-P` from `MP = P`) rather than entry-wise coordinate calculations (e.g., sorted eigenvalue multiset matching). Before diving into a coordinate proof, ask whether there's an abstract reformulation — a projection, an operator norm, a functional calculus — that makes the key identity fall out algebraically. The payoff compounds: abstract identities compose cleanly, while coordinate proofs each require their own index bookkeeping. **Exception:** when there's a single canonical basis and the proof is naturally a finite computation (e.g., `adjMatrix_row_sum`), coordinates are fine.

**When a user suggests an approach or lesson, rephrase it for CLAUDE.md** rather than copying verbatim. Lessons should be concise, actionable, and fit the existing style. This also applies to self-generated lessons: distill the insight before recording it.

## Proof Tactics

After completing each proof, reflect on what worked and what didn't. If there's a reusable lesson — a tactic pattern, a Mathlib gotcha, a refactoring that unlocked progress — add it here (not in auto memory). This file is the single source of truth for accumulated lessons, so they persist across machines.

**Extract defs from `where` blocks before proving properties.** Proving involutions/identities inline in a `where` block produces goals with fully-unfolded terms — nested `G.1` instead of `G.rot`, `Fin` literals with opaque `isLt` proof terms, and destructuring `let` compiled to `match`. Instead: extract the function as a standalone `private def` using `.1`/`.2` projections (not `let ⟨a, b⟩ := ...`), prove properties as separate theorems, plug both into the `where` block. Then `simp only [my_def, ...]` can unfold + rewrite in one pass. See `square_rot` / `square_rot_involution` in `RegularGraph.lean`.

**Generalize helper lemmas from the start.** Write `Fin` arithmetic helpers with the most general signature that makes sense (e.g., `Fin n × Fin d`, not `Fin d × Fin d`). The `square` helpers were initially specialized and had to be re-generalized for `zigzag`. General versions cost nothing extra and prevent rework.

**`Fin` simp lemmas: quantify over proof terms.** When writing simp lemmas for `Fin` encode/decode, take the `isLt` proof as a parameter `(h : ... < d)` so the lemma matches any proof term Lean generates internally.

**`Fin` arithmetic: `omega` vs. specialized lemmas.** `omega` handles linear `Nat` arithmetic but not nonlinear (`a * b` where both vary). For `j * d + i < n * d`: use `calc` with `Nat.add_lt_add_left` + `Nat.mul_le_mul_right`. For div/mod: `Nat.add_mul_div_right`, `Nat.add_mul_mod_self_right`, `Nat.div_eq_of_lt`, `Nat.mod_eq_of_lt`. For `(ij/d)*d + ij%d = ij`: `rw [Nat.mul_comm]; exact Nat.div_add_mod` (`omega` can't prove this).

**Search Mathlib before writing custom helpers.** Before defining a helper function or writing a manual proof, check whether Mathlib already provides it — existing helpers come with simp lemmas, API, and composability that custom code won't have. This applies especially to `Fin` operations, order theory, and algebraic identities. Examples found so far: `Fin.succAbove`/`Fin.predAbove` (skip-one-value embeddings with involution lemmas), `Monotone.map_min`/`Monotone.map_max` (`Mathlib.Order.MinMax`). To search: grep `.lake/packages/mathlib` for keywords (fastest), or use `#check @Fin.someName` in a scratch file to test if a name exists. Reparameterize types to match Mathlib conventions (e.g., `Fin (n+1)` instead of `Fin d` with `hd : d ≥ 2`).

**Avoid inline `⟨expr, by omega⟩` inside definitions.** Constructing `Fin` values with embedded proof terms inside a `def` creates opaque terms that `omega`/`simp` can't see through after unfolding (`omega` cannot reduce `(⟨a, h⟩ : Fin n).val` or `(x, y).1` after `split_ifs`). Instead use Mathlib helpers (see above) or named functions with `.val` simp lemmas. This turned `complete_rot_involution` from 8+ failed attempts into a 2-line `simp only` proof.

**Prefer `apply` over `exact` when arguments are inferrable.** `exact G.foo v i` can be shortened to `apply G.foo` when `v` and `i` are determined by unification with the goal. This is common after `rw` rewrites that leave a goal matching the lemma's conclusion.

**When stuck after 2-3 attempts, step back and refactor** rather than trying more tactic variations on the same structure. Repeated `omega`/`simp` failures usually indicate the definitions need restructuring, not a cleverer tactic combination.

**Define CLMs in three layers: standalone function → LinearMap → CLM.** (1) Define the function on plain vectors (`Fin n → ℝ`) as a standalone `def`, so proofs can `simp`/`unfold` it without fighting type wrappers. (2) Wrap it as a `→ₗ[ℝ]` on `EuclideanSpace`, using `WithLp.toLp 2` / `WithLp.ofLp` to bridge: `toFun f := WithLp.toLp 2 (myFun (WithLp.ofLp f))`. Prove `map_add'` and `map_smul'` via `apply PiLp.ext; intro v; simp [myFun, ...]`. (3) Promote to `→L[ℝ]` via `LinearMap.toContinuousLinearMap` (free in finite dimension). Finally, prove an `@[simp]` lemma `myCLM_apply` unpacking the CLM to the standalone function — this is typically `rfl` because `ofLp_toLp` is `rfl`. See `walkFun` / `walkLM` / `walkCLM` / `walkCLM_apply` in `RegularGraph.lean`.

**Triangle inequality for `|·|` via `dist_triangle`.** `abs_add` is hard to find. Instead, convert to the metric space API: `|μ| = ‖μ‖ = dist μ 0` (via `Real.norm_eq_abs`, `dist_zero_right` — no `Real.` prefix), then `dist_triangle μ c 0` gives `|μ| ≤ dist μ c + ‖c‖`. Use `Real.dist_eq` for `dist x y = |x - y|`.

**`↑(Finset.univ)` ≠ `Set.univ` in `MapsTo` proofs.** `card_eq_sum_card_fiberwise` needs `(s : Set ι).MapsTo f ↑t`. The coercion `↑(Finset.univ)` is `Finset.univ.toSet`, not `Set.univ`. Use `Finset.mem_coe.mpr (Finset.mem_univ _)` to prove `x ∈ ↑univ`.

**Matrix product entries via fiber decomposition.** To prove `adjMatrix G.square = (adjMatrix G) ^ 2`, reduce entry-wise to a Nat equality: `#{two-step walks u→v} = ∑_w #{edges u→w} × #{edges w→v}`. Use `Finset.card_eq_sum_card_fiberwise` to partition the LHS by intermediate vertex, then `Finset.card_nbij'` with div/mod encoding to biject each fiber with a product of filters. The `fin_encode_fst`/`fin_encode_snd`/`fin_div_add_mod` lemmas from `Fin.lean` handle the round-trip proofs. For the ℝ-level: `simp only [adjMatrix_apply, sq, Matrix.mul_apply, div_mul_div_comm]` + `rw [← Finset.sum_div, Nat.cast_mul]` + `congr 1` reduces to the Nat identity, then `exact_mod_cast key`.

**Connecting `eigenvalues₀` to `spectrum`.** To show `hA.eigenvalues₀ j ∈ spectrum ℝ A`: (1) `rw [hA.spectrum_real_eq_range_eigenvalues]`, (2) construct witness `⟨(Fintype.equivOfCardEq (Fintype.card_fin _)) j, proof⟩`, (3) prove equality with `unfold Matrix.IsHermitian.eigenvalues; simp [Equiv.symm_apply_apply]`. Key insight: `eigenvalues i = eigenvalues₀ (equiv.symm i)`, so `eigenvalues (equiv j) = eigenvalues₀ j`.

**Bridging `eigenvalues₀` ↔ `eigenvalues` dichotomies.** To lift a result about `eigenvalues j` (indexed by `Fin (n+1)`) to `eigenvalues₀ k` (indexed by `Fin (Fintype.card (Fin (n+1)))`): prove `eigenvalues₀ k ∈ Set.range eigenvalues` via the `spectrum` recipe above, then `obtain ⟨j, hj⟩` and substitute. Avoids constructing `Fintype.equivOfCardEq` explicitly. For sums: `change ∑ j, eigenvalues₀ (equiv.symm j) = _; exact Equiv.sum_comp _ _`.

**`set` + external lemmas: use `rw [hA_def]`.** After `set hA := adjMatrix_isHermitian G with hA_def`, the goal uses `hA` but external lemmas produce `(adjMatrix_isHermitian G).eigenvalues₀`. Use `rw [hA_def]` to convert back before `exact`. Define derived hypotheses (dichotomy, sum) inside the proof with `intro k; rw [hA_def]; exact external_lemma k` so they match the `set` binding.

**Star instance diamond on CLMs.** `IsSelfAdjoint` for CLMs uses `ContinuousLinearMap.instStarId`, but `IsSelfAdjoint.sub` and `IsSelfAdjoint.norm_mul_self` expect `StarAddMonoid.toInvolutiveStar.toStar` (from `[StarRing E]`). These are propositionally but not definitionally equal. **Workaround for `.sub`:** go through `LinearMap.IsSymmetric.sub` — convert to `IsSymmetric` via `isSelfAdjoint_iff_isSymmetric`, use `ContinuousLinearMap.coe_sub` to decompose the coercion, apply `IsSymmetric.sub`. **Workaround for `.norm_mul_self`:** use `rw [← hsa.norm_mul_self]` (rewrite) instead of `exact hsa.norm_mul_self.symm` — `rw` is more lenient about instance matching than `exact`. More broadly, when typeclass diamonds cause `exact` to fail, try `rw` — it performs less strict instance checking.

**`Finset.sum_comm` loops in `simp_rw`.** `simp_rw` applies under binders, so `simp_rw [Finset.sum_comm]` endlessly rewrites nested sums. Use `conv_rhs => rw [Finset.sum_comm]` (or `conv_lhs`) to apply it exactly once at the desired position.

**CLM self-adjointness via inner products.** To prove `IsSelfAdjoint A` for a CLM on `EuclideanSpace ℝ (Fin n)`: (1) `rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]; intro f g; change @inner ℝ _ _ (A f) g = @inner ℝ _ _ f (A g)` (2) decompose with `simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, myCLM_apply]` (3) rearrange sums. Handle d=0 separately. For `IsSelfAdjoint (A - B)` from `IsSelfAdjoint A` and `IsSelfAdjoint B`: use the Star diamond workaround above (`IsSymmetric.sub`).

**`ext f v` on `EuclideanSpace` CLM equalities produces `.ofLp` goals.** After `ext f v` on `A f = B f` where the codomain is `EuclideanSpace ℝ (Fin n)`, the second `ext v` produces goals with `(... f).ofLp v` wrapping. Simp lemmas like `meanCLM_apply` and `walkCLM_apply` (which match `f v` form) may not fire. **Fix:** use `refine ContinuousLinearMap.ext (fun f ↦ ?_); apply PiLp.ext; intro v; show A f v = B f v` — the `show` converts from `ofLp` to plain function application (definitionally equal). Then `rw`/`simp` with `_apply` lemmas works.

**`Fin n` has no `OfNat 0` or `OfNat 1` when `n` is variable.** Use `⟨0, by omega⟩ : Fin n` (with proof that `n > 0`) instead of `(0 : Fin n)`. Same for `1`. Bind with `set v0 : Fin n := ⟨0, by omega⟩` for reuse.

**`field_simp` leaves `↑(1 + n)` and `↑n` as separate atoms.** `ring` can't close the goal because it treats them as independent variables. Fix: add `push_cast` between `field_simp` and `ring` to normalize `↑(1 + n)` to `1 + ↑n`.

**`split_ifs` on nested ifs creates impossible branch combinations.** `if a then 1 else if b then -1 else 0` with `split_ifs` creates a case `a ∧ b` even when `a` and `b` are mutually exclusive. Handle with `exact absurd (h1.symm.trans h2) hne`. Alternatively, decompose nested ifs into sums of single ifs (`= (if a then 1 else 0) + (if b then -1 else 0)`) via a helper lemma, then use `Finset.sum_add_distrib` + `Finset.sum_ite_eq'`.

**`Equiv.sum_comp` for rotation-bijection sum swaps.** To show `∑ v ∑ i, f(nbr v i) · g v = ∑ v ∑ i, f v · g(nbr v i)`: reindex via `G.rotEquiv.sum_comp (fun q ↦ f q.1 * g (G.rot q).1)`, then `simp only [show ∀ p, (G.rotEquiv p : _) = G.rot p from fun _ ↦ rfl, G.rot_involution]`. The `show` lemma bridges the `Equiv` coercion with the raw `rot` function. Don't use `Equiv.sum_comp` inside `calc` — it fails to unify when the coercion differs.

**`linarith` can't handle division.** `1/↑n > 0` doesn't follow from `↑n > 0` in `linarith`'s linear fragment. Provide it as `have : (0:ℝ) < 1 / ↑n := by positivity`. Similarly, `(↑n + 1)/↑n = 1 + 1/↑n` needs `field_simp` to make `linarith`-accessible.

**`spectralGap_le_one` proof pattern: contraction + WP = P.** To show `‖W - P‖ ≤ 1` for walk operator W and mean projection P: (1) prove `‖W‖ ≤ 1` via `opNorm_le_bound` + Cauchy-Schwarz (`sq_sum_le_card_mul_sum_sq` from `Mathlib.Algebra.Order.Chebyshev`) + double-counting via `rotEquiv.sum_comp`; (2) prove `WP = P` (walk of a constant = same constant); (3) prove `‖f - Pf‖ ≤ ‖f‖` via `field_simp` + `nlinarith`; (4) factor `(W-P)f = W(f - Pf)` and chain inequalities. Handle d = 0 separately with `‖Pf‖ ≤ ‖f‖` (Cauchy-Schwarz). Key Lean pitfall: `Nat.cast_ne_zero.mpr` often has type-class mismatch issues; use `by positivity` instead.

**Indicator vector pattern for combinatorial-spectral bridges.** To relate a combinatorial quantity (edge count between sets) to a spectral bound (operator norm): (1) define `indicatorVec S` via `(WithLp.equiv 2 _).symm (fun v ↦ if v ∈ S then 1 else 0)` with an `@[simp]` apply lemma that's `rfl`; (2) prove `‖indicatorVec S‖ = √↑S.card` via `EuclideanSpace.norm_sq_eq` + `sum_boole`; (3) express the combinatorial quantity as `⟨1_S, A(1_T)⟩` by unfolding inner product (`PiLp.inner_apply` + `RCLike.inner_apply` + `conj_trivial`), then using `ite_mul`/`sum_filter`/`sum_boole` to convert indicator sums to filter cardinalities; (4) apply `abs_real_inner_le_norm` (Cauchy-Schwarz) + `le_opNorm` for the spectral bound. Key tactic sequence for indicator sums: `simp_rw [ite_mul, one_mul, zero_mul]; rw [← Finset.sum_filter]; have : univ.filter (· ∈ S) = S := by ext; simp`.

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
- `Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))` — star algebra equivalence
- As a `StarAlgEquiv`, it preserves `star`, `*`, `+`, `1`, and scalar multiplication: use `map_sub`, `map_smul`, `map_one`, `map_mul`, etc.
- `star` on CLMs is the Hilbert adjoint; `star` on `Matrix n n ℝ` is `conjTranspose = transpose` (for reals)
- `CStarRing (E →L[𝕜] E)` instance exists (from `Mathlib.Analysis.InnerProductSpace.Adjoint`): gives `CStarRing.norm_star_mul_self : ‖x⋆ * x‖ = ‖x‖ * ‖x‖`
- `IsSelfAdjoint.norm_mul_self : ‖x * x‖ = ‖x‖ ^ 2` — for self-adjoint elements in a C*-ring
- Combined with idempotency (`p * p = p`): `‖p‖ = ‖p‖²` → `‖p‖ ∈ {0, 1}`
- Explicit type params needed: `(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n))` — without them, coercion from `StarAlgEquiv` fails

## Architectural Direction: CLM-First Definitions

**Goal:** define graph operators natively as CLMs on `EuclideanSpace`, not as matrices. `walkCLM` and `meanCLM` are defined CLM-first (three-layer pattern: standalone function → `LinearMap` → CLM via `toContinuousLinearMap`). `spectralGap` is now `‖walkCLM - meanCLM‖`, the operator norm of the walk operator restricted to the orthogonal complement of constants.

No files have `#exit`. `expander_mixing_lemma` is fully proved via indicator vectors + Cauchy-Schwarz + operator norm. `ZigZag.lean` has 2 sorry's: `zigzag_spectral_bound` (assembly) and `explicit_expanders_exist_zigzag` (all-sizes interpolation). The `zigzag_spectral_bound` sorry has been decomposed into 16 smaller sublemmas across three new files: `ZigZagOperators.lean` (1 sorry: walk factorization), `ZigZagSpectral.lean` (12 sorry's: algebraic + spectral properties), and `RVWBound.lean` (3 sorry's: monotonicity + abstract operator bound). The mathematical core is `rvw_operator_norm_bound` in `RVWBound.lean` — a pure operator-theory result independent of graphs. Base expander is D=12 (20736 vertices, β ≤ 5/9); D=12 is minimal for the precise RVW bound to converge (β² < 1/3 + even parity). The next frontier is proving the easier sublemmas (algebraic properties).

## Proof Status by Difficulty

**Done:** `zero_one_principle`, `RegularGraph.square`, `RegularGraph.zigzag`, `completeGraph.rot_involution`, `spectralGap_nonneg`, `spectralGap_le_one`, `adjMatrix_square_eq_sq`, `spectralGap_square`, `spectralGap_complete`, `zigzagFamily`, `zigzagFamily_gap` (both cases), `expander_mixing_lemma`

**Achievable (weeks):** `halver_convergence`

**Achievable (weeks each):** The 16 sublemmas of `zigzag_spectral_bound`, decomposed as follows:
- *Easy (days):* `clusterMeanCLM_idempotent`, `clusterMeanCLM_isSelfAdjoint`, `stepPermCLM_sq_eq_one`, `withinCluster_comp_clusterMean`, `clusterMean_comp_withinCluster`, `meanCLM_eq_clusterMean_comp`, `clusterMean_comp_meanCLM`, `rvwBound_mono_left`, `rvwBound_mono_right`
- *Medium (1-2 weeks):* `withinClusterCLM_isSelfAdjoint`, `stepPermCLM_isSelfAdjoint`, `withinClusterCLM_norm_le_one`, `zigzag_walkCLM_eq`, `hat_block_norm`, `withinCluster_tilde_contraction`, assembly of `zigzag_spectral_bound`
- *Hard (2-4 weeks):* `rvw_operator_norm_bound` (mathematical core — Rayleigh quotient → 2×2 matrix eigenvalue)

**Substantial (months):** `halver_composition`, `expander_gives_halver`

**Engineering (weeks, fiddly):** replacing `baseExpander` axiom with a concrete verified graph, all-sizes interpolation in `explicit_expanders_exist_zigzag`

### Base expander certificate: open approaches

Replacing the `baseExpander` axioms requires certifying that a specific 12-regular graph on 20736 vertices has spectral gap ≤ 5/9. All known O(n)-data approaches are infeasible (see `Random.lean` header). Two ideas under investigation:

1. **Parallel dense LDL^T via sharded subfiles.** The LDL^T certificate is O(n²) data, but verification can be chopped into thousands of independent subfiles generated during the build and verified in parallel with `decide +kernel`. Each subfile checks a few rows of the factorization. Need to estimate: total data size, per-shard verification time, and whether Lean's build system can handle ~10K generated files.

2. **Eigenspace sparsity.** Random expanders might have high multiplicity in their second eigenvalue, allowing the eigenspace to be described with sparse data. If so, a certificate could consist of a few sparse eigenvectors + a spectral gap bound on the complement. Need numerical experiments on actual random 12-regular graphs to check eigenvalue multiplicities and eigenvector sparsity.
