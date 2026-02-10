# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Lean 4 formalization of the Ajtai–Komlós–Szemerédi (1983) O(n log n) sorting network construction. The project formalizes the proof architecture using the zig-zag product (Reingold–Vadhan–Wigderson 2002) as the route to explicit expander families, avoiding the heavy algebraic machinery (Margulis/LPS) that would require years of formalization effort.

Most theorems have `sorry` placeholders — this is intentional. The codebase is a structural skeleton demonstrating the complete proof architecture.

## Build Commands

```bash
lake build          # Build the project (first build downloads mathlib, takes a long time)
lake env printPaths # Show build paths
lake clean          # Clean build artifacts
```

There are no tests or linter configurations. Correctness is verified through Lean's type checker — if `lake build` succeeds, all type-checked proofs are valid.

## Architecture

**Entry point:** `AKS.lean` — imports both modules and states the top-level theorem `zigzag_implies_aks_network` connecting expander existence to sorting networks.

**Four modules with a bottom-up dependency:**

### `AKS/Fin.lean` — `Fin` Arithmetic Helpers
Reusable encode/decode lemmas for `Fin n × Fin d` ↔ `Fin (n * d)` product indexing: `Fin.pair_lt`, `fin_encode_fst`, `fin_encode_snd`, `fin_div_add_mod`.

### `AKS/Basic.lean` — Sorting Network Theory
Sections build on each other sequentially:
1. **Comparator networks** — `Comparator`, `ComparatorNetwork` (flat list of comparators), execution model
2. **0-1 principle** — reduces sorting correctness to Boolean inputs
3. **Expander graphs** — `BipartiteExpander`, spectral gap, existence
4. **ε-halvers** — approximate sorting via expanders (`IsEpsilonHalver`)
5. **AKS construction** — recursive build: split → recurse → merge with halvers
6. **Complexity analysis** — `IsBigO` notation, O(n log n) size
7. **Correctness** — `halver_composition` (geometric decrease), `AKS.sorts`

### `AKS/RegularGraph.lean` — Regular Graph Theory
General theory of d-regular graphs, independent of the zig-zag product:
1. **Regular graphs and adjacency matrices** — `RegularGraph` (rotation map representation), `adjMatrix`, symmetry proofs
2. **Spectral gap** — `spectralGap` via `IsHermitian.eigenvalues₀`, `spectralGap_nonneg`, `spectralGap_le_one`, `expander_mixing_lemma`
3. **Graph squaring** — `G.square`, `spectralGap_square`: λ(G²) = λ(G)²
4. **Complete graph** — `completeGraph`, `spectralGap_complete`: λ(K_{n+1}) = 1/n

### `AKS/ZigZag.lean` — Zig-Zag Product and Expander Families
Builds on `RegularGraph.lean` with the zig-zag product construction:
1. **Zig-zag product** — `G₁.zigzag G₂`, the three-step walk (zig-step-zag)
2. **Spectral composition theorem** — λ(G₁ ⓩ G₂) ≤ 1 - (1-λ₂)²(1-λ₁)/2
3. **Base case** — concrete small expander (axiomatized: `baseExpander`)
4. **Iterated construction** — `zigzagFamily`: square → zig-zag → repeat
5. **Main result** — `explicit_expanders_exist_zigzag`

### Data flow
```
Fin.lean → RegularGraph.lean → ZigZag.lean
                                    ↓ (provides expander families)
                              AKS.lean: zigzag_implies_aks_network
                                    ↑ (uses sorting network machinery)
                              Basic.lean: AKS construction + correctness
```

## Style

- Use `↦` (not `=>`) for lambda arrows: `fun x ↦ ...`
- In markdown/comments, backtick-quote Lean identifiers and filenames: `` `Fin` ``, not `Fin`; `` `ZigZag.lean` ``, not `ZigZag.lean`
- Use `/-! **Title** -/` for section headers, not numbered `§N.` or decorative `-- ═══` lines
- Keep mathematically high-level files (e.g., `ZigZag.lean`) clean by moving reusable helpers (e.g., `Fin` arithmetic lemmas) into their own files (e.g., `AKS/Fin.lean`). Iterate with helpers in the same file during development, then extract as a final pass before committing.

## Key Lean/Mathlib Conventions

- `autoImplicit` is **disabled** globally in `lakefile.lean` — do not add `set_option autoImplicit false` in individual files
- Depends on **Mathlib v4.27.0** — when updating, check import paths as they frequently change between versions (this has caused build breaks before)
- Lean toolchain: **v4.27.0** (pinned in `lean-toolchain`)

## Proof Workflow

Before attempting a `sorry`, estimate the probability of proving it directly (e.g., 30%, 50%, 80%) and report this. If the probability is below ~50%, first factor the `sorry` into intermediate lemmas — smaller steps that are each individually likely to succeed. This avoids wasting long build-test cycles on proofs that need restructuring.

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

**Triangle inequality for `|·|` via `dist_triangle`.** `abs_add` is hard to find. Instead, convert to the metric space API: `|μ| = ‖μ‖ = dist μ 0` (via `Real.norm_eq_abs`, `dist_zero_right` — no `Real.` prefix), then `dist_triangle μ c 0` gives `|μ| ≤ dist μ c + ‖c‖`. Use `Real.dist_eq` for `dist x y = |x - y|`.

**`↑(Finset.univ)` ≠ `Set.univ` in `MapsTo` proofs.** `card_eq_sum_card_fiberwise` needs `(s : Set ι).MapsTo f ↑t`. The coercion `↑(Finset.univ)` is `Finset.univ.toSet`, not `Set.univ`. Use `Finset.mem_coe.mpr (Finset.mem_univ _)` to prove `x ∈ ↑univ`.

**Matrix product entries via fiber decomposition.** To prove `adjMatrix G.square = (adjMatrix G) ^ 2`, reduce entry-wise to a Nat equality: `#{two-step walks u→v} = ∑_w #{edges u→w} × #{edges w→v}`. Use `Finset.card_eq_sum_card_fiberwise` to partition the LHS by intermediate vertex, then `Finset.card_nbij'` with div/mod encoding to biject each fiber with a product of filters. The `fin_encode_fst`/`fin_encode_snd`/`fin_div_add_mod` lemmas from `Fin.lean` handle the round-trip proofs. For the ℝ-level: `simp only [adjMatrix_apply, sq, Matrix.mul_apply, div_mul_div_comm]` + `rw [← Finset.sum_div, Nat.cast_mul]` + `congr 1` reduces to the Nat identity, then `exact_mod_cast key`.

**Connecting `eigenvalues₀` to `spectrum`.** To show `hA.eigenvalues₀ j ∈ spectrum ℝ A`: (1) `rw [hA.spectrum_real_eq_range_eigenvalues]`, (2) construct witness `⟨(Fintype.equivOfCardEq (Fintype.card_fin _)) j, proof⟩`, (3) prove equality with `unfold Matrix.IsHermitian.eigenvalues; simp [Equiv.symm_apply_apply]`. Key insight: `eigenvalues i = eigenvalues₀ (equiv.symm i)`, so `eigenvalues (equiv j) = eigenvalues₀ j`.

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

### Finset Counting
- `Finset.card_nbij'` takes `Set.MapsTo`/`Set.LeftInvOn`/`Set.RightInvOn` args
- `card_eq_sum_card_fiberwise` needs `Set.MapsTo` proof (see `↑univ` note above)

## Proof Status by Difficulty

**Done:** `zero_one_principle` (via `exec_comp_monotone` + threshold function contrapositive), `RegularGraph.square` and `RegularGraph.zigzag` (`Fin` encode/decode + `rot_involution` via extracted defs with projection-based simp lemmas), `completeGraph.rot_involution` (via Mathlib's `Fin.succAbove`/`Fin.predAbove` — reparameterized from `d, hd` to `n+1`), `spectralGap_le_one` (via Gershgorin's circle theorem: `eigenvalue_mem_ball` → row norm sum ≤ 1 → `|λ| ≤ 1`), `adjMatrix_square_eq_sq` (adjacency matrix of G² = (adjacency matrix of G)²; via fiber decomposition + `Finset.card_nbij'` bijection using div/mod encoding)

**Blocked on Mathlib:** `spectralGap_square` — `adjMatrix_square_eq_sq` is proved; remaining sorry is `eigenvalues₀_pow_sq` (eigenvalues of M² are squares of eigenvalues of M). Needs `ContinuousFunctionalCalculus` spectral mapping for `Matrix _ _ ℝ`, but Mathlib v4.27.0 lacks the required `CStarAlgebra` instance on real matrices. Alternatives: eigenvector basis argument via `apply_eigenvectorBasis` + uniqueness of eigenvalues, or upgrading to a Mathlib version with the CFC matrix instance.

**Achievable (weeks):** `spectralGap_complete`, `halver_convergence`

**Substantial (months):** `zigzag_spectral_bound` (core lemma — operator norm bound via orthogonal decomposition), `expander_mixing_lemma`, `halver_composition`, `expander_gives_halver`

**Engineering (weeks, fiddly):** replacing `baseExpander` axiom with a concrete verified graph, all-sizes interpolation in `explicit_expanders_exist_zigzag`
