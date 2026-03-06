# Code Shrinking Guide

Techniques for reducing lines of code, build time, and `.olean` size simultaneously. Apply these during dedicated shrink passes or opportunistically while working on nearby code.

## Metrics

When evaluating a shrink change, measure:
1. **Lines of code** — `wc -l` on affected `.lean` files
2. **Build time** — `mcp__lean__check` wall time (warm) before and after
3. **olean size** — `stat --format=%s .lake/build/lib/lean/AKS/...olean` before and after

A change that improves all three is ideal. A change that improves one without regressing the others is still worth taking.

## Techniques

### 1. Extract pure-arithmetic helpers to standalone files

**What:** Move definitions and lemmas that depend only on `ℕ`, `ℚ`, or basic Mathlib into their own file with minimal imports.

**Why:** A file that imports `AKS.Bags.Network` (which pulls in `Finset`, `Placement`, etc.) takes longer to elaborate and produces a larger `.olean` than one importing only `Mathlib.Data.Nat.Cast.Order.Field`. When downstream files import both, the pure file's `.olean` is already cached and doesn't re-elaborate the heavy imports.

**Example:** `splitParentCard`/`splitChildCard` (pure `ℕ → ℕ → ℕ` with omega proofs) were extracted from `Sizes.lean` (1036 lines, imports `Network`) into `SplitCard.lean` (84 lines, imports only `Nat.Cast.Order.Field` + `Rat.Cast.Order`).

**Signs to look for:**
- Definitions using only `ℕ`, `ℤ`, `ℚ`, `ℝ` with no domain types (`Bag`, `Params`, `RegularGraph`, etc.)
- Lemmas proved entirely by `omega`, `ring`, `norm_num`, `field_simp`, `linarith`, `nlinarith`, `positivity`
- Groups of 5+ related lemmas about the same definition

### 2. Reduce import weight

**What:** Replace heavy imports with lighter ones when a file only needs a fraction of what the heavy import provides.

**Why:** Every `import` loads that module's entire `.olean` into the LSP server. Lighter imports = faster cold starts, smaller memory footprint, faster incremental checks.

**How to find lighter imports:**
- Check which Mathlib lemma you actually need: `#check @Nat.cast_div_le`
- Grep Mathlib for its home file: `rg 'cast_div_le' .lake/packages/mathlib/Mathlib/`
- Import that file instead of a heavier ancestor
- Verify with `mcp__lean__check` — if it compiles, the import is sufficient

**Caveat:** Don't split an import into 5 fine-grained ones to save one transitive dependency. The sweet spot is usually 1-2 targeted imports replacing one heavy one.

### 3. Factor large case-split proofs into helper lemmas

**What:** When `bagCard_le_capacity` has a 250-line proof with 6 nested `by_cases`, extract each case as a standalone lemma.

**Why:**
- Lean elaborates the entire proof term at once — one huge proof is slower than several small ones composed
- Each helper gets its own cache entry, so changing one case doesn't re-elaborate the others
- Smaller proofs are easier to optimize individually

**Rule of thumb:** If a `by` block exceeds ~40 lines, look for `by_cases`/`match`/`induction` branches that could be lemmas.

### 4. Replace verbose proofs with tighter tactic chains

**What:** Eliminate unnecessary intermediate `have` steps, redundant `simp` calls, and verbose `calc` blocks.

**Signs to look for:**
- `have h := ...; exact h` — just use the expression directly
- `simp only [X]; omega` where `omega` alone works (or `simp only [X]` alone closes it)
- `rw [A]; rw [B]; rw [C]` — use `rw [A, B, C]`
- `have h1 : ... := by omega; have h2 : ... := by omega; linarith` — often `omega` or `linarith` can close the whole thing
- Chained `push_cast; ring` after `field_simp` — try `field_simp; ring` directly

**Caution:** Don't sacrifice readability for 1-2 lines. A clear `calc` block that makes the mathematical argument visible is worth keeping, even if `nlinarith` could close the goal in one line. Tighten mechanical boilerplate, not mathematical structure.

**Preserve valuable comments.** Comments documenting proof strategy, mathematical reasoning, paper citations, or invariant explanations should not be removed during shrinking. Compress them if wordy, but keep the information. The `scripts/large` script reports non-comment lines specifically so that well-commented files aren't penalized. Only remove comments that are truly redundant (e.g., restating what the next line of code does).

### 5. Delete dead code

**What:** Remove lemmas, definitions, and `private` helpers that are no longer referenced.

**How to find them:**
- `rg 'lemma_name'` across the codebase — if only the definition site matches, it's dead
- After extracting helpers to a new file, check that the old file doesn't still have a copy
- Look for `private` lemmas that were superseded by a restructuring

### 6. Merge near-identical lemmas

**What:** When two lemmas differ only in a parameter (e.g., `large_cap_root_slack` vs `large_cap_interior_slack`), see if they can share a common core.

**Why:** Less code to maintain, smaller `.olean`, one cache entry instead of two.

**When NOT to merge:** When the two proofs have genuinely different mathematical content or when merging requires adding parameters that obscure the meaning.

### 7. Eliminate redundant specific-case proofs

**What:** When a file has both a general theorem and a specific-case version that the general one subsumes, delete the specific version and route callers through the general one.

**Why:** The specific version is pure dead weight — it duplicates the proof structure, adds lines, and requires parallel maintenance. This was the single biggest win in the `FromExpander.lean` refactor: `bipartite_epsilon_initial_halved` and `bipartite_epsilon_final_halved` (~280 lines combined) were specific-to-`expanderHalver` versions of `general_epsilon_initial_halved`/`general_epsilon_final_halved`. Deleting them and routing `expanderHalver_isEpsilonHalver` through `any_bipartite_isEpsilonHalver` saved 40% of the file.

**Signs to look for:**
- A `private lemma` whose proof mirrors a later `theorem` with slightly different hypotheses
- A concrete construction's property proof that manually inlines the same argument as a general version
- Helper lemmas (e.g., `edge_mono_neighborhood_subset`) used only by the specific version

### 8. Use Mathlib lemmas instead of hand-rolled ones

**What:** Before writing a helper, search Mathlib: `rg 'pattern' .lake/packages/mathlib/Mathlib/`.

**Why:** Mathlib lemmas come with `@[simp]` annotations, are already in the `.olean` cache, and compose with the rest of Mathlib. A hand-rolled duplicate adds lines and `.olean` weight.

**Common missed Mathlib lemmas:** `Finset.sum_ite_eq'`, `Nat.div_add_mod`, `Fin.succAbove`/`predAbove`, `Monotone.map_min`, `Finset.card_filter_le_iff`.

## Current hot spots

Files over 1000 lines (candidates for extraction):

| File | Lines | Notes |
|------|-------|-------|
| `Bags/SepBridge.lean` | 1339 | Separator-stranger bridge (extracted from Strange.lean) |
| `Bags/Source3.lean` | 966 | j=1 parent stranger bound (extracted from Strange.lean) |
| `Bags/Subtree.lean` | 968 | Subregs lemmas + subtree bound (extracted from Strange.lean) |
| `Bags/Strange.lean` | 377 | Base case + arithmetic + inductive step + main theorem (shrunk from 3840) |
| `MGG/Young.lean` | 670 | Diamond geometry (split from 1811; defs in `YoungDefs`, assembly in `YoungAssembly`) |
| `Separator/FromHalver.lean` | 776 | Halver-to-separator bridge (split from 1583; defs in `FromHalverDefs`) |
| `ZigZag/RVWBound.lean` | 1214 | RVW operator bound |
| `Bitonic/Correctness.lean` | 1103 | Bitonic sort correctness |
| `Halver/FromExpander.lean` | 636 | Expander-to-halver bridge (shrunk from 1075) |

## Workflow

1. Pick a file from the hot spots table (or any file > 500 lines)
2. Read it end-to-end, noting section boundaries
3. Identify pure-arithmetic or domain-independent lemma clusters
4. Extract to a new file with minimal imports
5. `mcp__lean__check` both old and new files
6. If the old file still exceeds the target, look for proof tightening opportunities
7. Record before/after metrics in the commit message
