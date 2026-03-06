# Proof Cleanup Patterns

Recurring cleanup opportunities found across the codebase, especially in
`AKS/Cert/`. Each section describes a pattern, gives examples, and suggests
the target location for shared infrastructure.

---

## 1. Replace hand-rolled helpers with Mathlib lemmas

**Pattern:** A private lemma re-proves something Mathlib already provides,
sometimes with a slightly different signature (e.g., using a concrete default
instead of `Inhabited.default`).

**Examples found (already fixed):**

| Custom lemma | Mathlib replacement | Files |
|---|---|---|
| `bang_eq_getD_int`, `bang_eq_getD_nat` | `Array.getElem!_eq_getD` | ScatterBridge, FusedBridge |
| `getElem!_eq_getD_int`, `getElem!_eq_getD_nat` | `Array.getElem!_eq_getD` | ScatterBridge |

**Gotcha:** `Array.getElem!_eq_getD` rewrites `arr[k]!` to `arr.getD k default`,
not `arr.getD k 0`. Since `(default : Nat) = 0` and `(default : Int) = 0` are
only *definitionally* equal (not syntactically), `simp only` leaves the
`default` unreduced. Fix with `simp only [Array.getElem!_eq_getD]; rfl` or use
`change ... .getD k 0 = _; exact ...` when chaining with downstream lemmas.

**Import caveat:** Mathlib has `List.foldl_ext` (in `Mathlib.Data.List.Basic`)
which is a stronger version of ScatterBridge's `foldl_congr_fun`. However,
`Mathlib.Data.List.Basic` isn't transitively imported by the Cert/ files and
adding a Mathlib import for a 6-line lemma isn't worthwhile. Always verify a
Mathlib lemma is actually reachable from the file's import chain before
proposing a replacement.

**How to find more:** `rg 'private.*getD|private.*getElem' AKS/` and cross-check
against Mathlib's `Array` namespace.

---

## 2. Dead private lemmas

**Pattern:** A `private` lemma is defined but never referenced — not even
implicitly via `simp`. These accumulate during development when proof strategies
change but the abandoned helpers aren't cleaned up.

**Detection:** For each `private` declaration, grep for its name within the same
file. If it appears only at the definition site, it's dead. Exception:
`@[simp]`-tagged lemmas can fire implicitly, so verify no `simp` call could
match the LHS pattern.

**Examples found (already removed):**

| Lemma | File | Notes |
|---|---|---|
| `epsMaxCol_nonneg` | Bridge.lean | Never called |
| `seqFold_eq_pure` | ColumnNormBridge.lean | 56-line theorem, never used |
| `list_forIn_fin_yield_eq_foldl` | ColumnNormBridge.lean | Specialized variant, unused |
| `merge_first_true` | ColumnNormBridge.lean | Subsumed by `merge_first_gen` |
| `foldl_mprod_swap` | FusedBridge.lean | 19-line lemma, never applied |
| `portCount_zero` | ScatterBridge.lean | `@[simp] private` but never triggered |

**Prevention:** Before committing, run
`rg 'private (theorem|lemma|def)' <file>` and verify each name appears
elsewhere in the file.

---

## 3. Duplicate private lemmas across files

**Pattern:** Two files each define a `private` copy of the same lemma (same
statement, same proof). This happens when files are developed independently.
Fix by making one copy public and deleting the other.

**Rule of thumb:** If file A imports file B, make the lemma public in B and
delete A's copy.

**Examples found (already fixed):**

| Lemma | File A | File B | Resolution |
|---|---|---|---|
| `list_forIn_yield_foldl` / `list_forIn_yield_eq_foldl` | FusedBridge | ColumnNormBridge | Made public in ColumnNormBridge |
| `epsMaxVal_nonneg` | Bridge | ColumnNormBridge | Made public in ColumnNormBridge |
| `bang_eq_getD_int` | FusedBridge | ScatterBridge | Replaced both with Mathlib |

**How to find more:** Extract all private theorem names, sort, and look for
near-duplicates:
```bash
rg 'private (theorem|lemma|def) (\w+)' AKS/Cert/ -or --no-filename | \
  sed 's/.*private \(theorem\|lemma\|def\) //' | sed 's/ .*//' | sort | uniq -d
```

---

## 4. Extract generic `Nat.fold` algebra to `AKS/Misc/Fold.lean`

**Pattern:** `Nat.fold`-based proofs accumulate congruence, splitting, shifting,
and distributivity lemmas as `private` helpers. These are fully generic — they
don't depend on domain-specific types — so they belong in a shared module.

**Completed:** Extracted 11 lemmas from ScatterBridge into `AKS/Misc/Fold.lean`
(~190 lines), removing ~180 lines from ScatterBridge:

| Lemma | Purpose |
|---|---|
| `fold_congr_acc` | Congruence for `acc + f(k)` steps over `Int` |
| `fold_congr_acc_nat` | Congruence for `acc + f(k)` steps over `Nat` |
| `fold_congr_step` | Congruence for general `f k acc` step functions |
| `fold_zero_terms` | Fold adding all zeros is identity |
| `fold_split_add` | Split fold at a cutpoint |
| `fold_add_distrib` | Sum of `(a+b)` = sum of `a` + sum of `b` |
| `fold_ite_eq` | Indicator sum `∑(if v=t then c else 0) = c` |
| `fold_shift_nat` | Shift index range in a `Nat` sum |
| `fold_nested_to_flat_nat` | Flatten nested fold into flat fold |
| `fold_sum_replace` | Replace one term in a sum |
| `fold_sum_invol` | Involution preserves sums |

**Remaining minor duplication:** ColumnNormBridge still has `fold_sum_congr`
(public, `{d}` implicit, `init = 0`) which overlaps with `fold_congr_acc`
(explicit `n`, general `init`). The implicit `{d}` makes call sites cleaner
(`apply fold_sum_congr` vs `apply fold_congr_acc _ _ _ 0`), so it's kept for
now.

---

## 5. Array builder fold specifications

**Pattern:** Building an array via `Nat.fold` with `setIfInBounds` requires
three companion lemmas: size preservation, element retrieval (in-range), and
default retrieval (out-of-range). These form a reusable template.

**Current inventory:**

| Lemma set | File | Builder pattern |
|---|---|---|
| `fold_set_size`, `fold_set_getElem?`, `fold_set_getD` | ColumnNormBridge | `Nat.fold m (fun i _ a => a.setIfInBounds i (g i)) init` |
| `foldl_preserves_size` | ScatterBridge | `List.foldl f init` where `f` preserves `.size` |
| `getD_set!_eq` | ScatterBridge | `(arr.set! i v).getD j 0` case-split |

**Proposed:** Extract the `fold_set_*` triple to `AKS/Misc/Fold.lean` (or a new
`AKS/Misc/Array.lean`). They're fully generic over the builder function `g`.
`foldl_preserves_size` and `getD_set!_eq` are also generic.

---

## 6. `forIn` ↔ `foldl` bridging

**Pattern:** Imperative Lean loops (`forIn`, `for ... in ...`) desugar to
`List.forIn'` or `Std.Range.forIn`. Proofs bridge these to `List.foldl` or
`Nat.fold` for reasoning. The core bridge is:

```lean
forIn (m := Id) l init (fun x s => ForInStep.yield (f s x)) = l.foldl f init
```

**Current status (all in `AKS/Misc/ForLoop.lean`):**
- `list_forIn_yield_eq_foldl` — List-based forIn → foldl
- `forIn_range_eq_fold`, `forIn_range'_eq_fold` — range-based for → `Nat.fold`
- `List.forIn'_yield_preserves`, `List.forIn'_yield_rel` — invariant/relational
- `List.foldl_range'_eq_fold` — foldl over `range'` → `Nat.fold`

---

## 7. Involution-based counting symmetry

**Pattern (ScatterBridge-specific):** Proving `portCount(v,w) = portCount(w,v)`
via a rotation involution. The proof strategy is:
1. Flatten nested folds to a single flat fold over `{0, ..., n*d-1}`
2. Apply `fold_sum_invol`: involution preserves sums
3. Show the involution swaps the `v`/`w` roles

The supporting lemmas form a coherent chain:
- `portCount_as_sum` → `portCount_eq_flat_count` (flatten)
- `fold_nested_to_flat_nat` (nested → flat fold)
- `fold_sum_invol` (involution lemma, ~45 lines)
- `nested_extract_block` (extract one block from nested fold)

**Status:** `fold_sum_invol` (and its helper `fold_sum_replace`) extracted to
`AKS/Misc/Fold.lean`. The rest (`portCount_as_sum`, `portCount_eq_flat_count`,
`nested_extract_block`) remain in ScatterBridge as domain-specific helpers.

---

## 8. `@[simp] private` is usually wrong

**Pattern:** A `@[simp]` lemma that's also `private` can only fire within its
own file. If no `simp` call in that file could match the LHS, the `@[simp]` tag
is wasted. Worse, it clutters the local simp set.

**Example found:** `portCount_zero` — `@[simp] private`, but `portCount` was
never called with literal `0` as the `d` argument. Deleted.

**Rule:** If a simp lemma is `private`, verify it actually fires somewhere. If
not, either delete it or remove `@[simp]` and call it explicitly.

---

## 9. Replace trivial hand-rolled lemmas with Mathlib

**Pattern:** Small private lemmas that re-prove facts Mathlib already knows,
just with a different proof or slightly different framing.

**Examples found:**

| Custom lemma | Mathlib replacement | File |
|---|---|---|
| `size_set!` (3-line proof) | `Array.size_setIfInBounds` (direct) | ColumnNormBridge |
| `getElem!_eq_getElem` | `simp [h]` (where `h : i < a.size`) | ColumnNormBridge |

**Note:** `Array.set!` is definitionally `Array.setIfInBounds`, so
`Array.size_setIfInBounds` closes `(a.set! i v).size = a.size` directly.

---

## 10. Cross-file duplicate: `mul_add_lt` / `mul_add_lt_mul`

**Pattern:** Both Bridge.lean (line 673) and ScatterBridge.lean (line 377)
have private one-liners proving `a * d + b < n * d` from `a < n` and `b < d`.
Same arithmetic, different names and variable names.

**Assessment:** Low priority — both are 2-3 line proofs, and the files don't
import each other. `AKS/Misc/Fin.lean` already has `Fin.pair_lt` which proves
the same thing but takes `Fin` arguments. Adding a `Nat`-level version there
would require both files to import it, which may not be worth it.

---

## Proposed remaining shared infrastructure

### `AKS/Misc/Fold.lean` — done

See pattern 4 above. All generic `Nat.fold` algebra extracted.

### `AKS/Misc/ForLoop.lean` — done

`list_forIn_yield_eq_foldl` moved from ColumnNormBridge to ForLoop.lean where
the other `forIn` bridges live.

### Possible: `AKS/Misc/Array.lean` (new file, low priority)

| Lemma | Source | Notes |
|---|---|---|
| `foldl_preserves_size` | ScatterBridge | Generic but single-file use |
| `getD_set!_eq` | ScatterBridge | Generic but single-file use |
| `fold_set_size`, `fold_set_getElem?`, `fold_set_getD` | ColumnNormBridge | Already public, used by FusedBridge |

These are all single-use or already properly shared. Extracting them would save
no duplication — it would just change where they live. Not recommended unless
a new consumer appears.

---

## Methodology: how to run a cleanup pass

Lessons from the Cert/ cleanup that apply to future cleanup passes on other
subsystems.

### Extraction workflow

1. **Classify** each private lemma as generic or domain-specific. Generic = no
   domain types in the signature (just `Nat`, `Int`, `Array`, `List`, etc.).
2. **Name consistently** when extracting. Rename to match the shared module's
   conventions (e.g., `fold_sum_congr_nat` → `fold_congr_acc_nat`). Update all
   call sites.
3. **Check the import DAG** before moving. The target file must be transitively
   imported by all consumers. Use `import` lines at file tops.
4. **Verify incrementally**: `mcp__lean__check` on the extracted file first, then each
   consumer.

### Gotchas discovered

- **Removing `@[simp] private` can break `simp` calls.** Even if the lemma
  looks unused, `simp` may rely on it implicitly. When deleting, check each
  `simp` call in the file — if one breaks, replace with `rfl` or explicit
  `rw`/`simp only`.
- **Definitional equality ≠ syntactic equality.** `(default : Int) = 0` and
  `Array.set! = Array.setIfInBounds` are definitional but not syntactic. After
  `simp only [Array.getElem!_eq_getD]`, the goal shows `default` not `0`.
  Close with `rfl` (which checks definitional equality) or `change`.
- **`Nat.fold` signature has a proof argument.** The step function is
  `(i : Nat) → i < n → α → α`, not `Nat → Unit → α → α`. When writing
  generic fold lemmas, use `fun k _ acc => ...` to bind the proof as `_`.
- **Don't extract single-use helpers.** Moving a private lemma from file A to
  `AKS/Misc/` when only file A uses it adds indirection with no benefit. Only
  extract when there are (or will be) multiple consumers.
