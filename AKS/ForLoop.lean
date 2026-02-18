/-
  # For-loop characterization lemmas

  Proves that `for k in [:n] do acc := f k acc` in the `Id` monad
  equals `Nat.fold`, enabling proof reasoning about imperative loops
  without fighting the `ForIn` desugaring.

  Also provides generic **partition-fold** lemmas: when a fold over a list
  is split into chunks processed independently, and results are merged with
  an operation compatible with the step function, the outcome equals folding
  over the concatenation. This is the core abstraction for parallel fold
  correctness proofs.

  Only imports `Init` — no Mathlib dependency.
-/

universe u v
variable {α : Type u} {β : Type v}

/-! **Helper: fold with index shift** -/

/-- Applying one step before a fold equals folding with shifted indices. -/
private theorem fold_shift (f : Nat → β → β) (init : β) (s n : Nat) :
    Nat.fold n (fun i _ acc => f (s + 1 + i) acc) (f s init) =
    f (s + n) (Nat.fold n (fun i _ acc => f (s + i) acc) init) := by
  induction n generalizing init with
  | zero => simp [Nat.fold_zero]
  | succ n ih =>
    rw [Nat.fold_succ, Nat.fold_succ, ih]
    congr 1; omega

/-! **`forIn` on `List.range'` equals `Nat.fold`** -/

/-- `forIn (List.range' s n) init (yield ∘ f)` in `Id` equals `Nat.fold`
    with offset `s`. -/
theorem forIn_range'_eq_fold (f : Nat → β → β) (init : β) (s n : Nat) :
    (forIn (List.range' s n) init (fun k r => ForInStep.yield (f k r)) : Id β) =
    Nat.fold n (fun i _ acc => f (s + i) acc) init := by
  induction n generalizing s init with
  | zero =>
    simp [List.range', List.forIn_nil, Nat.fold_zero]; rfl
  | succ n ih =>
    rw [List.range'_succ, List.forIn_cons, Nat.fold_succ]
    simp only [bind]
    rw [ih (f s init) (s + 1)]
    exact fold_shift f init s n

/-! **Main characterization theorem** -/

/-- `for k in [:n] do acc := f k acc` in `Id` equals `Nat.fold n (fun k _ acc => f k acc) init`.
    This bridges imperative for-loops over ranges with pure recursive folds. -/
theorem forIn_range_eq_fold (f : Nat → β → β) (init : β) (n : Nat) :
    (Id.run do
      let mut acc := init
      for k in [:n] do
        acc := f k acc
      return acc) = Nat.fold n (fun k _ acc => f k acc) init := by
  simp only [Id.run, bind, pure, Std.Range.forIn_eq_forIn_range', Std.Range.size, Nat.div_one]
  rw [forIn_range'_eq_fold]
  simp [Nat.zero_add]


/-! **Partition-fold equivalence** -/

/-- If `merge` distributes over `step`, then
    `merge a (foldl step b xs) = foldl step (merge a b) xs`.
    Core compatibility lemma for partitioned fold proofs. -/
theorem List.foldl_merge_compat
    (merge : α → α → α) (step : α → β → α)
    (hcompat : ∀ a b x, merge a (step b x) = step (merge a b) x)
    (xs : List β) (a b : α) :
    merge a (xs.foldl step b) = xs.foldl step (merge a b) := by
  induction xs generalizing b with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (step b x), hcompat a b x]

/-- `merge a (foldl step init xs) = foldl step a xs` when `merge a init = a`. -/
theorem List.foldl_merge_absorb
    (merge : α → α → α) (step : α → β → α) (init : α)
    (hcompat : ∀ a b x, merge a (step b x) = step (merge a b) x)
    (hid : ∀ a, merge a init = a)
    (xs : List β) (a : α) :
    merge a (xs.foldl step init) = xs.foldl step a := by
  rw [List.foldl_merge_compat merge step hcompat xs a init, hid]

/-- **Partition-fold theorem.** Processing chunks independently then merging
    gives the same result as folding over the concatenation.

    Requires: `merge a (step b x) = step (merge a b) x` (compatibility) and
    `merge a init = a` (right identity of `merge`). -/
theorem List.partition_foldl
    (merge : α → α → α) (step : α → β → α) (init : α)
    (hcompat : ∀ a b x, merge a (step b x) = step (merge a b) x)
    (hid : ∀ a, merge a init = a)
    (chunks : List (List β)) (a : α) :
    (chunks.map (fun chunk => chunk.foldl step init)).foldl merge a =
    chunks.flatten.foldl step a := by
  induction chunks generalizing a with
  | nil => simp
  | cons chunk rest ih =>
    simp only [List.map_cons, List.foldl_cons, List.flatten_cons, List.foldl_append]
    rw [List.foldl_merge_absorb merge step init hcompat hid chunk a]
    exact ih (chunk.foldl step a)
