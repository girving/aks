module

@[expose] public section
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

/-! **`forIn` on `List` equals `List.foldl`** -/

/-- `forIn l init (yield ∘ f)` in `Id` equals `l.foldl f init`. -/
theorem list_forIn_yield_eq_foldl {α β : Type} (l : List α) (init : β) (f : β → α → β) :
    (forIn (m := Id) l init (fun x s => ForInStep.yield (f s x))) = l.foldl f init := by
  induction l generalizing init with
  | nil => simp only [forIn, ForIn.forIn, List.forIn'_nil, List.foldl, pure]
  | cons x xs ih =>
    simp only [forIn, ForIn.forIn, List.forIn'_cons, List.foldl, bind]
    exact ih (f init x)

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
  simp only [Id.run, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.div_one]
  rw [forIn_range'_eq_fold]
  simp [Nat.zero_add]


/-! **`forIn'` invariant and relational lemmas** -/

/-- Invariant preservation for `forIn'` with pure yield in `Id` monad.
    If `P` holds on `init` and every step preserves `P`, then `P` holds on
    the final result. -/
theorem List.forIn'_yield_preserves {α : Type} {β : Type}
    (P : β → Prop) :
    ∀ (l : List α) (init : β),
    P init →
    ∀ (f : (a : α) → a ∈ l → β → β),
    (∀ a (h : a ∈ l) b, P b → P (f a h b)) →
    P (forIn' (m := Id) l init (fun a h b => ForInStep.yield (f a h b))) := by
  intro l
  induction l with
  | nil => intro init hinit _ _; exact hinit
  | cons x xs ih =>
    intro init hinit f hstep
    simp only [List.forIn'_cons, bind]
    apply ih
    · exact hstep x List.mem_cons_self init hinit
    · intro a h b hp
      exact hstep a (List.mem_cons_of_mem x h) b hp

/-- Relational invariant for `forIn'` with pure yield in `Id` monad.
    Relates a `forIn'` loop to a plain `List.foldl`: if `R` holds on the initial
    states and every step preserves `R`, then `R` holds on the final states. -/
theorem List.forIn'_yield_rel {α : Type} {β γ : Type}
    (R : β → γ → Prop) :
    ∀ (l : List α) (initB : β) (initC : γ),
    R initB initC →
    ∀ (fB : (a : α) → a ∈ l → β → β)
      (fC : α → γ → γ),
    (∀ a (h : a ∈ l) b c, R b c → R (fB a h b) (fC a c)) →
    R (forIn' (m := Id) l initB (fun a h b => ForInStep.yield (fB a h b)))
      (l.foldl (fun c a => fC a c) initC) := by
  intro l
  induction l with
  | nil => intro _ _ hR _ _ _; exact hR
  | cons x xs ih =>
    intro initB initC hR fB fC hstep
    simp only [List.forIn'_cons, bind, List.foldl_cons]
    apply ih
    · exact hstep x List.mem_cons_self initB initC hR
    · intro a h b c hr
      exact hstep a (List.mem_cons_of_mem x h) b c hr

/-- `List.foldl` over `List.range' s n 1` equals `Nat.fold n` with offset `s`. -/
theorem List.foldl_range'_eq_fold (f : Nat → β → β) (init : β) (s n : Nat) :
    (List.range' s n 1).foldl (fun b a => f a b) init =
    Nat.fold n (fun j _ b => f (s + j) b) init := by
  induction n generalizing s init with
  | zero => simp [List.range', Nat.fold_zero]
  | succ m ih =>
    simp only [List.range'_succ, List.foldl_cons, Nat.fold_succ]
    rw [ih (f s init) (s + 1)]
    exact fold_shift f init s m


/-! **`forIn'` to `forIn` bridge for ranges** -/

/-- `forIn'` on a range equals `forIn` when the bodies agree pointwise
    (i.e., the `forIn'` body's value doesn't depend on the membership proof). -/
theorem range_forIn'_eq_forIn {β : Type} (n : Nat) (init : β)
    (f : (i : Nat) → i ∈ [:n] → β → Id (ForInStep β))
    (g : Nat → β → Id (ForInStep β))
    (h : ∀ i (hi : i ∈ [:n]) b, f i hi b = g i b) :
    forIn' (m := Id) [:n] init f = forIn (m := Id) [:n] init g := by
  show forIn' (m := Id) [:n] init f = forIn' (m := Id) [:n] init (fun a _ b => g a b)
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.forIn'_eq_forIn'_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  apply List.forIn'_congr rfl rfl
  intro a ha b
  have ha' : a ∈ [:n] := Std.Legacy.Range.mem_of_mem_range' (by
    simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] at ha ⊢; exact ha)
  exact h a ha' b

/-- Variant of `range_forIn'_eq_forIn` for 3-variable `MProd` accumulators
    with the `match` wrapper that converts `MProd` to `Prod`. -/
theorem range_forIn'_mprod_eq_forIn {n : Nat}
    {α β γ : Type} (init : MProd α (MProd β γ))
    (f : (i : Nat) → i ∈ [:n] → MProd α (MProd β γ) → Id (ForInStep (MProd α (MProd β γ))))
    (g : Nat → MProd α (MProd β γ) → Id (ForInStep (MProd α (MProd β γ))))
    (h : ∀ i (hi : i ∈ [:n]) b, f i hi b = g i b) :
    (match forIn' (m := Id) [:n] init f with | ⟨a, b, c⟩ => (a, b, c)) =
    (match forIn (m := Id) [:n] init g with | ⟨a, b, c⟩ => (a, b, c)) := by
  have := range_forIn'_eq_forIn n init f g h; rw [this]


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

end
