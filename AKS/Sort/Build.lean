module
/-
  # Build Monad for Comparator Networks

  A writer monad that incrementally builds a `ComparatorNetwork` while
  computing a result. `Build n α` has a `.net` (accumulated comparators)
  and a `.value` (the result).

  Use `emit` to append comparators, and standard `do` notation to
  sequence build steps that return intermediate results (e.g., new bag
  assignments after a split stage).
-/

public import AKS.Sort.Defs

@[expose] public section


/-- Writer monad that accumulates a `ComparatorNetwork n` alongside a result. -/
@[ext] structure Build (n : ℕ) (α : Type) where
  net : ComparatorNetwork n
  value : α

instance {n : ℕ} : Monad (Build n) where
  pure a := ⟨⟨[]⟩, a⟩
  bind b f := let r := f b.value; ⟨⟨b.net.comparators ++ r.net.comparators⟩, r.value⟩

instance {n : ℕ} : LawfulMonad (Build n) where
  map_const := by intros; funext; apply Build.ext <;> simp [Functor.mapConst, Functor.map]
  id_map := by intros; apply Build.ext <;> simp [Functor.map, List.append_nil]
  seqLeft_eq := by intros; apply Build.ext <;> simp [SeqLeft.seqLeft, Seq.seq, Functor.map, List.append_nil]
  seqRight_eq := by intros; apply Build.ext <;> simp [SeqRight.seqRight, Seq.seq, Functor.map]
  pure_seq := by intros; apply Build.ext <;> simp [Seq.seq, Functor.map, Pure.pure]
  bind_pure_comp := by intros; apply Build.ext <;> simp [Functor.map, Bind.bind, Pure.pure, List.append_nil]
  bind_map := by intros; apply Build.ext <;> simp [Seq.seq, Functor.map, Bind.bind]
  pure_bind := by intros; apply Build.ext <;> simp [Bind.bind, Pure.pure]
  bind_assoc := by intros; apply Build.ext <;> simp [Bind.bind, List.append_assoc]

/-- Append a comparator network to the accumulator. -/
def Build.emit {n : ℕ} (net : ComparatorNetwork n) : Build n Unit :=
  ⟨net, ()⟩

/-- Append a single comparator. -/
def Build.compare {n : ℕ} (c : Comparator n) : Build n Unit :=
  Build.emit ⟨[c]⟩

/-! **Simp lemmas** -/

@[simp] theorem Build.net_pure {n : ℕ} {α : Type} (a : α) :
    (Pure.pure a : Build n α).net = ⟨[]⟩ := rfl

@[simp] theorem Build.value_pure {n : ℕ} {α : Type} (a : α) :
    (Pure.pure a : Build n α).value = a := rfl

@[simp] theorem Build.net_emit {n : ℕ} (net : ComparatorNetwork n) :
    (Build.emit net).net = net := rfl

@[simp] theorem Build.net_bind {n : ℕ} {α β : Type}
    (b : Build n α) (f : α → Build n β) :
    (b >>= f).net = ⟨b.net.comparators ++ (f b.value).net.comparators⟩ := rfl

@[simp] theorem Build.value_bind {n : ℕ} {α β : Type}
    (b : Build n α) (f : α → Build n β) :
    (b >>= f).value = (f b.value).value := rfl

/-! **Execution** -/

/-- Executing the network from a bind is sequential execution. -/
theorem Build.exec_bind {n : ℕ} {α β γ : Type} [LinearOrder γ]
    (b : Build n α) (f : α → Build n β) (v : Fin n → γ) :
    (b >>= f).net.exec v = (f b.value).net.exec (b.net.exec v) := by
  show (⟨b.net.comparators ++ (f b.value).net.comparators⟩ : ComparatorNetwork n).exec v = _
  exact ComparatorNetwork.exec_append b.net (f b.value).net v

theorem Build.exec_pure {n : ℕ} {α β : Type} [LinearOrder α]
    (a : β) (v : Fin n → α) :
    (Pure.pure a : Build n β).net.exec v = v := by
  show (⟨[]⟩ : ComparatorNetwork n).exec v = v
  simp [ComparatorNetwork.exec]

theorem Build.exec_emit {n : ℕ} {α : Type} [LinearOrder α]
    (net : ComparatorNetwork n) (v : Fin n → α) :
    (Build.emit net).net.exec v = net.exec v := rfl

end
