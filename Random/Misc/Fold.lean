module

@[expose] public section
/-
  # Generic `Nat.fold` Algebra

  Reusable lemmas for `Nat.fold`-based sums and accumulators, extracted
  from `AKS/Cert/ScatterBridge.lean`. These cover congruence, splitting,
  shifting, distributivity, indicator evaluation, and involution invariance.
-/

/-! **Congruence** -/

/-- `Nat.fold` congruence for `acc + f(k)` steps over `Int`. -/
theorem fold_congr_acc (n : Nat) (a b : Nat → Int) (init : Int)
    (h : ∀ k, k < n → a k = b k) :
    Nat.fold n (fun k _ acc => acc + a k) init =
    Nat.fold n (fun k _ acc => acc + b k) init := by
  induction n with
  | zero => simp [Nat.fold_zero]
  | succ n ih =>
    rw [Nat.fold_succ, Nat.fold_succ, h n (by omega)]
    congr 1
    exact ih (fun k hk => h k (by omega))

/-- `Nat.fold` congruence for `acc + f(k)` steps over `Nat`. -/
theorem fold_congr_acc_nat (n : Nat) (f g : Nat → Nat)
    (h : ∀ k, k < n → f k = g k) :
    Nat.fold n (fun k _ acc => acc + f k) 0 =
    Nat.fold n (fun k _ acc => acc + g k) 0 := by
  induction n with
  | zero => simp [Nat.fold_zero]
  | succ n ih =>
    rw [Nat.fold_succ, Nat.fold_succ, h n (by omega)]
    congr 1; exact ih (fun k hk => h k (by omega))

/-- `Nat.fold` congruence for a general step function `f : Nat → α → α`. -/
theorem fold_congr_step (n : Nat) (f g : Nat → Int → Int) (init : Int)
    (h : ∀ k, k < n → ∀ acc, f k acc = g k acc) :
    Nat.fold n (fun k _ acc => f k acc) init =
    Nat.fold n (fun k _ acc => g k acc) init := by
  induction n with
  | zero => simp [Nat.fold_zero]
  | succ n ih =>
    rw [Nat.fold_succ, Nat.fold_succ, h n (by omega)]
    congr 1
    exact ih (fun k hk acc => h k (by omega) acc)

/-! **Zero terms and splitting** -/

/-- Fold where every step adds 0 is identity. -/
theorem fold_zero_terms (m : Nat) (init : Int) (f : Nat → Int)
    (hf : ∀ k, k < m → f k = 0) :
    Nat.fold m (fun k _ acc => acc + f k) init = init := by
  induction m with
  | zero => simp [Nat.fold_zero]
  | succ m ih =>
    rw [Nat.fold_succ, hf m (by omega), Int.add_zero]
    exact ih (fun k hk => hf k (by omega))

/-- Splitting `Nat.fold` at a cutpoint. -/
theorem fold_split_add (n m : Nat) (hm : m ≤ n) (f : Nat → Int → Int) (init : Int) :
    Nat.fold n (fun k _ acc => f k acc) init =
    Nat.fold (n - m) (fun k _ acc => f (m + k) acc)
      (Nat.fold m (fun k _ acc => f k acc) init) := by
  induction n with
  | zero =>
    have := Nat.le_zero.mp hm
    subst this; simp [Nat.fold_zero]
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hm with rfl | hlt
    · rw [Nat.sub_self, Nat.fold_zero]
    · have hm' : m ≤ n := Nat.lt_succ_iff.mp hlt
      rw [Nat.fold_succ, ih hm', show n + 1 - m = (n - m) + 1 from by omega,
          Nat.fold_succ, show m + (n - m) = n from by omega]

/-! **Additive structure** -/

/-- Fold distributes: sum of `(a + b)` = sum of `a` + sum of `b`. -/
theorem fold_add_distrib (m : Nat) (a b : Nat → Int) :
    Nat.fold m (fun v _ acc => acc + (a v + b v)) (0 : Int) =
    Nat.fold m (fun v _ acc => acc + a v) 0 +
    Nat.fold m (fun v _ acc => acc + b v) 0 := by
  induction m with
  | zero => simp [Nat.fold_zero]
  | succ m ih => simp only [Nat.fold_succ]; rw [ih]; omega

/-- Fold of indicator: `∑_{v<m} (if v = t then c else 0) = c` when `t < m`. -/
theorem fold_ite_eq (m t : Nat) (ht : t < m) (c : Int) :
    Nat.fold m (fun v _ acc => acc + if v = t then c else 0) (0 : Int) = c := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [Nat.fold_succ]
    by_cases h : m = t
    · subst h
      simp only [ite_true]
      rw [fold_zero_terms m 0 (fun v => if v = m then c else 0)
        (fun k hk => by simp [show k ≠ m from by omega])]
      omega
    · simp only [h, ite_false, Int.add_zero]
      exact ih (by omega)

/-! **Shifting and flattening** -/

/-- Shift the index range in a `Nat` fold sum. -/
theorem fold_shift_nat (m s : Nat) (f : Nat → Nat) :
    Nat.fold (s + m) (fun k _ acc => acc + f k) 0 =
    Nat.fold m (fun p _ acc => acc + f (s + p))
      (Nat.fold s (fun k _ acc => acc + f k) 0) := by
  induction m with
  | zero => simp [Nat.fold_zero, Nat.add_zero]
  | succ m ih =>
    rw [show s + (m + 1) = (s + m) + 1 from by omega, Nat.fold_succ, ih, Nat.fold_succ]

/-- Flatten a nested fold over `n` blocks of size `d` into a flat fold. -/
theorem fold_nested_to_flat_nat : ∀ (n d : Nat) (f : Nat → Nat),
    Nat.fold n (fun v _ acc_v =>
      Nat.fold d (fun p _ acc_p => acc_p + f (v * d + p)) acc_v) 0 =
    Nat.fold (n * d) (fun k _ acc => acc + f k) 0 := by
  intro n; induction n with
  | zero => intro d f; rw [Nat.zero_mul]; simp [Nat.fold_zero]
  | succ n ih =>
    intro d f; rw [Nat.fold_succ, ih d f, show (n + 1) * d = n * d + d from Nat.succ_mul n d]
    rw [fold_shift_nat d (n * d) f]

/-! **Involution invariance** -/

/-- Replacing one term in a `Nat` fold sum. -/
theorem fold_sum_replace (m : Nat) (f g : Nat → Nat) (j : Nat) (hj : j < m)
    (hrest : ∀ k, k < m → k ≠ j → f k = g k) :
    Nat.fold m (fun k _ acc => acc + f k) 0 + g j =
    Nat.fold m (fun k _ acc => acc + g k) 0 + f j := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [Nat.fold_succ, Nat.fold_succ]
    by_cases hjm : j = m
    · subst hjm
      have := fold_congr_acc_nat j f g (fun k hk => hrest k (by omega) (by omega)); omega
    · have := ih (by omega : j < m) (fun k hk hkj => hrest k (by omega) hkj)
      have := hrest m (by omega) (fun h => hjm h.symm); omega

/-- Involution preserves `Nat`-valued sums:
    `∑_{k<N} f(k) = ∑_{k<N} f(σ(k))` when `σ` is an involution on `{0,...,N-1}`. -/
theorem fold_sum_invol : ∀ (N : Nat) (σ : Nat → Nat) (f : Nat → Nat),
    (∀ k, k < N → σ k < N) →
    (∀ k, k < N → σ (σ k) = k) →
    Nat.fold N (fun k _ acc => acc + f k) 0 =
    Nat.fold N (fun k _ acc => acc + f (σ k)) 0 := by
  intro N; induction N with
  | zero => intros; simp [Nat.fold_zero]
  | succ N ih =>
    intro σ f hbound hinv
    rw [Nat.fold_succ, Nat.fold_succ]
    by_cases hfix : σ N = N
    · have hN_bound : ∀ k, k < N → σ k < N := by
        intro k hk
        have hsk := hbound k (by omega)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hsk with h | h
        · exact h
        · exfalso; have := hinv k (by omega); rw [h, hfix] at this; omega
      rw [hfix, ih σ f hN_bound (fun k hk => hinv k (by omega))]
    · have hj : σ N < N := by have := hbound N (by omega); omega
      have hσσN : σ (σ N) = N := hinv N (by omega)
      let σ2 : Nat → Nat := fun k => if k = σ N then σ N else σ k
      have hσ2_bound : ∀ k, k < N → σ2 k < N := by
        intro k hk; show (if k = σ N then σ N else σ k) < N
        split
        · exact hj
        · next hne =>
          have hsk := hbound k (by omega)
          rcases Nat.lt_succ_iff_lt_or_eq.mp hsk with h | h
          · exact h
          · exfalso; have := hinv k (by omega); rw [h] at this; exact hne this.symm
      have hσ2_inv : ∀ k, k < N → σ2 (σ2 k) = k := by
        intro k hk; show (if (if k = σ N then σ N else σ k) = σ N then σ N else
              σ (if k = σ N then σ N else σ k)) = k
        by_cases hkj : k = σ N
        · simp [hkj]
        · rw [if_neg hkj]; have : σ k ≠ σ N := by
            intro h; have := hinv k (by omega); rw [h, hσσN] at this; omega
          rw [if_neg this]; exact hinv k (by omega)
      have ih_val := ih σ2 f hσ2_bound hσ2_inv
      have hreplace := fold_sum_replace N (fun k => f (σ2 k)) (fun k => f (σ k)) (σ N) hj
        (fun k _ hkj => by show f (if k = σ N then σ N else σ k) = f (σ k); rw [if_neg hkj])
      dsimp only [] at hreplace
      have h1 : σ2 (σ N) = σ N := by
        show (if σ N = σ N then σ N else σ (σ N)) = σ N; rw [if_pos rfl]
      rw [h1, hσσN] at hreplace
      omega

end
