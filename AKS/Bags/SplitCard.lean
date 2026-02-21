/-
  # Cardinality Bounds for the Concrete Split

  Proves the cardinality hypotheses of `invariant_maintained` hold for
  the concrete split defined in `Split.lean` (Part B, Instance 1).

  Key results:
  - `concreteSplit_hkick`: parent kick ≤ 2λ·cap + 1
  - `concreteSplit_hsend_left`: left child ≤ cap/2
  - `concreteSplit_hsend_right`: right child ≤ cap/2
  - `concreteSplit_hkick_pair`: paired kick when cap < A (proved, modulo `bags_even_at_small_cap`)
  - `concreteSplit_hrebag_uniform`: uniform sizes after rebag (proved)
  - `concreteSplit_hrebag_disjoint`: disjoint bags after rebag (proved)
-/

import AKS.Bags.Split

open Finset

/-! **Injection Lemma for Rank-Based Filters** -/

/-- Items with rank in a range [a, b) number at most b - a,
    when `perm` is injective on `regs`. -/
theorem filter_rankInBag_Ico_card_le {n : ℕ} {perm : Fin n → Fin n}
    {regs : Finset (Fin n)} (hperm : Function.Injective perm) (a b : ℕ) :
    (regs.filter (fun i ↦
      a ≤ rankInBag perm regs i ∧ rankInBag perm regs i < b)).card ≤ b - a := by
  calc (regs.filter (fun i ↦ a ≤ rankInBag perm regs i ∧
        rankInBag perm regs i < b)).card
      ≤ (Finset.Ico a b).card := by
        apply card_le_card_of_injOn (fun i ↦ rankInBag perm regs i)
        · intro i hi
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hi
          exact mem_coe.mpr (Finset.mem_Ico.mpr hi.2)
        · exact (rankInBag_injOn hperm).mono (fun x hx ↦ by
            simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx; exact hx.1)
    _ = b - a := Nat.card_Ico a b

/-- Items with rank < k number at most k. -/
theorem filter_rankInBag_lt_card_le {n : ℕ} {perm : Fin n → Fin n}
    {regs : Finset (Fin n)} (hperm : Function.Injective perm) (k : ℕ) :
    (regs.filter (fun i ↦ rankInBag perm regs i < k)).card ≤ k := by
  have h := filter_rankInBag_Ico_card_le (regs := regs) hperm 0 k
  simp only [Nat.zero_le, true_and, tsub_zero] at h
  exact h

/-- Items with rank ≥ k number at most b - k. -/
theorem filter_rankInBag_ge_card_le {n : ℕ} {perm : Fin n → Fin n}
    {regs : Finset (Fin n)} (hperm : Function.Injective perm) (k : ℕ) :
    (regs.filter (fun i ↦ k ≤ rankInBag perm regs i)).card ≤
      regs.card - k := by
  calc (regs.filter (fun i ↦ k ≤ rankInBag perm regs i)).card
      ≤ (Finset.Ico k regs.card).card := by
        apply card_le_card_of_injOn (fun i ↦ rankInBag perm regs i)
        · intro i hi
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hi
          exact mem_coe.mpr (Finset.mem_Ico.mpr ⟨hi.2, rankInBag_lt_card hi.1⟩)
        · exact (rankInBag_injOn hperm).mono (fun x hx ↦ by
            simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx; exact hx.1)
    _ = regs.card - k := Nat.card_Ico k regs.card

/-! **Exact Rank Counts**

Since `rankInBag` is injective on `regs` and maps into `{0, ..., regs.card - 1}`,
it's a bijection. Combined with the upper bounds above, this gives exact counts:
exactly `k` items have rank < `k`. -/

/-- Exactly `k` items have rank < `k` (for `k ≤ regs.card`). -/
theorem filter_rankInBag_lt_card_exact {n : ℕ} {perm : Fin n → Fin n}
    {regs : Finset (Fin n)} (hperm : Function.Injective perm)
    {k : ℕ} (hk : k ≤ regs.card) :
    (regs.filter (fun i ↦ rankInBag perm regs i < k)).card = k := by
  -- Upper bound: ≤ k
  have hle := filter_rankInBag_lt_card_le hperm (regs := regs) k
  -- Lower bound via complement: regs = filter(< k) ∪ filter(≥ k)
  have hcomp : regs = regs.filter (fun i ↦ rankInBag perm regs i < k) ∪
      regs.filter (fun i ↦ k ≤ rankInBag perm regs i) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro hm; exact (Nat.lt_or_ge (rankInBag perm regs x) k).elim
        (fun h ↦ Or.inl ⟨hm, h⟩) (fun h ↦ Or.inr ⟨hm, h⟩)
    · rintro (⟨hm, _⟩ | ⟨hm, _⟩) <;> exact hm
  have hdisj : Disjoint (regs.filter (fun i ↦ rankInBag perm regs i < k))
      (regs.filter (fun i ↦ k ≤ rankInBag perm regs i)) := by
    simp only [Finset.disjoint_filter]; intro _ _ h1 h2; omega
  have hge_le := filter_rankInBag_ge_card_le hperm (regs := regs) k
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [← hcomp] at hcard
  omega

/-- Exactly `b - k` items have rank ≥ `k` (for `k ≤ regs.card`). -/
theorem filter_rankInBag_ge_card_exact {n : ℕ} {perm : Fin n → Fin n}
    {regs : Finset (Fin n)} (hperm : Function.Injective perm)
    {k : ℕ} (hk : k ≤ regs.card) :
    (regs.filter (fun i ↦ k ≤ rankInBag perm regs i)).card = regs.card - k := by
  have hcomp : regs = regs.filter (fun i ↦ rankInBag perm regs i < k) ∪
      regs.filter (fun i ↦ k ≤ rankInBag perm regs i) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro hm; exact (Nat.lt_or_ge (rankInBag perm regs x) k).elim
        (fun h ↦ Or.inl ⟨hm, h⟩) (fun h ↦ Or.inr ⟨hm, h⟩)
    · rintro (⟨hm, _⟩ | ⟨hm, _⟩) <;> exact hm
  have hdisj : Disjoint (regs.filter (fun i ↦ rankInBag perm regs i < k))
      (regs.filter (fun i ↦ k ≤ rankInBag perm regs i)) := by
    simp only [Finset.disjoint_filter]; intro _ _ h1 h2; omega
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [← hcomp, filter_rankInBag_lt_card_exact hperm hk] at hcard
  omega

/-- Exactly `b - a` items have rank in `[a, b)` (for `a ≤ b ≤ regs.card`). -/
theorem filter_rankInBag_Ico_card_exact {n : ℕ} {perm : Fin n → Fin n}
    {regs : Finset (Fin n)} (hperm : Function.Injective perm)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ regs.card) :
    (regs.filter (fun i ↦ a ≤ rankInBag perm regs i ∧
      rankInBag perm regs i < b)).card = b - a := by
  -- [0, b) = [0, a) ∪ [a, b), disjoint union
  have hunion : regs.filter (fun i ↦ rankInBag perm regs i < b) =
      regs.filter (fun i ↦ rankInBag perm regs i < a) ∪
      regs.filter (fun i ↦ a ≤ rankInBag perm regs i ∧ rankInBag perm regs i < b) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hm, hlt⟩; exact (Nat.lt_or_ge (rankInBag perm regs x) a).elim
        (fun h ↦ Or.inl ⟨hm, h⟩) (fun h ↦ Or.inr ⟨hm, h, hlt⟩)
    · rintro (⟨hm, _⟩ | ⟨hm, _, _⟩) <;> exact ⟨hm, by omega⟩
  have hdisj : Disjoint
      (regs.filter (fun i ↦ rankInBag perm regs i < a))
      (regs.filter (fun i ↦ a ≤ rankInBag perm regs i ∧ rankInBag perm regs i < b)) := by
    simp only [Finset.disjoint_filter]; intro _ _ h1 h2; omega
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [← hunion, filter_rankInBag_lt_card_exact hperm hb,
      filter_rankInBag_lt_card_exact hperm (hab.trans hb)] at hcard
  omega

/-! **Deterministic Component Sizes**

For `concreteSplit`, the component sizes are deterministic given the bag size:
- `toParent.card = b - 2 * childSendSize lam b`
- `toLeftChild.card = childSendSize lam b` (non-leaf)
- `toRightChild.card = childSendSize lam b` (non-leaf)
This follows from `rankInBag` being a bijection. -/

/-- `fringeSize lam b + 2 * childSendSize lam b ≤ b` (requires `lam ≤ 1`). -/
theorem fringeSize_add_two_childSendSize_le {lam : ℝ} (b : ℕ) (hlam : lam ≤ 1) :
    fringeSize lam b + 2 * childSendSize lam b ≤ b := by
  have hfb : fringeSize lam b ≤ b := by
    simp only [fringeSize]
    have hbb : (0 : ℝ) ≤ ↑b := Nat.cast_nonneg b
    calc ⌊lam * ↑b⌋₊ ≤ ⌊(↑b : ℝ)⌋₊ :=
          Nat.floor_mono (le_trans (mul_le_mul_of_nonneg_right hlam hbb) (one_mul _).le)
      _ = b := Nat.floor_natCast b
  simp only [childSendSize]; omega

/-- The toParent component has exactly `b - 2 * childSendSize` items. -/
theorem concreteSplit_toParent_card_eq {n : ℕ} {perm : Fin n → Fin n}
    {regs : Finset (Fin n)} (hperm : Function.Injective perm) {lam : ℝ}
    (hlam : lam ≤ 1) :
    (regs.filter (fun i ↦
      rankInBag perm regs i < fringeSize lam regs.card ∨
      fringeSize lam regs.card + 2 * childSendSize lam regs.card ≤
        rankInBag perm regs i)).card =
    regs.card - 2 * childSendSize lam regs.card := by
  set b := regs.card
  set f := fringeSize lam b
  set h := childSendSize lam b
  -- toParent = filter(< f) ∪ filter(≥ f + 2h), disjoint
  have hunion : regs.filter (fun i ↦ rankInBag perm regs i < f ∨
      f + 2 * h ≤ rankInBag perm regs i) =
      regs.filter (fun i ↦ rankInBag perm regs i < f) ∪
      regs.filter (fun i ↦ f + 2 * h ≤ rankInBag perm regs i) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_union]; tauto
  have hdisj : Disjoint (regs.filter (fun i ↦ rankInBag perm regs i < f))
      (regs.filter (fun i ↦ f + 2 * h ≤ rankInBag perm regs i)) := by
    simp only [Finset.disjoint_filter]; intro _ _ h1 h2; omega
  rw [hunion, Finset.card_union_of_disjoint hdisj]
  have hfb : f + 2 * h ≤ b := fringeSize_add_two_childSendSize_le b hlam
  rw [filter_rankInBag_lt_card_exact hperm (by omega : f ≤ b),
      filter_rankInBag_ge_card_exact hperm hfb]
  omega

/-- The toLeftChild component has exactly `childSendSize` items (non-leaf). -/
theorem concreteSplit_toLeftChild_card_eq {n : ℕ} {perm : Fin n → Fin n}
    {regs : Finset (Fin n)} (hperm : Function.Injective perm) {lam : ℝ}
    (hlam : lam ≤ 1) :
    (regs.filter (fun i ↦
      fringeSize lam regs.card ≤ rankInBag perm regs i ∧
      rankInBag perm regs i < fringeSize lam regs.card +
        childSendSize lam regs.card)).card =
    childSendSize lam regs.card := by
  set f := fringeSize lam regs.card
  set h := childSendSize lam regs.card
  have hfb : f + 2 * h ≤ regs.card := fringeSize_add_two_childSendSize_le regs.card hlam
  have hfh : f + h ≤ regs.card := by omega
  have := filter_rankInBag_Ico_card_exact hperm (a := f) (b := f + h) (by omega) hfh
  omega

/-- The toRightChild component has exactly `childSendSize` items (non-leaf). -/
theorem concreteSplit_toRightChild_card_eq {n : ℕ} {perm : Fin n → Fin n}
    {regs : Finset (Fin n)} (hperm : Function.Injective perm) {lam : ℝ}
    (hlam : lam ≤ 1) :
    (regs.filter (fun i ↦
      fringeSize lam regs.card + childSendSize lam regs.card ≤
        rankInBag perm regs i ∧
      rankInBag perm regs i < fringeSize lam regs.card +
        2 * childSendSize lam regs.card)).card =
    childSendSize lam regs.card := by
  set f := fringeSize lam regs.card
  set h := childSendSize lam regs.card
  have hfb : f + 2 * h ≤ regs.card := fringeSize_add_two_childSendSize_le regs.card hlam
  have := filter_rankInBag_Ico_card_exact hperm (a := f + h) (b := f + 2 * h) (by omega) hfb
  omega

/-! **Cardinality Bounds in Terms of Bag Size** -/

/-- The toParent component has at most `2 * fringeSize + 1` items. -/
theorem concreteSplit_toParent_card_le {n : ℕ} (lam : ℝ)
    (perm : Fin n → Fin n) (bags : BagAssignment n)
    (hperm : Function.Injective perm) (level idx : ℕ) :
    (concreteSplit lam perm bags level idx).toParent.card ≤
      2 * fringeSize lam (bags level idx).card + 1 := by
  simp only [concreteSplit]
  set regs := bags level idx with regs_def
  set b := regs.card with b_def
  set f := fringeSize lam b with f_def
  set h := childSendSize lam b with h_def
  -- Union bound: filter(P ∨ Q) ≤ filter(P) + filter(¬P ∧ Q) ≤ filter(P) + filter(Q)
  have hunion : (regs.filter (fun i ↦
      rankInBag perm regs i < f ∨ f + 2 * h ≤ rankInBag perm regs i)).card ≤
      (regs.filter (fun i ↦ rankInBag perm regs i < f)).card +
      (regs.filter (fun i ↦ f + 2 * h ≤ rankInBag perm regs i)).card := by
    calc _ ≤ ((regs.filter (fun i ↦ rankInBag perm regs i < f)) ∪
        (regs.filter (fun i ↦ f + 2 * h ≤ rankInBag perm regs i))).card := by
          apply card_le_card
          intro x hx
          simp only [mem_filter, mem_union] at hx ⊢
          rcases hx.2 with h1 | h2
          · exact Or.inl ⟨hx.1, h1⟩
          · exact Or.inr ⟨hx.1, h2⟩
      _ ≤ _ := card_union_le _ _
  have hlt := filter_rankInBag_lt_card_le hperm (regs := regs) f
  have hge := filter_rankInBag_ge_card_le hperm (regs := regs) (f + 2 * h)
  -- b - (f + 2h) + f ≤ 2f + 1 because b - 2*(b/2) ≤ 1
  have harith : f + (b - (f + 2 * h)) ≤ 2 * f + 1 := by
    simp only [h_def, childSendSize]; omega
  linarith

/-- The toLeftChild component has at most `childSendSize` items. -/
theorem concreteSplit_toLeftChild_card_le {n : ℕ} (lam : ℝ)
    (perm : Fin n → Fin n) (bags : BagAssignment n)
    (hperm : Function.Injective perm) (level idx : ℕ) :
    (concreteSplit lam perm bags level idx).toLeftChild.card ≤
      childSendSize lam (bags level idx).card := by
  simp only [concreteSplit]
  split_ifs with hl
  · exact Nat.zero_le _
  · set regs := bags level idx
    set f := fringeSize lam regs.card
    set h := childSendSize lam regs.card
    calc (regs.filter (fun i ↦ f ≤ rankInBag perm regs i ∧
          rankInBag perm regs i < f + h)).card
        ≤ (f + h) - f := filter_rankInBag_Ico_card_le hperm f (f + h)
      _ = h := Nat.add_sub_cancel_left f h

/-- The toRightChild component has at most `childSendSize` items. -/
theorem concreteSplit_toRightChild_card_le {n : ℕ} (lam : ℝ)
    (perm : Fin n → Fin n) (bags : BagAssignment n)
    (hperm : Function.Injective perm) (level idx : ℕ) :
    (concreteSplit lam perm bags level idx).toRightChild.card ≤
      childSendSize lam (bags level idx).card := by
  simp only [concreteSplit]
  split_ifs with hl
  · exact Nat.zero_le _
  · set regs := bags level idx
    set f := fringeSize lam regs.card
    set h := childSendSize lam regs.card
    calc (regs.filter (fun i ↦ f + h ≤ rankInBag perm regs i ∧
          rankInBag perm regs i < f + 2 * h)).card
        ≤ (f + 2 * h) - (f + h) := filter_rankInBag_Ico_card_le hperm (f + h) (f + 2 * h)
      _ = h := by omega

/-! **Arithmetic Lemmas for Floor Bounds** -/

/-- `fringeSize lam b ≤ lam * b` (floor bound). -/
theorem fringeSize_le_mul {lam : ℝ} {b : ℕ} (hlam : 0 ≤ lam) :
    (fringeSize lam b : ℝ) ≤ lam * ↑b := by
  simp only [fringeSize]
  exact Nat.floor_le (mul_nonneg hlam (Nat.cast_nonneg b))

/-- `childSendSize lam b ≤ b / 2` (as reals). -/
theorem childSendSize_le_half {lam : ℝ} {b : ℕ} :
    (childSendSize lam b : ℝ) ≤ ↑b / 2 := by
  simp only [childSendSize]
  calc (↑(b / 2 - fringeSize lam b) : ℝ)
      ≤ ↑(b / 2) := by exact_mod_cast Nat.sub_le _ _
    _ ≤ ↑b / 2 := Nat.cast_div_le

/-! **Bridge to `bagCapacity` (Using Invariant)** -/

/-- `hkick`: parent kick bounded by `2 * lam * bagCapacity + 1`. -/
theorem concreteSplit_hkick {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hlam : 0 ≤ lam) (hperm : Function.Injective perm) :
    ∀ l i, ((concreteSplit lam perm bags l i).toParent.card : ℝ) ≤
      2 * lam * bagCapacity n A ν t l + 1 := by
  intro l i
  have hcard := concreteSplit_toParent_card_le lam perm bags hperm l i
  have hf := fringeSize_le_mul hlam (b := (bags l i).card)
  have hcap := inv.capacity_bound l i
  calc ((concreteSplit lam perm bags l i).toParent.card : ℝ)
      ≤ ↑(2 * fringeSize lam (bags l i).card + 1) := by exact_mod_cast hcard
    _ = 2 * ↑(fringeSize lam (bags l i).card) + 1 := by push_cast; ring
    _ ≤ 2 * (lam * ↑(bags l i).card) + 1 := by linarith
    _ ≤ 2 * (lam * bagCapacity n A ν t l) + 1 := by
        have : lam * ↑(bags l i).card ≤ lam * bagCapacity n A ν t l :=
          mul_le_mul_of_nonneg_left hcap hlam
        linarith
    _ = 2 * lam * bagCapacity n A ν t l + 1 := by ring

/-- `hsend_left`: left child bounded by `bagCapacity / 2`. -/
theorem concreteSplit_hsend_left {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hperm : Function.Injective perm) :
    ∀ l i, ((concreteSplit lam perm bags l i).toLeftChild.card : ℝ) ≤
      bagCapacity n A ν t l / 2 := by
  intro l i
  have hcard := concreteSplit_toLeftChild_card_le lam perm bags hperm l i
  have hh := @childSendSize_le_half lam (bags l i).card
  have hcap := inv.capacity_bound l i
  calc ((concreteSplit lam perm bags l i).toLeftChild.card : ℝ)
      ≤ ↑(childSendSize lam (bags l i).card) := by exact_mod_cast hcard
    _ ≤ ↑(bags l i).card / 2 := hh
    _ ≤ bagCapacity n A ν t l / 2 := by linarith

/-- `hsend_right`: right child bounded by `bagCapacity / 2`. -/
theorem concreteSplit_hsend_right {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hperm : Function.Injective perm) :
    ∀ l i, ((concreteSplit lam perm bags l i).toRightChild.card : ℝ) ≤
      bagCapacity n A ν t l / 2 := by
  intro l i
  have hcard := concreteSplit_toRightChild_card_le lam perm bags hperm l i
  have hh := @childSendSize_le_half lam (bags l i).card
  have hcap := inv.capacity_bound l i
  calc ((concreteSplit lam perm bags l i).toRightChild.card : ℝ)
      ≤ ↑(childSendSize lam (bags l i).card) := by exact_mod_cast hcard
    _ ≤ ↑(bags l i).card / 2 := hh
    _ ≤ bagCapacity n A ν t l / 2 := by linarith

/-! **Harder Properties** -/

/-- When `bagCapacity n A ν t l < A`, bags at level `l+1` have even size.
    Extracted directly from `SeifInvariant.small_cap_even`. -/
private theorem bags_even_at_small_cap {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (_ : 1 < A) {l : ℕ}
    (hcap : bagCapacity n A ν t l < A) :
    ∀ idx, Even (bags (l + 1) idx).card :=
  fun idx ↦ inv.small_cap_even l idx hcap

/-- When `b` is even and `lam ≤ 1/2`: `b - 2 * childSendSize lam b = 2 * fringeSize lam b`.
    The rounding error in `b / 2` vanishes because `b` is even. -/
private theorem toParent_card_even {lam : ℝ} {b : ℕ}
    (heven : Even b) (hlam_half : lam ≤ 1/2) (_ : 0 ≤ lam) :
    b - 2 * childSendSize lam b = 2 * fringeSize lam b := by
  obtain ⟨m, rfl⟩ := heven
  simp only [childSendSize, fringeSize]
  have h1 : (m + m) / 2 = m := by omega
  have h2 : ⌊lam * ↑(m + m)⌋₊ ≤ m := by
    have : lam * (↑(m + m) : ℝ) ≤ ↑m := by
      have hmm : (↑(m + m) : ℝ) = ↑m + ↑m := by push_cast; ring
      have hm : (0 : ℝ) ≤ ↑m := Nat.cast_nonneg m
      nlinarith
    calc ⌊lam * ↑(m + m)⌋₊ ≤ ⌊(↑m : ℝ)⌋₊ := Nat.floor_mono this
      _ = m := Nat.floor_natCast m
  rw [h1]; omega

/-- `hkick_pair`: when `cap < A`, the paired kick from both children
    has no `+2` additive term. Requires even bag sizes at the child level
    (from `bags_even_at_small_cap`). -/
theorem concreteSplit_hkick_pair {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hA : 1 < A) (hlam : 0 ≤ lam) (hlam_half : lam ≤ 1/2)
    (hperm : Function.Injective perm) :
    ∀ l i, bagCapacity n A ν t l < A →
      ((concreteSplit lam perm bags (l + 1) (2 * i)).toParent.card +
       (concreteSplit lam perm bags (l + 1) (2 * i + 1)).toParent.card : ℝ) ≤
      4 * lam * bagCapacity n A ν t (l + 1) := by
  intro l i hcap
  -- Get even-size from sorry'd lemma
  have heven_left := bags_even_at_small_cap inv hA hcap (2 * i)
  have heven_right := bags_even_at_small_cap inv hA hcap (2 * i + 1)
  -- Exact toParent cards: card = b - 2 * childSendSize
  have hlam1 : lam ≤ 1 := by linarith
  have htp_l : (concreteSplit lam perm bags (l + 1) (2 * i)).toParent.card =
      (bags (l + 1) (2 * i)).card - 2 * childSendSize lam (bags (l + 1) (2 * i)).card := by
    show (bags (l + 1) (2 * i) |>.filter _).card = _
    exact concreteSplit_toParent_card_eq hperm hlam1
  have htp_r : (concreteSplit lam perm bags (l + 1) (2 * i + 1)).toParent.card =
      (bags (l + 1) (2 * i + 1)).card - 2 * childSendSize lam (bags (l + 1) (2 * i + 1)).card := by
    show (bags (l + 1) (2 * i + 1) |>.filter _).card = _
    exact concreteSplit_toParent_card_eq hperm hlam1
  -- Rewrite using even-size to eliminate rounding
  have hev_l := toParent_card_even heven_left hlam_half hlam
  have hev_r := toParent_card_even heven_right hlam_half hlam
  rw [htp_l, hev_l, htp_r, hev_r]
  -- Now goal: (2 * fringeSize_l + 2 * fringeSize_r : ℝ) ≤ 4 * lam * cap(l+1)
  -- Both bags at level l+1 have uniform size
  set b_l := (bags (l + 1) (2 * i)).card
  set b_r := (bags (l + 1) (2 * i + 1)).card
  have hf_l := fringeSize_le_mul hlam (b := b_l)
  have hf_r := fringeSize_le_mul hlam (b := b_r)
  have hcap_l := inv.capacity_bound (l + 1) (2 * i)
  have hcap_r := inv.capacity_bound (l + 1) (2 * i + 1)
  push_cast
  calc (2 * (fringeSize lam b_l : ℝ) + 2 * (fringeSize lam b_r : ℝ))
      ≤ 2 * (lam * ↑b_l) + 2 * (lam * ↑b_r) := by linarith
    _ ≤ 2 * (lam * bagCapacity n A ν t (l + 1)) +
        2 * (lam * bagCapacity n A ν t (l + 1)) := by
        have : lam * ↑b_l ≤ lam * bagCapacity n A ν t (l + 1) :=
          mul_le_mul_of_nonneg_left hcap_l hlam
        have : lam * ↑b_r ≤ lam * bagCapacity n A ν t (l + 1) :=
          mul_le_mul_of_nonneg_left hcap_r hlam
        linarith
    _ = 4 * lam * bagCapacity n A ν t (l + 1) := by ring

/-- Three sources of `rebag` are pairwise disjoint: kicked items from left child,
    kicked items from right child, and items from parent all come from different bags. -/
theorem rebag_sources_disjoint {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (level idx : ℕ) :
    let split := concreteSplit lam perm bags
    Disjoint ((split (level + 1) (2 * idx)).toParent)
             ((split (level + 1) (2 * idx + 1)).toParent) ∧
    Disjoint ((split (level + 1) (2 * idx)).toParent)
             (fromParent split level idx) ∧
    Disjoint ((split (level + 1) (2 * idx + 1)).toParent)
             (fromParent split level idx) := by
  set split := concreteSplit lam perm bags
  have hsub := concreteSplit_hsplit_sub lam perm bags
  -- Left and right children are different bags at level+1
  refine ⟨?_, ?_, ?_⟩
  · exact (inv.bags_disjoint (level + 1) (level + 1) (2 * idx) (2 * idx + 1)
      (by simp only [ne_eq, Prod.mk.injEq]; omega)).mono (hsub _ _).1 (hsub _ _).1
  · -- Left child at level+1 vs parent at level-1
    unfold fromParent
    split_ifs with h₁ h₂
    · exact disjoint_empty_right _
    · exact (inv.bags_disjoint (level + 1) (level - 1) (2 * idx) (idx / 2)
        (by simp only [ne_eq, Prod.mk.injEq]; omega)).mono (hsub _ _).1 (hsub _ _).2.1
    · exact (inv.bags_disjoint (level + 1) (level - 1) (2 * idx) (idx / 2)
        (by simp only [ne_eq, Prod.mk.injEq]; omega)).mono (hsub _ _).1 (hsub _ _).2.2
  · -- Right child at level+1 vs parent at level-1
    unfold fromParent
    split_ifs with h₁ h₂
    · exact disjoint_empty_right _
    · exact (inv.bags_disjoint (level + 1) (level - 1) (2 * idx + 1) (idx / 2)
        (by simp only [ne_eq, Prod.mk.injEq]; omega)).mono (hsub _ _).1 (hsub _ _).2.1
    · exact (inv.bags_disjoint (level + 1) (level - 1) (2 * idx + 1) (idx / 2)
        (by simp only [ne_eq, Prod.mk.injEq]; omega)).mono (hsub _ _).1 (hsub _ _).2.2

/-- Card of `rebag` equals sum of three component cards (exact, using disjointness). -/
theorem rebag_card_eq {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (level idx : ℕ) :
    (rebag (concreteSplit lam perm bags) level idx).card =
      (concreteSplit lam perm bags (level + 1) (2 * idx)).toParent.card +
      (concreteSplit lam perm bags (level + 1) (2 * idx + 1)).toParent.card +
      (fromParent (concreteSplit lam perm bags) level idx).card := by
  unfold rebag
  have ⟨h1, h2, h3⟩ := rebag_sources_disjoint inv level idx
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨h2, h3⟩)]
  rw [Finset.card_union_of_disjoint h1]

/-- `fromParent` cards are uniform: two indices at the same level with same parent
    bag size have equal `fromParent` card. -/
private theorem fromParent_card_uniform {n : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (hperm : Function.Injective perm)
    {lam : ℝ} (hlam : lam ≤ 1) {level : ℕ} {i₁ i₂ : ℕ}
    (hunif : (bags (level - 1) (i₁ / 2)).card = (bags (level - 1) (i₂ / 2)).card) :
    (fromParent (concreteSplit lam perm bags) level i₁).card =
    (fromParent (concreteSplit lam perm bags) level i₂).card := by
  by_cases h0 : level = 0
  · simp [fromParent, h0]
  · -- Helper: card = 0 at leaf parent, childSendSize otherwise
    suffices h : ∀ i, (fromParent (concreteSplit lam perm bags) level i).card =
        if maxLevel n ≤ level - 1 then 0
        else childSendSize lam (bags (level - 1) (i / 2)).card by
      rw [h i₁, h i₂]; split_ifs with _ <;> [rfl; rw [hunif]]
    intro i; unfold fromParent; rw [if_neg h0]
    -- Split on parity first (using by_cases to avoid split_ifs touching RHS if)
    by_cases h_even : i % 2 = 0
    · -- Even: toLeftChild
      rw [if_pos h_even]
      by_cases hl : maxLevel n ≤ level - 1
      · -- Leaf parent: toLeftChild = ∅
        simp only [concreteSplit, if_pos hl, Finset.card_empty]
      · -- Non-leaf parent: card = childSendSize
        simp only [concreteSplit, if_neg hl]
        exact concreteSplit_toLeftChild_card_eq hperm hlam
    · -- Odd: toRightChild
      rw [if_neg h_even]
      by_cases hl : maxLevel n ≤ level - 1
      · simp only [concreteSplit, if_pos hl, Finset.card_empty]
      · simp only [concreteSplit, if_neg hl]
        exact concreteSplit_toRightChild_card_eq hperm hlam

/-- `toParent` card depends only on the bag size. -/
private theorem toParent_card_eq {n : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (hperm : Function.Injective perm)
    {lam : ℝ} (hlam : lam ≤ 1) (level idx : ℕ) :
    (concreteSplit lam perm bags level idx).toParent.card =
    (bags level idx).card - 2 * childSendSize lam (bags level idx).card := by
  show (bags level idx |>.filter _).card = _
  exact concreteSplit_toParent_card_eq hperm hlam

/-- `hrebag_uniform`: all bags at a given level have equal size after rebagging.
    Follows from: component sizes are deterministic given bag size, and all bags
    at each level have uniform size (by invariant). -/
theorem concreteSplit_hrebag_uniform {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hperm : Function.Injective perm) (hlam : lam ≤ 1) :
    ∀ level i₁ i₂,
      i₁ < 2 ^ level → i₂ < 2 ^ level →
      (rebag (concreteSplit lam perm bags) level i₁).card =
      (rebag (concreteSplit lam perm bags) level i₂).card := by
  intro level i₁ i₂ hi₁ hi₂
  -- Express rebag card as sum of three deterministic component cards
  rw [rebag_card_eq inv level i₁, rebag_card_eq inv level i₂]
  -- toParent cards at level+1 depend only on bags.card at level+1
  have htp₁ := toParent_card_eq (bags := bags) hperm hlam (level + 1) (2 * i₁)
  have htp₂ := toParent_card_eq (bags := bags) hperm hlam (level + 1) (2 * i₂)
  have htp₃ := toParent_card_eq (bags := bags) hperm hlam (level + 1) (2 * i₁ + 1)
  have htp₄ := toParent_card_eq (bags := bags) hperm hlam (level + 1) (2 * i₂ + 1)
  -- All bags at level+1 have the same size
  have hu₁ := inv.uniform_size (level + 1) (2 * i₁) (2 * i₂)
    (by omega) (by omega)
  have hu₂ := inv.uniform_size (level + 1) (2 * i₁ + 1) (2 * i₂ + 1)
    (by omega) (by omega)
  rw [htp₁, htp₂, hu₁, htp₃, htp₄, hu₂]
  -- fromParent cards are uniform (uses parent uniform_size)
  suffices hfp : (fromParent (concreteSplit lam perm bags) level i₁).card =
      (fromParent (concreteSplit lam perm bags) level i₂).card by omega
  by_cases h0 : level = 0
  · simp [fromParent, h0]
  · have hpow : 2 ^ level = 2 * 2 ^ (level - 1) := by
      conv_lhs => rw [show level = level - 1 + 1 from by omega, pow_succ]
      rw [Nat.mul_comm]
    exact fromParent_card_uniform hperm hlam
      (inv.uniform_size (level - 1) (i₁ / 2) (i₂ / 2) (by omega) (by omega))

/-- Split components of a single bag are pairwise disjoint (rank ranges don't overlap). -/
private theorem concreteSplit_components_disjoint {n : ℕ} (lam : ℝ)
    (perm : Fin n → Fin n) (bags : BagAssignment n) (level idx : ℕ) :
    let s := concreteSplit lam perm bags level idx
    Disjoint s.toParent s.toLeftChild ∧
    Disjoint s.toParent s.toRightChild ∧
    Disjoint s.toLeftChild s.toRightChild := by
  simp only [concreteSplit]
  refine ⟨?_, ?_, ?_⟩ <;> {
    split_ifs <;> first
    | exact Finset.disjoint_empty_right _
    | exact Finset.disjoint_empty_left _
    | exact disjoint_bot_right
    | (rw [Finset.disjoint_left]; intro x hx₁ hx₂
       simp only [Finset.mem_filter] at hx₁ hx₂; omega) }

/-- `hrebag_disjoint`: bags at distinct positions are disjoint after rebagging. -/
theorem concreteSplit_hrebag_disjoint {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags) :
    ∀ l₁ l₂ i₁ i₂,
      (l₁, i₁) ≠ (l₂, i₂) →
      Disjoint (rebag (concreteSplit lam perm bags) l₁ i₁)
               (rebag (concreteSplit lam perm bags) l₂ i₂) := by
  intro l₁ l₂ i₁ i₂ hne
  simp only [ne_eq, Prod.mk.injEq, not_and_or] at hne
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  set split := concreteSplit lam perm bags with split_def
  unfold rebag at hx₁ hx₂
  simp only [Finset.mem_union] at hx₁ hx₂
  have hsub := concreteSplit_hsplit_sub lam perm bags
  have hcomp := concreteSplit_components_disjoint lam perm bags
  -- Helper: items in fromParent are in the parent bag
  have fromP_sub : ∀ l i, fromParent split l i ⊆ bags (l - 1) (i / 2) := by
    intro l i
    unfold fromParent; rw [split_def]
    split_ifs with h1 h2
    · exact Finset.empty_subset _
    · exact (hsub _ _).2.1
    · exact (hsub _ _).2.2
  -- x is in some original bag from each rebag source
  -- Source bags for rebag(l, i): bags(l+1, 2i), bags(l+1, 2i+1), bags(l-1, i/2)
  have src₁ : ∀ {l i}, x ∈ (split (l+1) (2*i)).toParent → x ∈ bags (l+1) (2*i) :=
    fun h ↦ (hsub _ _).1 h
  have src₂ : ∀ {l i}, x ∈ (split (l+1) (2*i+1)).toParent → x ∈ bags (l+1) (2*i+1) :=
    fun h ↦ (hsub _ _).1 h
  have src₃ : ∀ {l i}, x ∈ fromParent split l i → x ∈ bags (l-1) (i/2) :=
    fun h ↦ fromP_sub _ _ h
  -- For disjoint original bags: contradiction
  have bag_contra : ∀ {L₁ I₁ L₂ I₂}, (L₁, I₁) ≠ (L₂, I₂) →
      x ∈ bags L₁ I₁ → x ∈ bags L₂ I₂ → False := by
    intro L₁ I₁ L₂ I₂ hne hm₁ hm₂
    exact Finset.disjoint_left.mp (inv.bags_disjoint L₁ L₂ I₁ I₂ hne) hm₁ hm₂
  -- For same bag, different components: contradiction
  have comp_contra_PL : ∀ l i, x ∈ (split l i).toParent →
      x ∈ (split l i).toLeftChild → False := fun l i h1 h2 ↦
    Finset.disjoint_left.mp (hcomp l i).1 h1 h2
  have comp_contra_PR : ∀ l i, x ∈ (split l i).toParent →
      x ∈ (split l i).toRightChild → False := fun l i h1 h2 ↦
    Finset.disjoint_left.mp (hcomp l i).2.1 h1 h2
  have comp_contra_LR : ∀ l i, x ∈ (split l i).toLeftChild →
      x ∈ (split l i).toRightChild → False := fun l i h1 h2 ↦
    Finset.disjoint_left.mp (hcomp l i).2.2 h1 h2
  -- fromParent is a specific component of the parent split
  have fromP_comp : ∀ l i, x ∈ fromParent split l i →
      (l ≠ 0 ∧ i % 2 = 0 ∧ x ∈ (split (l-1) (i/2)).toLeftChild) ∨
      (l ≠ 0 ∧ i % 2 ≠ 0 ∧ x ∈ (split (l-1) (i/2)).toRightChild) := by
    intro l i hm; unfold fromParent at hm; rw [split_def] at hm
    split_ifs at hm with h1 h2
    · exact absurd hm (Finset.notMem_empty _)
    · exact Or.inl ⟨h1, h2, hm⟩
    · exact Or.inr ⟨h1, h2, hm⟩
  -- 9 cases
  rcases hx₁ with (hx₁ | hx₁) | hx₁ <;> rcases hx₂ with (hx₂ | hx₂) | hx₂
  -- Case 1: toParent(l₁+1,2i₁) vs toParent(l₂+1,2i₂) — always different bags
  · exact bag_contra (by simp only [ne_eq, Prod.mk.injEq]; omega) (src₁ hx₁) (src₁ hx₂)
  -- Case 2: toParent(l₁+1,2i₁) vs toParent(l₂+1,2i₂+1) — always different bags
  · exact bag_contra (by simp only [ne_eq, Prod.mk.injEq]; omega) (src₁ hx₁) (src₂ hx₂)
  -- Case 3: toParent(l₁+1,2i₁) vs fromParent(l₂,i₂) — cross-level
  · rcases fromP_comp l₂ i₂ hx₂ with ⟨hl₂, hev, hcomp₂⟩ | ⟨hl₂, hod, hcomp₂⟩
    · by_cases heq : (l₁ + 1, 2 * i₁) = (l₂ - 1, i₂ / 2)
      · rw [Prod.mk.injEq] at heq
        rw [← heq.1, ← heq.2] at hcomp₂; exact comp_contra_PL _ _ hx₁ hcomp₂
      · exact bag_contra heq (src₁ hx₁) ((hsub _ _).2.1 hcomp₂)
    · by_cases heq : (l₁ + 1, 2 * i₁) = (l₂ - 1, i₂ / 2)
      · rw [Prod.mk.injEq] at heq
        rw [← heq.1, ← heq.2] at hcomp₂; exact comp_contra_PR _ _ hx₁ hcomp₂
      · exact bag_contra heq (src₁ hx₁) ((hsub _ _).2.2 hcomp₂)
  -- Case 4: toParent(l₁+1,2i₁+1) vs toParent(l₂+1,2i₂) — always different bags
  · exact bag_contra (by simp only [ne_eq, Prod.mk.injEq]; omega) (src₂ hx₁) (src₁ hx₂)
  -- Case 5: toParent(l₁+1,2i₁+1) vs toParent(l₂+1,2i₂+1) — always different bags
  · exact bag_contra (by simp only [ne_eq, Prod.mk.injEq]; omega) (src₂ hx₁) (src₂ hx₂)
  -- Case 6: toParent(l₁+1,2i₁+1) vs fromParent(l₂,i₂) — cross-level
  · rcases fromP_comp l₂ i₂ hx₂ with ⟨hl₂, hev, hcomp₂⟩ | ⟨hl₂, hod, hcomp₂⟩
    · by_cases heq : (l₁ + 1, 2 * i₁ + 1) = (l₂ - 1, i₂ / 2)
      · rw [Prod.mk.injEq] at heq
        rw [← heq.1, ← heq.2] at hcomp₂; exact comp_contra_PL _ _ hx₁ hcomp₂
      · exact bag_contra heq (src₂ hx₁) ((hsub _ _).2.1 hcomp₂)
    · by_cases heq : (l₁ + 1, 2 * i₁ + 1) = (l₂ - 1, i₂ / 2)
      · rw [Prod.mk.injEq] at heq
        rw [← heq.1, ← heq.2] at hcomp₂; exact comp_contra_PR _ _ hx₁ hcomp₂
      · exact bag_contra heq (src₂ hx₁) ((hsub _ _).2.2 hcomp₂)
  -- Case 7: fromParent(l₁,i₁) vs toParent(l₂+1,2i₂) — symmetric to Case 3
  · rcases fromP_comp l₁ i₁ hx₁ with ⟨hl₁, hev, hcomp₁⟩ | ⟨hl₁, hod, hcomp₁⟩
    · by_cases heq : (l₁ - 1, i₁ / 2) = (l₂ + 1, 2 * i₂)
      · rw [Prod.mk.injEq] at heq
        rw [heq.1, heq.2] at hcomp₁; exact comp_contra_PL _ _ hx₂ hcomp₁
      · exact bag_contra heq ((hsub _ _).2.1 hcomp₁) (src₁ hx₂)
    · by_cases heq : (l₁ - 1, i₁ / 2) = (l₂ + 1, 2 * i₂)
      · rw [Prod.mk.injEq] at heq
        rw [heq.1, heq.2] at hcomp₁; exact comp_contra_PR _ _ hx₂ hcomp₁
      · exact bag_contra heq ((hsub _ _).2.2 hcomp₁) (src₁ hx₂)
  -- Case 8: fromParent(l₁,i₁) vs toParent(l₂+1,2i₂+1) — symmetric to Case 6
  · rcases fromP_comp l₁ i₁ hx₁ with ⟨hl₁, hev, hcomp₁⟩ | ⟨hl₁, hod, hcomp₁⟩
    · by_cases heq : (l₁ - 1, i₁ / 2) = (l₂ + 1, 2 * i₂ + 1)
      · rw [Prod.mk.injEq] at heq
        rw [heq.1, heq.2] at hcomp₁; exact comp_contra_PL _ _ hx₂ hcomp₁
      · exact bag_contra heq ((hsub _ _).2.1 hcomp₁) (src₂ hx₂)
    · by_cases heq : (l₁ - 1, i₁ / 2) = (l₂ + 1, 2 * i₂ + 1)
      · rw [Prod.mk.injEq] at heq
        rw [heq.1, heq.2] at hcomp₁; exact comp_contra_PR _ _ hx₂ hcomp₁
      · exact bag_contra heq ((hsub _ _).2.2 hcomp₁) (src₂ hx₂)
  -- Case 9: fromParent(l₁,i₁) vs fromParent(l₂,i₂)
  · rcases fromP_comp l₁ i₁ hx₁ with ⟨hl₁, hev₁, hc₁⟩ | ⟨hl₁, hod₁, hc₁⟩ <;>
    rcases fromP_comp l₂ i₂ hx₂ with ⟨hl₂, hev₂, hc₂⟩ | ⟨hl₂, hod₂, hc₂⟩
    · -- Both even: both toLeftChild — same (l-1, i/2) forces (l,i) equal
      by_cases heq : (l₁ - 1, i₁ / 2) = (l₂ - 1, i₂ / 2)
      · rw [Prod.mk.injEq] at heq
        exact hne.elim (by omega) (by omega)
      · exact bag_contra heq ((hsub _ _).2.1 hc₁) ((hsub _ _).2.1 hc₂)
    · -- l₁ even, l₂ odd: toLeftChild vs toRightChild
      by_cases heq : (l₁ - 1, i₁ / 2) = (l₂ - 1, i₂ / 2)
      · rw [Prod.mk.injEq] at heq; rw [heq.1, heq.2] at hc₁
        exact comp_contra_LR _ _ hc₁ hc₂
      · exact bag_contra heq ((hsub _ _).2.1 hc₁) ((hsub _ _).2.2 hc₂)
    · -- l₁ odd, l₂ even: toRightChild vs toLeftChild
      by_cases heq : (l₁ - 1, i₁ / 2) = (l₂ - 1, i₂ / 2)
      · rw [Prod.mk.injEq] at heq; rw [heq.1, heq.2] at hc₁
        exact comp_contra_LR _ _ hc₂ hc₁
      · exact bag_contra heq ((hsub _ _).2.2 hc₁) ((hsub _ _).2.1 hc₂)
    · -- Both odd: both toRightChild
      by_cases heq : (l₁ - 1, i₁ / 2) = (l₂ - 1, i₂ / 2)
      · rw [Prod.mk.injEq] at heq
        -- l₁-1=l₂-1 → l₁=l₂ (since both ≠ 0), i₁/2=i₂/2, both odd → i₁=i₂ → contradiction
        exact hne.elim (by omega) (by omega)
      · exact bag_contra heq ((hsub _ _).2.2 hc₁) ((hsub _ _).2.2 hc₂)

