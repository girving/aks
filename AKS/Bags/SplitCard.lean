/-
  # Cardinality Bounds for the Concrete Split

  Proves the cardinality hypotheses of `invariant_maintained` hold for
  the concrete split defined in `Split.lean` (Part B, Instance 1).

  Key results:
  - `concreteSplit_hkick`: parent kick ≤ 2λ·cap + 1
  - `concreteSplit_hsend_left`: left child ≤ cap/2
  - `concreteSplit_hsend_right`: right child ≤ cap/2
  - `concreteSplit_hkick_pair`: paired kick when cap < A (sorry)
  - `concreteSplit_hrebag_uniform`: uniform sizes after rebag (sorry)
  - `concreteSplit_hrebag_disjoint`: disjoint bags after rebag (sorry)
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

/-! **Harder Properties (Sorry)** -/

/-- `hkick_pair`: when `cap < A`, the paired kick from both children
    has no `+2` additive term. Requires even bag sizes at the child level. -/
theorem concreteSplit_hkick_pair {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hlam : 0 ≤ lam) (hperm : Function.Injective perm) :
    ∀ l i, bagCapacity n A ν t l < A →
      ((concreteSplit lam perm bags (l + 1) (2 * i)).toParent.card +
       (concreteSplit lam perm bags (l + 1) (2 * i + 1)).toParent.card : ℝ) ≤
      4 * lam * bagCapacity n A ν t (l + 1) := by
  sorry

/-- `hrebag_uniform`: all bags at a given level have equal size after rebagging. -/
theorem concreteSplit_hrebag_uniform {n : ℕ} {lam : ℝ}
    {perm : Fin n → Fin n} {bags : BagAssignment n} :
    ∀ level i₁ i₂,
      i₁ < 2 ^ level → i₂ < 2 ^ level →
      (rebag (concreteSplit lam perm bags) level i₁).card =
      (rebag (concreteSplit lam perm bags) level i₂).card := by
  sorry

/-- `hrebag_disjoint`: bags at distinct positions are disjoint after rebagging. -/
theorem concreteSplit_hrebag_disjoint {n : ℕ} {lam : ℝ}
    {perm : Fin n → Fin n} {bags : BagAssignment n} :
    ∀ l₁ l₂ i₁ i₂,
      (l₁, i₁) ≠ (l₂, i₂) →
      Disjoint (rebag (concreteSplit lam perm bags) l₁ i₁)
               (rebag (concreteSplit lam perm bags) l₂ i₂) := by
  sorry
