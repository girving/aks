module
/-
  # Displaced Count Monotonicity for Comparator Networks

  A comparator network can only decrease the "displaced count" — the number
  of small values at high positions (or large values at low positions).
  This is a key structural property used in the separator correctness proof.

  Main results:
  • `exec_displaced_le`: small values at high positions can only decrease
  • `exec_displaced_final_le`: large values at low positions can only decrease
-/

public import AKS.Sort.Defs

@[expose] public section


open Finset BigOperators

/-! **Comparator helpers** -/

/-- When `w(c.i) ≤ w(c.j)`, the comparator is identity. -/
lemma Comparator.apply_eq_of_le {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (w : Fin n → α) (h : w c.i ≤ w c.j) :
    c.apply w = w := by
  ext pos; unfold Comparator.apply
  by_cases hpi : pos = c.i
  · rw [if_pos hpi, hpi, min_eq_left h]
  · rw [if_neg hpi]; by_cases hpj : pos = c.j
    · rw [if_pos hpj, hpj, max_eq_right h]
    · rw [if_neg hpj]

/-- When `w(c.j) < w(c.i)`, the comparator swaps positions `i` and `j`. -/
lemma Comparator.apply_eq_swap {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (w : Fin n → α) (h : w c.j < w c.i) (pos : Fin n) :
    c.apply w pos = w (Equiv.swap c.i c.j pos) := by
  unfold Comparator.apply
  by_cases hpi : pos = c.i
  · rw [if_pos hpi, hpi, min_eq_right h.le, Equiv.swap_apply_left]
  · rw [if_neg hpi]; by_cases hpj : pos = c.j
    · rw [if_pos hpj, hpj, max_eq_left h.le, Equiv.swap_apply_right]
    · rw [if_neg hpj, Equiv.swap_apply_of_ne_of_ne hpi hpj]


/-! **SepInitial direction: small values at high positions** -/

/-- A single comparator does not increase the count of small values at high positions.
    At position `c.j` (higher), the comparator places `max`, which is harder
    to be `< threshold`. -/
lemma apply_displaced_le {n : ℕ} (c : Comparator n) (w : Fin n → Fin n)
    (B threshold : ℕ) :
    (univ.filter (fun pos : Fin n ↦
      B ≤ pos.val ∧ (c.apply w pos).val < threshold)).card ≤
    (univ.filter (fun pos : Fin n ↦
      B ≤ pos.val ∧ (w pos).val < threshold)).card := by
  by_cases hle : w c.i ≤ w c.j
  · rw [c.apply_eq_of_le w hle]
  · push_neg at hle
    by_cases hBi : B ≤ c.i.val
    · -- B ≤ c.i: swap bijection preserves cardinality
      have hBj : B ≤ c.j.val := le_trans hBi (le_of_lt c.h)
      apply le_of_eq
      apply Finset.card_nbij' (Equiv.swap c.i c.j) (Equiv.swap c.i c.j)
      · intro pos hp
        simp only [mem_coe, mem_filter, mem_univ, true_and] at hp ⊢
        refine ⟨?_, by rw [c.apply_eq_swap w hle] at hp
                       simpa [Equiv.swap_apply_self] using hp.2⟩
        by_cases hpi : pos = c.i
        · rw [hpi, Equiv.swap_apply_left]; exact hBj
        · by_cases hpj : pos = c.j
          · rw [hpj, Equiv.swap_apply_right]; exact hBi
          · rw [Equiv.swap_apply_of_ne_of_ne hpi hpj]; exact hp.1
      · intro pos hp
        simp only [mem_coe, mem_filter, mem_univ, true_and] at hp ⊢
        refine ⟨?_, by rw [c.apply_eq_swap w hle]
                       simpa [Equiv.swap_apply_self] using hp.2⟩
        by_cases hpi : pos = c.i
        · rw [hpi, Equiv.swap_apply_left]; exact hBj
        · by_cases hpj : pos = c.j
          · rw [hpj, Equiv.swap_apply_right]; exact hBi
          · rw [Equiv.swap_apply_of_ne_of_ne hpi hpj]; exact hp.1
      · intro _ _; simp [Equiv.swap_apply_self]
      · intro _ _; simp [Equiv.swap_apply_self]
    · -- c.i < B: subset argument
      push_neg at hBi
      apply Finset.card_le_card
      intro pos hp
      simp only [mem_filter, mem_univ, true_and] at hp ⊢
      refine ⟨hp.1, ?_⟩
      rw [c.apply_eq_swap w hle] at hp
      by_cases hpi : pos = c.i
      · subst hpi; omega
      · by_cases hpj : pos = c.j
        · subst hpj; rw [Equiv.swap_apply_right] at hp; exact lt_trans hle hp.2
        · rw [Equiv.swap_apply_of_ne_of_ne hpi hpj] at hp; exact hp.2

/-- A comparator network does not increase the count of small values at high positions. -/
theorem exec_displaced_le {n : ℕ} (net : ComparatorNetwork n)
    (w : Fin n → Fin n) (B threshold : ℕ) :
    (univ.filter (fun pos : Fin n ↦
      B ≤ pos.val ∧ (net.exec w pos).val < threshold)).card ≤
    (univ.filter (fun pos : Fin n ↦
      B ≤ pos.val ∧ (w pos).val < threshold)).card := by
  unfold ComparatorNetwork.exec
  induction net.comparators generalizing w with
  | nil => exact le_refl _
  | cons c cs ih =>
    simp only [List.foldl_cons]
    exact le_trans (ih (c.apply w)) (apply_displaced_le c w B threshold)


/-! **SepFinal direction: large values at low positions** -/

/-- A single comparator does not increase large values at low positions.
    At position `c.i` (lower), the comparator places `min`, which is harder
    to be `≥ threshold`. -/
lemma apply_displaced_final_le {n : ℕ} (c : Comparator n) (w : Fin n → Fin n)
    (B threshold : ℕ) :
    (univ.filter (fun pos : Fin n ↦
      pos.val < B ∧ threshold ≤ (c.apply w pos).val)).card ≤
    (univ.filter (fun pos : Fin n ↦
      pos.val < B ∧ threshold ≤ (w pos).val)).card := by
  by_cases hle : w c.i ≤ w c.j
  · rw [c.apply_eq_of_le w hle]
  · push_neg at hle
    have hsw : ∀ q, c.apply w q = w (Equiv.swap c.i c.j q) := c.apply_eq_swap w hle
    by_cases hBj : c.j.val < B
    · -- Both below B: swap bijection preserves cardinality
      have hBi : c.i.val < B := lt_trans c.h hBj
      apply le_of_eq
      apply Finset.card_nbij' (Equiv.swap c.i c.j) (Equiv.swap c.i c.j)
      · intro pos hp
        simp only [mem_coe, mem_filter, mem_univ, true_and] at hp ⊢
        refine ⟨?_, ?_⟩
        · by_cases hpi : pos = c.i
          · rw [hpi, Equiv.swap_apply_left]; exact hBj
          · by_cases hpj : pos = c.j
            · rw [hpj, Equiv.swap_apply_right]; exact hBi
            · rw [Equiv.swap_apply_of_ne_of_ne hpi hpj]; exact hp.1
        · rw [hsw pos] at hp; simpa [Equiv.swap_apply_self] using hp.2
      · intro pos hp
        simp only [mem_coe, mem_filter, mem_univ, true_and] at hp ⊢
        refine ⟨?_, ?_⟩
        · by_cases hpi : pos = c.i
          · rw [hpi, Equiv.swap_apply_left]; exact hBj
          · by_cases hpj : pos = c.j
            · rw [hpj, Equiv.swap_apply_right]; exact hBi
            · rw [Equiv.swap_apply_of_ne_of_ne hpi hpj]; exact hp.1
        · rw [hsw (Equiv.swap c.i c.j pos), Equiv.swap_apply_self]; exact hp.2
      · intro _ _; simp [Equiv.swap_apply_self]
      · intro _ _; simp [Equiv.swap_apply_self]
    · -- c.j ≥ B: subset (c.i gets min ≤ w(c.i), c.j not counted)
      push_neg at hBj
      apply Finset.card_le_card
      intro pos hp
      simp only [mem_filter, mem_univ, true_and] at hp ⊢
      refine ⟨hp.1, ?_⟩
      rw [hsw pos] at hp
      by_cases hpi : pos = c.i
      · subst hpi; rw [Equiv.swap_apply_left] at hp; exact le_trans hp.2 hle.le
      · by_cases hpj : pos = c.j
        · subst hpj; omega
        · rw [Equiv.swap_apply_of_ne_of_ne hpi hpj] at hp; exact hp.2

/-- A comparator network does not increase large values at low positions. -/
theorem exec_displaced_final_le {n : ℕ} (net : ComparatorNetwork n)
    (w : Fin n → Fin n) (B threshold : ℕ) :
    (univ.filter (fun pos : Fin n ↦
      pos.val < B ∧ threshold ≤ (net.exec w pos).val)).card ≤
    (univ.filter (fun pos : Fin n ↦
      pos.val < B ∧ threshold ≤ (w pos).val)).card := by
  unfold ComparatorNetwork.exec
  induction net.comparators generalizing w with
  | nil => exact le_refl _
  | cons c cs ih =>
    simp only [List.foldl_cons]
    exact le_trans (ih (c.apply w)) (apply_displaced_final_le c w B threshold)

end
