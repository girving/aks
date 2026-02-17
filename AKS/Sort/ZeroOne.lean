/-
  # The 0-1 Principle

  A comparator network sorts all inputs iff it sorts all Boolean (0-1) inputs.
  This is the key reduction that makes correctness proofs tractable.
-/

import AKS.Sort.Monotone

open Finset BigOperators


/-- The 0-1 Principle: A comparator network sorts all inputs iff it
    sorts all Boolean (0-1) inputs. This is the key reduction that
    makes correctness proofs tractable. -/
theorem zero_one_principle {n : ℕ} (net : ComparatorNetwork n) :
    (∀ (v : Fin n → Bool), Monotone (net.exec v)) →
    IsSortingNetwork net := by
  intro h_bool
  unfold IsSortingNetwork
  intro α _ v
  -- By contradiction: if net.exec v isn't sorted, construct a
  -- Boolean witness via a threshold function.
  by_contra h_not_mono
  simp only [Monotone, not_forall, not_le] at h_not_mono
  obtain ⟨i, j, hij, hlt⟩ := h_not_mono
  -- hlt : (net.exec v) j < (net.exec v) i, with hij : i ≤ j
  -- Threshold function: true iff strictly above (net.exec v) j
  let f : α → Bool := fun x ↦ decide ((net.exec v) j < x)
  have hf : Monotone f := by
    intro a b hab
    show decide ((net.exec v) j < a) ≤ decide ((net.exec v) j < b)
    by_cases ha : (net.exec v) j < a
    · have hb : (net.exec v) j < b := lt_of_lt_of_le ha hab
      simp [ha, hb]
    · simp [ha]
  -- By exec_comp_monotone: net.exec (f ∘ v) = f ∘ (net.exec v)
  have hcomm := (net.exec_comp_monotone (f := f) hf v).symm
  -- The Boolean input f ∘ v is not sorted by the network
  have h_sorted := (h_bool (f ∘ v)) hij
  rw [hcomm, show (f ∘ net.exec v) i = true from decide_eq_true_eq.mpr hlt,
      show (f ∘ net.exec v) j = false from decide_eq_false_iff_not.mpr (lt_irrefl _)] at h_sorted
  exact absurd h_sorted (by decide)
