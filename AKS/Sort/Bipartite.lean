module
/-
  # Bipartite Comparator Lemmas

  Monotonicity and ordering lemmas for bipartite comparator networks:
  comparators whose top wire `c.i.val < m` and bottom wire `m ≤ c.j.val`.

  Main results:
  • `foldl_member_order`: after executing a bipartite list, each comparator's
    wires satisfy `output[c.i] ≤ output[c.j]`
-/

public import AKS.Sort.Defs

@[expose] public section


open Finset BigOperators


/-! **Bipartite Comparator Monotonicity** -/

/-- Applying a bipartite comparator: top values can only decrease. -/
lemma bipartite_apply_top_le {n m : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n)
    (hcj : m ≤ c.j.val)
    (w : Fin n → α) (k : Fin n) (hk : k.val < m) :
    c.apply w k ≤ w k := by
  have hkj : k ≠ c.j := fun h => absurd (h ▸ hk) (by omega)
  by_cases hki : k = c.i
  · subst hki; unfold Comparator.apply; rw [if_pos rfl]; exact min_le_left _ _
  · unfold Comparator.apply; rw [if_neg hki, if_neg hkj]

/-- Applying a bipartite comparator: bottom values can only increase. -/
lemma bipartite_apply_bot_ge {n m : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n)
    (hci : c.i.val < m)
    (w : Fin n → α) (k : Fin n) (hk : m ≤ k.val) :
    w k ≤ c.apply w k := by
  have hki : k ≠ c.i := fun h => absurd (h ▸ hk) (by omega)
  by_cases hkj : k = c.j
  · subst hkj; unfold Comparator.apply; rw [if_neg hki, if_pos rfl]; exact le_max_right _ _
  · unfold Comparator.apply; rw [if_neg hki, if_neg hkj]

/-- A comparator establishes order between its two wires: output[i] ≤ output[j]. -/
lemma comparator_apply_order {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (w : Fin n → α) :
    c.apply w c.i ≤ c.apply w c.j := by
  have hij : c.j ≠ c.i := c.h.ne'
  unfold Comparator.apply
  rw [if_pos rfl, if_neg hij, if_pos rfl]
  exact le_trans (min_le_left _ _) (le_max_left _ _)

/-- Executing a list of bipartite comparators preserves ordering between
    a top wire and a bottom wire. -/
lemma foldl_bipartite_preserves_le {n m : ℕ} {α : Type*} [LinearOrder α]
    (cs : List (Comparator n))
    (hcs : ∀ c ∈ cs, c.i.val < m ∧ m ≤ c.j.val)
    (w : Fin n → α) (top bot : Fin n) (htop : top.val < m) (hbot : m ≤ bot.val)
    (h : w top ≤ w bot) :
    (cs.foldl (fun acc c ↦ c.apply acc) w) top ≤
    (cs.foldl (fun acc c ↦ c.apply acc) w) bot := by
  induction cs generalizing w with
  | nil => exact h
  | cons c rest ih =>
    simp only [List.foldl_cons]
    apply ih (fun c' hc' => hcs c' (.tail c hc'))
    have ⟨hci, hcj⟩ := hcs c (.head rest)
    exact le_trans (bipartite_apply_top_le c hcj w top htop)
      (le_trans h (bipartite_apply_bot_ge c hci w bot hbot))

/-- If a comparator c₀ is in a list of bipartite comparators, then after
    executing the list, output[c₀.i] ≤ output[c₀.j]. -/
lemma foldl_member_order {n m : ℕ} {α : Type*} [LinearOrder α]
    (cs : List (Comparator n))
    (c₀ : Comparator n) (hc₀ : c₀ ∈ cs)
    (hall : ∀ c' ∈ cs, c'.i.val < m ∧ m ≤ c'.j.val)
    (w : Fin n → α) :
    (cs.foldl (fun acc c ↦ c.apply acc) w) c₀.i ≤
    (cs.foldl (fun acc c ↦ c.apply acc) w) c₀.j := by
  induction cs generalizing w with
  | nil => nomatch hc₀
  | cons c rest ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hc₀ with rfl | h_rest
    · have ⟨hci, hcj⟩ := hall c₀ (.head rest)
      exact foldl_bipartite_preserves_le rest
        (fun c' hc' => hall c' (.tail c₀ hc'))
        (c₀.apply w) c₀.i c₀.j hci hcj (comparator_apply_order c₀ w)
    · exact ih h_rest
        (fun c' hc' => hall c' (.tail c hc'))
        (c.apply w)

end
