/-
  # König's Edge Coloring Theorem

  A d-regular bipartite multigraph decomposes into d perfect matchings.
  Proved by induction on d: extract one matching (via Hall's theorem),
  remove it to get a (d-1)-regular graph, and recurse.

  Main results:
  • `removeMatching`       — remove a matching from (d+1)-regular to get d-regular
  • `konig_coloring`       — d perfect matchings with partition property
-/

import AKS.Konig.Hall

open Finset BigOperators


/-! **Removing a Perfect Matching** -/

/-- Remove a perfect matching from a (d+1)-regular bipartite graph.
    Uses `Fin.succAbove` to skip the matched port at each vertex,
    producing a d-regular bipartite graph on the remaining edges. -/
noncomputable def RegBipartite.removeMatching {m d : ℕ} (B : RegBipartite m (d + 1))
    (M : PerfectMatching B) : RegBipartite m d where
  edges v p := B.edges v ((M.portOf v).succAbove p)
  bot_regular u := by
    set new_fiber := (univ ×ˢ (univ : Finset (Fin d))).filter
      (fun vp : Fin m × Fin d ↦ B.edges vp.1 ((M.portOf vp.1).succAbove vp.2) = u)
    set old_fiber := (univ ×ˢ (univ : Finset (Fin (d + 1)))).filter
      (fun vp : Fin m × Fin (d + 1) ↦ B.edges vp.1 vp.2 = u)
    have h_match_bij : Function.Bijective (fun v ↦ B.edges v (M.portOf v)) :=
      Finite.injective_iff_bijective.mp M.injective
    obtain ⟨v₀, hv₀⟩ := h_match_bij.2 u
    have hv₀_mem : (v₀, M.portOf v₀) ∈ old_fiber := by
      simp only [old_fiber, mem_filter, Finset.mem_product, mem_univ, true_and]
      exact hv₀
    have h_old : old_fiber.card = d + 1 := B.bot_regular u
    suffices new_fiber.card = (old_fiber.erase (v₀, M.portOf v₀)).card by
      rw [this, card_erase_of_mem hv₀_mem, h_old, Nat.add_sub_cancel]
    -- Handle d = 0 separately (Fin 0 is empty so new_fiber is empty)
    rcases Nat.eq_zero_or_pos d with rfl | hd_pos
    · simp only [new_fiber, Finset.univ_eq_empty (α := Fin 0), Finset.product_empty,
        Finset.filter_empty, Finset.card_empty]
      rw [Finset.card_erase_of_mem hv₀_mem, h_old]
    · -- d > 0: bijection via succAbove
      apply card_nbij'
        (fun ⟨v, p⟩ ↦ (v, (M.portOf v).succAbove p))
        (fun ⟨v, q⟩ ↦ (v,
          if h : q.val < (M.portOf v).val
          then ⟨q.val, by omega⟩
          else ⟨q.val - 1, by have := q.isLt; omega⟩))
      · -- Forward: new_fiber → old_fiber.erase
        intro ⟨v, p⟩ hvp
        have hvp' := (mem_filter.mp (Finset.mem_coe.mp hvp)).2
        refine Finset.mem_coe.mpr (mem_erase.mpr ⟨?_, mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨mem_univ _, mem_univ _⟩, hvp'⟩⟩)
        intro heq
        have hv_eq := (Prod.mk.inj heq).1
        subst hv_eq
        exact absurd (Prod.mk.inj heq).2 (Fin.succAbove_ne _ _)
      · -- Backward: old_fiber.erase → new_fiber
        intro ⟨v, q⟩ hvq
        have hvq' := mem_erase.mp (Finset.mem_coe.mp hvq)
        have hq_mem : B.edges v q = u := (mem_filter.mp hvq'.2).2
        have hne_pair : (v, q) ≠ (v₀, M.portOf v₀) := hvq'.1
        have hne : q ≠ M.portOf v := by
          intro heq
          have h1 : B.edges v (M.portOf v) = u := by rw [← heq]; exact hq_mem
          have hv_eq : v = v₀ := M.injective (h1.trans hv₀.symm)
          exact hne_pair (Prod.ext hv_eq (heq.trans (congr_arg M.portOf hv_eq)))
        have hne_val : q.val ≠ (M.portOf v).val := fun h ↦ hne (Fin.ext h)
        simp only [Finset.mem_coe, new_fiber, mem_filter, Finset.mem_product, mem_univ,
          true_and]
        split_ifs with h
        · -- q.val < (M.portOf v).val
          rw [Fin.succAbove, if_pos (show (⟨q.val, by omega⟩ : Fin d).castSucc < M.portOf v by
            simp only [Fin.lt_def, Fin.val_castSucc]; exact h)]
          exact hq_mem
        · -- q.val ≥ (M.portOf v).val
          push_neg at h
          have hlt : (M.portOf v).val < q.val := Nat.lt_of_le_of_ne h (Ne.symm hne_val)
          rw [Fin.succAbove, if_neg (show ¬((⟨q.val - 1, by omega⟩ : Fin d).castSucc <
              M.portOf v) by simp only [Fin.lt_def, Fin.val_castSucc]; omega)]
          show B.edges v (Fin.succ ⟨q.val - 1, _⟩) = u
          have : (Fin.succ ⟨q.val - 1, by omega⟩ : Fin (d + 1)) = q :=
            Fin.ext (by simp only [Fin.val_succ]; omega)
          rw [this]; exact hq_mem
      · -- Left inverse: backward ∘ forward = id on new_fiber
        intro ⟨v, p⟩ _
        ext
        · rfl
        · simp only [Fin.succAbove]
          split_ifs with h₁ h₂ h₃
          · -- castSucc p < pivot, (castSucc p).val < pivot.val
            simp only [Fin.val_castSucc]
          · -- castSucc p < pivot, ¬((castSucc p).val < pivot.val) → impossible
            exact absurd (Fin.lt_def.mp h₁) h₂
          · -- ¬(castSucc p < pivot), (succ p).val < pivot.val → impossible
            exfalso; push_neg at h₁
            have := Fin.le_def.mp h₁; simp only [Fin.val_castSucc] at this
            simp only [Fin.val_succ] at h₃; omega
          · -- ¬(castSucc p < pivot), ¬((succ p).val < pivot.val)
            simp only [Fin.val_succ]; omega
      · -- Right inverse: forward ∘ backward = id on old_fiber.erase
        intro ⟨v, q⟩ hvq
        have hvq' := mem_erase.mp (Finset.mem_coe.mp hvq)
        have hq_mem : B.edges v q = u := (mem_filter.mp hvq'.2).2
        have hne_pair : (v, q) ≠ (v₀, M.portOf v₀) := hvq'.1
        have hne : q ≠ M.portOf v := by
          intro heq
          have h1 : B.edges v (M.portOf v) = u := by rw [← heq]; exact hq_mem
          exact hne_pair (Prod.ext (M.injective (h1.trans hv₀.symm))
            (heq.trans (congr_arg M.portOf (M.injective (h1.trans hv₀.symm)))))
        have hne_val : q.val ≠ (M.portOf v).val := fun h ↦ hne (Fin.ext h)
        ext
        · rfl
        · simp only [Fin.succAbove]
          split_ifs with h₁ h₂ h₃
          · -- q.val < pivot.val, castSucc ⟨q.val, _⟩ < pivot
            simp only [Fin.val_castSucc]
          · -- q.val < pivot.val, ¬(castSucc ⟨q.val, _⟩ < pivot) → impossible
            exfalso; simp only [Fin.lt_def, Fin.val_castSucc] at h₂; omega
          · -- ¬(q.val < pivot.val), castSucc ⟨q.val - 1, _⟩ < pivot → impossible
            exfalso; push_neg at h₁
            simp only [Fin.lt_def, Fin.val_castSucc] at h₃; omega
          · -- ¬(q.val < pivot.val), ¬(castSucc ⟨q.val - 1, _⟩ < pivot)
            push_neg at h₁
            simp only [Fin.val_succ]; omega


/-! **König's Edge Coloring** -/

/-- Lift a perfect matching of `B.removeMatching M` back to a perfect matching of `B`,
    by composing port selection with `succAbove` (skip the matched port). -/
private def liftMatching {m d : ℕ} (B : RegBipartite m (d + 1))
    (M : PerfectMatching B)
    (M' : PerfectMatching (B.removeMatching M)) :
    PerfectMatching B where
  portOf v := (M.portOf v).succAbove (M'.portOf v)
  injective _ _ h := M'.injective h

/-- König's edge coloring: d perfect matchings that partition all edges.
    Returns matchings and proof that ports are bijective per vertex. -/
noncomputable def RegBipartite.konigData {m : ℕ} :
    ∀ (d : ℕ) (B : RegBipartite m d) (_ : 0 < d),
    { matchings : Fin d → PerfectMatching B //
      ∀ v : Fin m, Function.Bijective (fun k ↦ (matchings k).portOf v) }
  | 0, _, hd => absurd hd (by omega)
  | 1, B, _ =>
    let M := B.exists_perfect_matching (by omega)
    ⟨fun _ ↦ M, fun v ↦ by
      constructor
      · intro a b _; exact Subsingleton.elim a b
      · intro q; exact ⟨⟨0, by omega⟩, by ext; omega⟩⟩
  | d + 2, B, _ =>
    let M := B.exists_perfect_matching (by omega)
    let B' := B.removeMatching M
    let ⟨matchings', h_bij'⟩ := konigData (d + 1) B' (by omega)
    ⟨Fin.cons M (fun k ↦ liftMatching B M (matchings' k)), fun v ↦ by
      constructor
      · -- Injectivity
        intro ⟨i, hi⟩ ⟨j, hj⟩ heq
        simp only [Fin.cons] at heq
        match i, j with
        | 0, 0 => rfl
        | 0, j + 1 =>
          exfalso; exact absurd heq.symm (Fin.succAbove_ne _ _)
        | i + 1, 0 =>
          exfalso; exact absurd heq (Fin.succAbove_ne _ _)
        | i + 1, j + 1 =>
          have h_ij := (h_bij' v).1 (Fin.succAbove_right_injective heq)
          have hij : i = j := by rw [Fin.mk.injEq] at h_ij; exact h_ij
          subst hij; rfl
      · -- Surjectivity
        intro q
        by_cases hq : q = M.portOf v
        · exact ⟨⟨0, by omega⟩, by simp [Fin.cons, hq]⟩
        · -- q ≠ M.portOf v, so q is in the range of succAbove
          obtain ⟨p, hp⟩ := Fin.exists_succAbove_eq hq
          obtain ⟨k, hk⟩ := (h_bij' v).2 p
          refine ⟨k.succ, ?_⟩
          simp only [Fin.cons_succ]
          show (M.portOf v).succAbove ((matchings' k).portOf v) = q
          have hk' : (matchings' k).portOf v = p := hk
          rw [hk', hp]⟩


/-! **Downstream API** -/

/-- König's edge coloring: every d-regular bipartite multigraph (d > 0) admits
    d perfect matchings covering all edges. -/
noncomputable def RegBipartite.konigMatchings {m d : ℕ} (B : RegBipartite m d) (hd : 0 < d) :
    Fin d → PerfectMatching B :=
  (B.konigData d hd).val

theorem RegBipartite.konigMatchings_bijective {m d : ℕ} (B : RegBipartite m d) (hd : 0 < d)
    (v : Fin m) :
    Function.Bijective (fun k ↦ (B.konigMatchings hd k).portOf v) :=
  (B.konigData d hd).property v
