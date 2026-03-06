module
/-
  # Comparator Filter/Range Preservation and Separator-Quality Lemmas

  Extracted from `Strange.lean` for faster incremental checking.

  Contains:
  - Comparator filter preservation: a comparator (or network) preserves
    filter cardinality when both endpoints are in S or both outside.
  - Range preservation: comparator network execution preserves the
    multiset of values (as `Set.range`).
  - Separator-quality lemmas: `strangers_stage_invariant` (perm invariance
    across stage application) and `kick_stranger_le` (kick bound from
    child to parent).
-/

public import AKS.Bags.Sizes

@[expose] public section

open Finset

variable {k : ℕ}

/-! **Comparator Filter Preservation** -/

/-- A comparator preserves filter cardinality for value predicates when
    both positions are in S or both outside. -/
theorem comparator_card_filter {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (v : Fin n → α) (S : Finset (Fin n))
    (P : α → Prop) [DecidablePred P]
    (h : (c.i ∈ S ∧ c.j ∈ S) ∨ (c.i ∉ S ∧ c.j ∉ S)) :
    (S.filter (fun r ↦ P (c.apply v r))).card =
    (S.filter (fun r ↦ P (v r))).card := by
  rcases h with ⟨hi, hj⟩ | ⟨hni, hnj⟩
  · -- Both in S
    by_cases hle : v c.i ≤ v c.j
    · rw [c.apply_eq_of_le v hle]
    · push_neg at hle
      have hsw : c.apply v = v ∘ ⇑(Equiv.swap c.i c.j) := by
        ext r; exact c.apply_eq_swap v hle r
      rw [hsw]
      -- Need: (S.filter (P ∘ v ∘ swap)).card = (S.filter (P ∘ v)).card
      set σ := Equiv.swap c.i c.j
      have swap_mem : ∀ {r}, r ∈ S → σ r ∈ S := by
        intro r hr; simp only [σ, Equiv.swap_apply_def]
        split_ifs <;> assumption
      apply Finset.card_nbij' (fun r ↦ σ r) (fun r ↦ σ r)
      · intro r hr; simp only [mem_coe, mem_filter, Function.comp] at hr ⊢
        exact ⟨swap_mem hr.1, hr.2⟩
      · intro r hr; simp only [mem_coe, mem_filter, Function.comp] at hr ⊢
        exact ⟨swap_mem hr.1, by rw [Equiv.swap_apply_self]; exact hr.2⟩
      · intro r _; exact Equiv.swap_apply_self c.i c.j r
      · intro r _; exact Equiv.swap_apply_self c.i c.j r
  · -- Both outside S: comparator doesn't affect S
    congr 1; apply filter_congr; intro r hr
    simp only [Comparator.apply,
      if_neg (show r ≠ c.i from fun h ↦ hni (h ▸ hr)),
      if_neg (show r ≠ c.j from fun h ↦ hnj (h ▸ hr))]

/-- A comparator network preserves filter cardinality for value predicates when
    every comparator has both positions in S or both outside. -/
theorem foldl_card_filter {n : ℕ} {α : Type*} [LinearOrder α]
    (cs : List (Comparator n)) (v : Fin n → α) (S : Finset (Fin n))
    (P : α → Prop) [DecidablePred P]
    (h : ∀ c ∈ cs, (c.i ∈ S ∧ c.j ∈ S) ∨ (c.i ∉ S ∧ c.j ∉ S)) :
    (S.filter (fun r ↦ P (cs.foldl (fun acc c ↦ c.apply acc) v r))).card =
    (S.filter (fun r ↦ P (v r))).card := by
  induction cs generalizing v with
  | nil => rfl
  | cons c cs ih =>
    rw [List.foldl_cons]
    rw [ih (c.apply v) (fun c' hc' ↦ h c' (.tail c hc'))]
    exact comparator_card_filter c v S P (h c (.head cs))

theorem network_card_filter {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) (v : Fin n → α) (S : Finset (Fin n))
    (P : α → Prop) [DecidablePred P]
    (h : ∀ c ∈ net.comparators, (c.i ∈ S ∧ c.j ∈ S) ∨ (c.i ∉ S ∧ c.j ∉ S)) :
    (S.filter (fun r ↦ P (net.exec v r))).card =
    (S.filter (fun r ↦ P (v r))).card :=
  foldl_card_filter net.comparators v S P h

/-! **Range Preservation** -/

/-- A single comparator preserves the range (multiset of values) of a function. -/
theorem Comparator.apply_range_eq {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (v : Fin n → α) :
    Set.range (c.apply v) = Set.range v := by
  ext val
  simp only [Set.mem_range]
  constructor
  · intro ⟨k, hk⟩
    unfold Comparator.apply at hk
    by_cases hki : k = c.i
    · subst hki; simp only [↓reduceIte] at hk
      by_cases hle : v c.i ≤ v c.j
      · rw [min_eq_left hle] at hk; exact ⟨c.i, hk⟩
      · push_neg at hle; rw [min_eq_right hle.le] at hk; exact ⟨c.j, hk⟩
    · simp only [hki, ↓reduceIte] at hk
      by_cases hkj : k = c.j
      · subst hkj; simp only [↓reduceIte] at hk
        by_cases hle : v c.i ≤ v c.j
        · rw [max_eq_right hle] at hk; exact ⟨c.j, hk⟩
        · push_neg at hle; rw [max_eq_left hle.le] at hk; exact ⟨c.i, hk⟩
      · simp only [hkj, ↓reduceIte] at hk; exact ⟨k, hk⟩
  · intro ⟨k, hk⟩
    by_cases hki : k = c.i
    · -- v k = v c.i; need to find a position that maps to v c.i
      by_cases hle : v c.i ≤ v c.j
      · use c.i; unfold Comparator.apply; subst hki
        simp only [min_eq_left hle]; exact hk
      · push_neg at hle
        use c.j; unfold Comparator.apply; subst hki
        simp only [ne_of_gt c.h, ↓reduceIte, max_eq_left hle.le]; exact hk
    · by_cases hkj : k = c.j
      · -- v k = v c.j
        by_cases hle : v c.i ≤ v c.j
        · use c.j; unfold Comparator.apply; subst hkj
          simp only [ne_of_gt c.h, ↓reduceIte, max_eq_right hle]; exact hk
        · push_neg at hle
          use c.i; unfold Comparator.apply; subst hkj
          simp only [min_eq_right hle.le]; exact hk
      · -- k is neither c.i nor c.j
        use k; unfold Comparator.apply; simp [hki, hkj, hk]

/-- Comparator network execution preserves the range (multiset of values). -/
theorem ComparatorNetwork.exec_range_eq {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) (v : Fin n → α) :
    Set.range (net.exec v) = Set.range v := by
  unfold ComparatorNetwork.exec
  induction net.comparators generalizing v with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [ih (c.apply v), c.apply_range_eq]

/-! **Separator-Quality Lemmas** -/

/-- The stage separator only rearranges values within each bag's registers,
    so the stranger count on the whole bag is preserved.

    The stage network is composed of per-bag separators via scatter embedding,
    and each per-bag separator only affects wires within that bag's register set
    (disjoint from other bags by `Placement.disjoint`). Since exec only
    rearranges values among the affected wires, the multiset of values on
    each bag's registers is preserved, hence the stranger count is unchanged. -/
theorem strangers_stage_invariant (p : Params) (k : ℕ)
    (perm₀ : Fin (2 ^ k) → Fin (2 ^ k))
    (t : ℕ) (c : Bag k) (j : ℕ) :
    c.strangers j ((stages p k (t + 1)).net.exec perm₀)
      ((stages p k t).value.regs c) =
    c.strangers j ((stages p k t).net.exec perm₀)
      ((stages p k t).value.regs c) := by
  -- Decompose stages(t+1).net.exec into stage_net.exec ∘ stages(t).net.exec
  set pl := (stages p k t).value
  set perm_t := (stages p k t).net.exec perm₀
  set S := pl.regs c
  have hexec : (stages p k (t + 1)).net.exec perm₀ =
      (stage p pl t).net.exec perm_t := by
    show (do let pl' ← stages p k t; stage p pl' t).net.exec perm₀ = _
    rw [Build.exec_bind]
  rw [hexec]
  set snet := (stage p pl t).net
  -- Rewrite Strange in terms of a value predicate P
  set a := c.ancestor (j - 1)
  have hstrange : ∀ (perm : Fin (2 ^ k) → Fin (2 ^ k)) (r : Fin (2 ^ k)),
      c.Strange j r perm = (j = 0 ∨ nativeBagIdx k a.l (perm r).val ≠ a.x) := fun _ _ ↦ rfl
  simp only [Bag.strangers, hstrange]
  exact network_card_filter snet perm_t S
    (fun v ↦ j = 0 ∨ nativeBagIdx k a.l v.val ≠ a.x) (by
    -- Every comparator in snet respects S = pl.regs c
    intro comp hcomp
    -- Extract: comp comes from some bag b's separator, with both positions in pl.regs b
    -- Stage net structure: stage emits flatMap of per-bag separator networks
    show (comp.i ∈ S ∧ comp.j ∈ S) ∨ (comp.i ∉ S ∧ comp.j ∉ S)
    -- Unfold stage to access the comparator list
    have hcomp' : comp ∈ (stage p pl t).net.comparators := hcomp
    unfold stage separateAndSplit separate at hcomp'
    simp only [Build.net_bind, Build.net_emit, Build.net_pure, List.append_nil] at hcomp'
    -- hcomp' : comp ∈ flatMap of per-bag separator comparators
    rw [List.mem_flatMap] at hcomp'
    obtain ⟨b, _, hcomp_b⟩ := hcomp'
    -- comp is in bag b's scatter-embedded separator
    rw [ComparatorNetwork.scatterEmbed] at hcomp_b
    simp only [List.mem_map] at hcomp_b
    obtain ⟨c', _, hceq⟩ := hcomp_b
    -- Both endpoints are in the range of the embedding, which is ⊆ pl.regs b
    -- The embedding is castLEOrderEmb.trans (orderEmbOfFin rfl), so its range ⊆ regs
    have hemb_mem : ∀ (i : Fin (2 * ((pl.regs b).card / 2))),
        ((Fin.castLEOrderEmb (by omega : 2 * ((pl.regs b).card / 2) ≤ (pl.regs b).card)).trans
          ((pl.regs b).orderEmbOfFin rfl)) i ∈ pl.regs b := by
      intro i; exact orderEmbOfFin_mem _ rfl _
    have hin : comp.i ∈ pl.regs b ∧ comp.j ∈ pl.regs b := by
      rw [← hceq]; exact ⟨hemb_mem _, hemb_mem _⟩
    by_cases hbc : b = c
    · left; rwa [hbc] at hin
    · right
      have hdisj := pl.disjoint b c hbc
      exact ⟨fun hi ↦ absurd hin.1 (disjoint_right.mp hdisj hi),
             fun hj ↦ absurd hin.2 (disjoint_right.mp hdisj hj)⟩)

/-- Kick bound: items kicked from child `c` to parent `c.parent` have
    bounded j-stranger count at the parent level.

    Chain: level shift → subset monotonicity → perm invariance → IH.
    The key insight: the separator within c only rearranges values among
    c's wires, preserving the stranger count on the whole bag. -/
theorem kick_stranger_le (p : Params) (k : ℕ)
    (perm₀ : Fin (2 ^ k) → Fin (2 ^ k))
    (t : ℕ)
    (ih : ∀ (b : Bag k) (j : ℕ), 1 ≤ j →
      (b.strangers j ((stages p k t).net.exec perm₀)
        ((stages p k t).value.regs b) : ℚ) ≤
      p.γ * p.ε ^ (j - 1) * capacity p k t b.l)
    (c : Bag k) (hl : 1 ≤ c.l) (j : ℕ) (hj : 1 ≤ j)
    (S : Finset (Fin (2 ^ k))) (hS : S ⊆ (stages p k t).value.regs c) :
    (c.parent.strangers j ((stages p k (t + 1)).net.exec perm₀) S : ℚ) ≤
    p.γ * p.ε ^ j * capacity p k t c.l := by
  -- Level shift: c.parent.strangers j = c.strangers (j+1) since c.l ≥ 1
  have level_shift : c.parent.strangers j
      ((stages p k (t + 1)).net.exec perm₀) S =
      c.strangers (j + 1) ((stages p k (t + 1)).net.exec perm₀) S :=
    Bag.strangers_parent_eq c j hj hl _ S
  -- Perm invariance on whole bag
  have perm_inv := strangers_stage_invariant p k perm₀ t c (j + 1)
  -- IH at j+1
  have ih_c := ih c (j + 1) (by omega)
  rw [show (j + 1) - 1 = j from by omega] at ih_c
  -- Chain
  calc (c.parent.strangers j ((stages p k (t + 1)).net.exec perm₀) S : ℚ)
      = ↑(c.strangers (j + 1) ((stages p k (t + 1)).net.exec perm₀) S) := by
          exact_mod_cast level_shift
    _ ≤ ↑(c.strangers (j + 1) ((stages p k (t + 1)).net.exec perm₀)
          ((stages p k t).value.regs c)) := by
          exact_mod_cast Bag.strangers_mono c (j + 1) _ hS
    _ = ↑(c.strangers (j + 1) ((stages p k t).net.exec perm₀)
          ((stages p k t).value.regs c)) := by
          exact_mod_cast perm_inv
    _ ≤ p.γ * p.ε ^ j * capacity p k t c.l := ih_c

end
