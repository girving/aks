/-
  # ε-Halver Theory

  Defines ε-halvers and proves the expander → halver bridge.

  Key results:
  • `IsEpsilonHalver`: ε-halver definition
  • `expander_gives_halver`: expanders yield ε-halvers (proved)
  • `IsEpsilonSorted`, `Monotone.bool_pattern`: sortedness infrastructure

  The actual AKS correctness proof (geometric decrease of unsortedness)
  uses the tree-based approach in `TreeSorting.lean`, not single-halver
  composition.
-/

import AKS.ComparatorNetwork
import AKS.RegularGraph
import AKS.Mixing

open Finset BigOperators


/-! **ε-Halvers** -/

/-- A comparator network is an ε-halver if, for every 0-1 input,
    after applying the network, the excess of 1s in the top half
    (beyond fair share) is at most `ε · (n / 2)`.

    Concretely: `onesInTop ≤ totalOnes / 2 + ε · (n / 2)`.

    Intuitively: it balances 1s between the two halves, up to
    an ε-fraction error. -/
def IsEpsilonHalver {n : ℕ} (net : ComparatorNetwork n) (ε : ℝ) : Prop :=
  ∀ (v : Fin n → Bool),
    let w := net.exec v
    let topHalf := Finset.univ.filter (fun i : Fin n ↦ (i : ℕ) < n / 2)
    let onesInTop := (topHalf.filter (fun i ↦ w i = true)).card
    let totalOnes := (Finset.univ.filter (fun i : Fin n ↦ w i = true)).card
    (onesInTop : ℝ) ≤ totalOnes / 2 + ε * (n / 2)

/-- The bipartite comparator list: for each vertex v and port p of G,
    compare wire v (top) with wire m + G.neighbor v p (bottom). -/
private def bipartiteComparators {m d : ℕ} (G : RegularGraph m d) :
    List (Comparator (2 * m)) :=
  (List.finRange m).flatMap fun v =>
    (List.finRange d).map fun p =>
      { i := ⟨v.val, by omega⟩
        j := ⟨m + (G.neighbor v p).val, by omega⟩
        h := by simp [Fin.lt_iff_val_lt_val]; omega }

private lemma bipartiteComparators_length {m d : ℕ} (G : RegularGraph m d) :
    (bipartiteComparators G).length = m * d := by
  simp [bipartiteComparators, List.length_flatMap, List.length_map,
    List.length_finRange, List.map_const', List.sum_replicate, Nat.mul_comm]

/-- All comparators in the bipartite network are bipartite: top wire < m ≤ bottom wire. -/
private lemma bipartiteComparators_bipartite {m d : ℕ} (G : RegularGraph m d)
    (c : Comparator (2 * m)) (hc : c ∈ bipartiteComparators G) :
    c.i.val < m ∧ m ≤ c.j.val := by
  simp only [bipartiteComparators, List.mem_flatMap, List.mem_finRange, List.mem_map,
    true_and] at hc
  obtain ⟨v, p, rfl⟩ := hc
  exact ⟨v.isLt, Nat.le_add_right m _⟩

/-- Applying a bipartite Bool comparator: top values can only decrease. -/
private lemma bipartite_apply_top_le {n m : ℕ} (c : Comparator n)
    (hci : c.i.val < m) (hcj : m ≤ c.j.val)
    (w : Fin n → Bool) (k : Fin n) (hk : k.val < m) :
    c.apply w k ≤ w k := by
  have hkj : k ≠ c.j := fun h => absurd (h ▸ hk) (by omega)
  by_cases hki : k = c.i
  · subst hki; unfold Comparator.apply; rw [if_pos rfl]; exact min_le_left _ _
  · unfold Comparator.apply; rw [if_neg hki, if_neg hkj]

/-- Applying a bipartite Bool comparator: bottom values can only increase. -/
private lemma bipartite_apply_bot_ge {n m : ℕ} (c : Comparator n)
    (hci : c.i.val < m) (hcj : m ≤ c.j.val)
    (w : Fin n → Bool) (k : Fin n) (hk : m ≤ k.val) :
    w k ≤ c.apply w k := by
  have hki : k ≠ c.i := fun h => absurd (h ▸ hk) (by omega)
  by_cases hkj : k = c.j
  · subst hkj; unfold Comparator.apply; rw [if_neg hki, if_pos rfl]; exact le_max_right _ _
  · unfold Comparator.apply; rw [if_neg hki, if_neg hkj]

/-- A comparator establishes order between its two wires: output[i] ≤ output[j]. -/
private lemma comparator_apply_order {n : ℕ} (c : Comparator n) (w : Fin n → Bool) :
    c.apply w c.i ≤ c.apply w c.j := by
  have hij : c.j ≠ c.i := c.h.ne'
  unfold Comparator.apply
  rw [if_pos rfl, if_neg hij, if_pos rfl]
  exact le_trans (min_le_left _ _) (le_max_left _ _)

/-- Executing a list of bipartite comparators preserves ordering between
    a top wire and a bottom wire. -/
private lemma foldl_bipartite_preserves_le {n m : ℕ} (cs : List (Comparator n))
    (hcs : ∀ c ∈ cs, c.i.val < m ∧ m ≤ c.j.val)
    (w : Fin n → Bool) (top bot : Fin n) (htop : top.val < m) (hbot : m ≤ bot.val)
    (h : w top ≤ w bot) :
    (cs.foldl (fun acc c ↦ c.apply acc) w) top ≤
    (cs.foldl (fun acc c ↦ c.apply acc) w) bot := by
  induction cs generalizing w with
  | nil => exact h
  | cons c rest ih =>
    simp only [List.foldl_cons]
    apply ih (fun c' hc' => hcs c' (.tail c hc'))
    have ⟨hci, hcj⟩ := hcs c (.head rest)
    exact le_trans (bipartite_apply_top_le c hci hcj w top htop)
      (le_trans h (bipartite_apply_bot_ge c hci hcj w bot hbot))

/-- If a comparator c₀ is in a list of bipartite comparators, then after
    executing the list, output[c₀.i] ≤ output[c₀.j]. -/
private lemma foldl_member_order {n m : ℕ} (cs : List (Comparator n))
    (c₀ : Comparator n) (hc₀ : c₀ ∈ cs)
    (hall : ∀ c' ∈ cs, c'.i.val < m ∧ m ≤ c'.j.val)
    (w : Fin n → Bool) :
    (cs.foldl (fun acc c ↦ c.apply acc) w) c₀.i ≤
    (cs.foldl (fun acc c ↦ c.apply acc) w) c₀.j := by
  induction cs generalizing w with
  | nil => nomatch hc₀
  | cons c rest ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hc₀ with rfl | h_rest
    · -- c = c₀: the comparator establishes the ordering, rest preserves it
      have ⟨hci, hcj⟩ := hall c₀ (.head rest)
      exact foldl_bipartite_preserves_le rest
        (fun c' hc' => hall c' (.tail c₀ hc'))
        (c₀.apply w) c₀.i c₀.j hci hcj (comparator_apply_order c₀ w)
    · -- c₀ ∈ rest: use IH
      exact ih h_rest
        (fun c' hc' => hall c' (.tail c hc'))
        (c.apply w)

/-- The specific comparator for (v, p) is in `bipartiteComparators G`. -/
private lemma mem_bipartiteComparators {m d : ℕ} (G : RegularGraph m d)
    (v : Fin m) (p : Fin d) :
    (⟨⟨v.val, by omega⟩, ⟨m + (G.neighbor v p).val, by omega⟩,
      by simp [Fin.lt_iff_val_lt_val]; omega⟩ : Comparator (2 * m))
      ∈ bipartiteComparators G := by
  simp only [bipartiteComparators, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and]
  exact ⟨v, p, rfl⟩

/-- After executing bipartite comparators, for each (v, p), output satisfies
    w[v] ≤ w[m + G.neighbor v p]. -/
private lemma exec_bipartite_edge_mono {m d : ℕ} (G : RegularGraph m d)
    (w : Fin (2 * m) → Bool) (v : Fin m) (p : Fin d) :
    (bipartiteComparators G).foldl (fun acc c ↦ c.apply acc) w
      ⟨v.val, by omega⟩ ≤
    (bipartiteComparators G).foldl (fun acc c ↦ c.apply acc) w
      ⟨m + (G.neighbor v p).val, by omega⟩ := by
  exact foldl_member_order (bipartiteComparators G)
    ⟨⟨v.val, by omega⟩, ⟨m + (G.neighbor v p).val, by omega⟩,
      by simp [Fin.lt_iff_val_lt_val]; omega⟩
    (mem_bipartiteComparators G v p)
    (bipartiteComparators_bipartite G) w

/-- From p/m ≤ β√p, derive p ≤ β²m². -/
private lemma div_sqrt_to_sq_bound {p m β : ℝ}
    (hp : 0 ≤ p) (hm : 0 < m) (hβ : 0 ≤ β)
    (h : p / m ≤ β * Real.sqrt p) :
    p ≤ β ^ 2 * m ^ 2 := by
  have h1 : p ≤ β * Real.sqrt p * m := by rwa [div_le_iff₀ hm] at h
  nlinarith [sq_nonneg (β * m - Real.sqrt p), Real.sq_sqrt hp]

/-- Partition a predicate on Fin (2*m) into top half (val < m) and bottom half (m ≤ val),
    each bijecting with Fin m. -/
private lemma card_filter_fin_double {m : ℕ} (P : Fin (2 * m) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
    (Finset.univ.filter (fun v : Fin m ↦ P ⟨v.val, by omega⟩)).card +
    (Finset.univ.filter (fun u : Fin m ↦ P ⟨m + u.val, by omega⟩)).card := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · -- Split by i.val < m using card_filter_add_card_filter_not
    rw [← Finset.card_filter_add_card_filter_not (fun i : Fin (2 * m) ↦ i.val < m),
        Finset.filter_filter, Finset.filter_filter]
    congr 1
    · -- Top half: #{i | P i ∧ i.val < m} = #{v : Fin m | P ⟨v.val, _⟩}
      apply Finset.card_nbij'
        (fun i ↦ ⟨i.val % m, Nat.mod_lt _ hm⟩)
        (fun v ↦ ⟨v.val, by omega⟩)
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        convert hi.1 using 1; ext1; exact Nat.mod_eq_of_lt hi.2
      · intro v hv
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        exact ⟨hv, v.isLt⟩
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        ext1; exact Nat.mod_eq_of_lt hi.2
      · intro v _; ext1; exact Nat.mod_eq_of_lt v.isLt
    · -- Bottom half: #{i | P i ∧ ¬(i.val < m)} = #{u : Fin m | P ⟨m+u.val, _⟩}
      apply Finset.card_nbij'
        (fun i ↦ ⟨i.val - m, by omega⟩)
        (fun u ↦ ⟨m + u.val, by omega⟩)
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          not_lt] at hi ⊢
        convert hi.1 using 1; ext1; dsimp; omega
      · intro u hu
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          not_lt] at hu ⊢
        exact ⟨hu, by omega⟩
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          not_lt] at hi
        have := hi.2; ext1; dsimp; omega
      · intro u _; ext1; dsimp; omega

/-- Top-half card equivalence: #{i : Fin (2m) | i.val < m ∧ P i} = #{v : Fin m | P ⟨v.val, _⟩} -/
private lemma card_filter_top_half {m : ℕ} (P : Fin (2 * m) → Prop) [DecidablePred P] :
    ((Finset.univ.filter (fun i : Fin (2 * m) ↦ (i : ℕ) < m)).filter P).card =
    (Finset.univ.filter (fun v : Fin m ↦ P ⟨v.val, by omega⟩)).card := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [Finset.filter_filter]
    apply Finset.card_nbij'
      (fun i ↦ ⟨i.val % m, Nat.mod_lt _ hm⟩)
      (fun v ↦ ⟨v.val, by omega⟩)
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      convert hi.2 using 1; ext1; exact Nat.mod_eq_of_lt hi.1
    · intro v hv
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact ⟨v.isLt, hv⟩
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      ext1; exact Nat.mod_eq_of_lt hi.1
    · intro v _; ext1; exact Nat.mod_eq_of_lt v.isLt

/-- If s·(m+s-k) ≤ β²m², then s ≤ k/2 + βm.
    This is the arithmetic core of the expander → halver proof:
    the product bound on top-1s × bottom-0s implies the halver inequality. -/
private lemma quadratic_halver_bound {s k m β : ℝ}
    (hs : 0 ≤ s) (hm : 0 ≤ m) (hk : 0 ≤ k) (hksm : k - s ≤ m) (hkm : k ≤ 2 * m)
    (hβ : 0 ≤ β) (hbound : s * (m + s - k) ≤ β ^ 2 * m ^ 2) :
    s ≤ k / 2 + β * m := by
  by_contra h
  push_neg at h
  have hδ : 0 < s - k / 2 - β * m := by linarith
  have : s * (m + s - k) =
      β ^ 2 * m ^ 2 + β * m ^ 2 + k * (2 * m - k) / 4 +
      (s - k / 2 - β * m) * (m * (1 + 2 * β)) +
      (s - k / 2 - β * m) ^ 2 := by ring
  have h1 : 0 ≤ β * m ^ 2 := by positivity
  have h2 : 0 ≤ k * (2 * m - k) / 4 := by nlinarith
  have h3 : 0 ≤ (s - k / 2 - β * m) * (m * (1 + 2 * β)) := by
    apply mul_nonneg hδ.le; nlinarith
  have h4 : 0 < (s - k / 2 - β * m) ^ 2 := by positivity
  linarith

theorem expander_gives_halver (m d : ℕ) (G : RegularGraph m d)
    (β : ℝ) (hβ : spectralGap G ≤ β) :
    ∃ (net : ComparatorNetwork (2 * m)),
      IsEpsilonHalver net β ∧ net.size ≤ m * d := by
  -- Construct the network
  refine ⟨⟨bipartiteComparators G⟩, ?_, ?_⟩
  · -- Halver property: bipartite comparator network is a β-halver
    intro inp w topHalf onesInTop totalOnes
    -- w := exec inp, topHalf := filter(< 2*m/2), onesInTop := card, totalOnes := card
    -- Goal: (onesInTop : ℝ) ≤ totalOnes / 2 + β * (↑(2 * m) / 2)
    -- Handle m = 0
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · -- Simplify ↑(2 * m) / 2 to ↑m in the goal
      have h2m_real : (↑(2 * m) : ℝ) / 2 = ↑m := by push_cast; ring
      rw [h2m_real]
      -- Bridge: topHalf uses 2*m/2, which equals m
      have h2m_div : 2 * m / 2 = m := by omega
      have h_topHalf : topHalf = Finset.univ.filter (fun i : Fin (2 * m) ↦ (i : ℕ) < m) := by
        show Finset.univ.filter (fun i : Fin (2 * m) ↦ (i : ℕ) < 2 * m / 2) = _
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      -- S = top 1s, T' = bottom 0s (in G's vertex space Fin m)
      set S := Finset.univ.filter (fun v : Fin m ↦ w ⟨v.val, by omega⟩ = true)
      set T' := Finset.univ.filter (fun u : Fin m ↦ w ⟨m + u.val, by omega⟩ = false)
      -- (1) onesInTop = S.card
      have h_onesInTop : onesInTop = S.card := by
        show (topHalf.filter (fun i ↦ w i = true)).card = S.card
        rw [h_topHalf]
        exact card_filter_top_half (fun i ↦ w i = true)
      -- (2) totalOnes = S.card + onesInBot
      set onesInBot := (Finset.univ.filter
        (fun u : Fin m ↦ w ⟨m + u.val, by omega⟩ = true)).card
      have h_totalOnes : totalOnes = S.card + onesInBot := by
        show (Finset.univ.filter (fun i : Fin (2 * m) ↦ w i = true)).card = S.card + onesInBot
        exact card_filter_fin_double (fun i ↦ w i = true)
      -- (3) onesInBot + T'.card = m (partition of Fin m)
      have h_bot_part : onesInBot + T'.card = m := by
        have h := Finset.card_filter_add_card_filter_not
          (fun u : Fin m ↦ w ⟨m + u.val, by omega⟩ = true)
          (s := (Finset.univ : Finset (Fin m)))
        simp only [Finset.card_univ, Fintype.card_fin] at h
        -- h : #{true} + #{¬true} = m, need: onesInBot + T'.card = m
        -- T' uses (=false), complement uses ¬(=true); bridge via Bool.not_eq_true'
        suffices hsuff : T' = Finset.univ.filter
            (fun u : Fin m ↦ ¬(w ⟨m + u.val, by omega⟩ = true)) by
          rw [hsuff]; exact h
        show Finset.univ.filter (fun u : Fin m ↦ w ⟨m + u.val, by omega⟩ = false) =
          Finset.univ.filter (fun u : Fin m ↦ ¬(w ⟨m + u.val, by omega⟩ = true))
        ext1 u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        cases w ⟨m + u.val, by omega⟩ <;> decide
      -- Finset cardinality bounds for S and onesInBot
      have h_onesInBot_le : onesInBot ≤ m := by
        calc onesInBot ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
          _ = m := by simp
      have h_S_le : S.card ≤ m := by
        calc S.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
          _ = m := by simp
      -- (4) No edges from S to T'
      have h_no_edge : ∀ v ∈ S, ∀ p : Fin d, G.neighbor v p ∉ T' := by
        intro v hv p hmem
        simp only [S, T', Finset.mem_filter, Finset.mem_univ, true_and] at hv hmem
        -- hv : w ⟨v.val, _⟩ = true, hmem : w ⟨m + (G.nbr v p).val, _⟩ = false
        -- exec_bipartite_edge_mono gives w[v] ≤ w[m + nbr] (definitionally via exec)
        have h_le : w ⟨v.val, by omega⟩ ≤ w ⟨m + (G.neighbor v p).val, by omega⟩ :=
          exec_bipartite_edge_mono G inp v p
        rw [hv, hmem] at h_le
        exact absurd h_le (by decide)
      -- (5) Edge sum = 0
      have h_edge_zero : ∑ v ∈ S, (Finset.univ.filter
          (fun i : Fin d ↦ G.neighbor v i ∈ T')).card = 0 := by
        apply Finset.sum_eq_zero; intro v hv
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro p _; exact h_no_edge v hv p
      -- (6) Mixing lemma → product bound
      have h_prod_bound : (↑S.card : ℝ) * ↑T'.card ≤ β ^ 2 * ↑m ^ 2 := by
        have h_mix := expander_mixing_lemma G S T'
        simp only [h_edge_zero, Nat.cast_zero, zero_div, zero_sub, abs_neg] at h_mix
        rw [abs_of_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          (Nat.cast_nonneg _))] at h_mix
        have h_β_nonneg : (0 : ℝ) ≤ β := le_trans (spectralGap_nonneg G) hβ
        exact div_sqrt_to_sq_bound
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          (by positivity : (0 : ℝ) < ↑m) h_β_nonneg
          (h_mix.trans (mul_le_mul_of_nonneg_right hβ (Real.sqrt_nonneg _)))
      -- (7) Apply quadratic halver bound
      rw [h_onesInTop, h_totalOnes]
      -- Goal: (↑#S : ℝ) ≤ (↑#S + ↑onesInBot) / 2 + β * ↑m
      have h_β_nonneg : (0 : ℝ) ≤ β := le_trans (spectralGap_nonneg G) hβ
      have h_T'_eq : (↑T'.card : ℝ) = ↑m - ↑onesInBot := by
        have : (↑onesInBot : ℝ) + ↑T'.card = ↑m := by exact_mod_cast h_bot_part
        linarith
      apply quadratic_halver_bound
        (Nat.cast_nonneg S.card) (Nat.cast_nonneg m)
        (Nat.cast_nonneg (S.card + onesInBot))
        (by simp only [Nat.cast_add]
            have : (↑onesInBot : ℝ) ≤ ↑m := by exact_mod_cast h_onesInBot_le
            linarith)
        (by simp only [Nat.cast_add]
            have : (↑S.card : ℝ) ≤ ↑m := by exact_mod_cast h_S_le
            have : (↑onesInBot : ℝ) ≤ ↑m := by exact_mod_cast h_onesInBot_le
            linarith)
        h_β_nonneg
      -- hbound: ↑S.card * (↑m + ↑S.card - ↑(S.card + onesInBot)) ≤ β² * ↑m²
      -- Expand ↑(S.card + onesInBot) to ↑S.card + ↑onesInBot
      push_cast
      -- Now: ↑S.card * (↑m + ↑S.card - (↑S.card + ↑onesInBot)) ≤ β² * ↑m²
      have : (↑m : ℝ) + ↑S.card - (↑S.card + ↑onesInBot) = ↑T'.card := by linarith [h_T'_eq]
      rw [this]
      exact h_prod_bound
  · -- Size bound
    simp only [ComparatorNetwork.size]
    exact le_of_eq (bipartiteComparators_length G)

/-- Merge two sorted halves using iterated ε-halvers.
    After k rounds of ε-halving, the "unsortedness" decreases
    geometrically: at most (2ε)^k · n elements are out of place. -/
def epsHalverMerge (n : ℕ) (ε : ℝ) (k : ℕ)
    (halver : ComparatorNetwork n) : ComparatorNetwork n :=
  { comparators := (List.replicate k halver.comparators).flatten }


/-! **Top/Bottom Half Partitioning** -/

/-- Top half: positions with index < n/2 -/
def topHalf (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i ↦ (i : ℕ) < n / 2)

/-- Bottom half: positions with index ≥ n/2 -/
def bottomHalf (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i ↦ n / 2 ≤ (i : ℕ))

/-- Top and bottom halves cover all positions -/
lemma topHalf_union_bottomHalf (n : ℕ) :
    topHalf n ∪ bottomHalf n = Finset.univ := by
  ext i
  simp [topHalf, bottomHalf]
  omega

/-- Top and bottom halves are disjoint -/
lemma topHalf_disjoint_bottomHalf (n : ℕ) :
    (topHalf n ∩ bottomHalf n) = ∅ := by
  ext i
  simp [topHalf, bottomHalf]

/-- Cardinality of top half -/
lemma card_topHalf (n : ℕ) : (topHalf n).card = n / 2 := by
  by_cases hn : n = 0
  · subst hn; simp [topHalf]
  · have hn2 : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) one_lt_two
    have : topHalf n = Finset.Iio ⟨n / 2, hn2⟩ := by
      ext ⟨i, hi⟩
      simp only [topHalf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio,
        Fin.lt_iff_val_lt_val]
    rw [this, Fin.card_Iio]

/-- Cardinality of bottom half -/
lemma card_bottomHalf (n : ℕ) : (bottomHalf n).card = n - n / 2 := by
  have h_union := topHalf_union_bottomHalf n
  have h_disj : Disjoint (topHalf n) (bottomHalf n) :=
    Finset.disjoint_iff_inter_eq_empty.mpr (topHalf_disjoint_bottomHalf n)
  have h_card := Finset.card_union_of_disjoint h_disj
  rw [h_union, Finset.card_univ, Fintype.card_fin, card_topHalf] at h_card
  omega

/-! **Halver Composition** -/

/-- An ε-sorted vector: at most εn elements are not in their
    correct sorted position. -/
def IsEpsilonSorted {n : ℕ} (v : Fin n → Bool) (ε : ℝ) : Prop :=
  ∃ (w : Fin n → Bool), Monotone w ∧
    ((Finset.univ.filter (fun i ↦ v i ≠ w i)).card : ℝ) ≤ ε * n

/-! **Basic Properties of IsEpsilonSorted** -/

/-- Witness extraction helper -/
lemma IsEpsilonSorted.exists_witness {n : ℕ} {v : Fin n → Bool} {ε : ℝ}
    (h : IsEpsilonSorted v ε) :
    ∃ (w : Fin n → Bool), Monotone w ∧
      ((Finset.univ.filter (fun i ↦ v i ≠ w i)).card : ℝ) ≤ ε * n :=
  h

/-- Monotone Boolean sequences have the pattern 0* 1* (zeros then ones) -/
lemma Monotone.bool_pattern {n : ℕ} (w : Fin n → Bool) (hw : Monotone w) :
    ∃ k : ℕ, (∀ i : Fin n, (i : ℕ) < k → w i = false) ∧
             (∀ i : Fin n, k ≤ (i : ℕ) → w i = true) := by
  -- k = number of false values = size of the downward-closed false set
  use (Finset.univ.filter (fun i : Fin n ↦ w i = false)).card
  set k := (Finset.univ.filter (fun i : Fin n ↦ w i = false)).card
  constructor
  · -- For i.val < k: w i = false
    intro ⟨i, hi⟩ h_lt
    by_contra h_not
    have h_true : w ⟨i, hi⟩ = true := by
      match h : w ⟨i, hi⟩ with
      | true => rfl
      | false => exact absurd h h_not
    -- Every j ≥ i has w j = true (by monotonicity)
    have h_above : ∀ j : Fin n, i ≤ j.val → w j = true := by
      intro ⟨j, hj⟩ h_ij
      have := hw (show (⟨i, hi⟩ : Fin n) ≤ ⟨j, hj⟩ from h_ij)
      rw [h_true] at this
      match h : w ⟨j, hj⟩ with
      | true => rfl
      | false => rw [h] at this; exact absurd this (by decide)
    -- So false set ⊆ {j | j.val < i}
    have h_sub : Finset.univ.filter (fun j : Fin n ↦ w j = false) ⊆
        Finset.Iio ⟨i, hi⟩ := by
      intro ⟨j, hj⟩ hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      simp only [Finset.mem_Iio, Fin.lt_iff_val_lt_val]
      by_contra h_ge; push_neg at h_ge
      exact absurd (h_above ⟨j, hj⟩ h_ge) (by simp [hm])
    -- Card of false set ≤ card of Iio = i
    have := Finset.card_le_card h_sub
    rw [Fin.card_Iio] at this; omega
  · -- For k ≤ i.val: w i = true
    intro ⟨i, hi⟩ h_ge
    by_contra h_not
    have h_false : w ⟨i, hi⟩ = false := by
      match h : w ⟨i, hi⟩ with
      | false => rfl
      | true => exact absurd h h_not
    -- Every j ≤ i has w j = false (by monotonicity)
    have h_below : ∀ j : Fin n, j.val ≤ i → w j = false := by
      intro ⟨j, hj⟩ h_ji
      have := hw (show (⟨j, hj⟩ : Fin n) ≤ ⟨i, hi⟩ from h_ji)
      rw [h_false] at this
      match h : w ⟨j, hj⟩ with
      | false => rfl
      | true => rw [h] at this; exact absurd this (by decide)
    -- So Iic ⟨i, hi⟩ ⊆ false set
    have h_sub : Finset.Iic ⟨i, hi⟩ ⊆
        Finset.univ.filter (fun j : Fin n ↦ w j = false) := by
      intro ⟨j, hj⟩ hm
      simp only [Finset.mem_Iic, Fin.le_iff_val_le_val] at hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h_below ⟨j, hj⟩ hm
    -- Card of Iic = i + 1 ≤ card of false set = k
    have := Finset.card_le_card h_sub
    rw [Fin.card_Iic] at this; omega

/-- Relaxation: if ε₁ ≤ ε₂, then ε₁-sorted implies ε₂-sorted -/
lemma IsEpsilonSorted.mono {n : ℕ} {v : Fin n → Bool} {ε₁ ε₂ : ℝ}
    (h : IsEpsilonSorted v ε₁) (hle : ε₁ ≤ ε₂) :
    IsEpsilonSorted v ε₂ := by
  obtain ⟨w, hw_mono, hw_card⟩ := h
  refine ⟨w, hw_mono, ?_⟩
  calc ((Finset.univ.filter (fun i ↦ v i ≠ w i)).card : ℝ)
      ≤ ε₁ * n := hw_card
    _ ≤ ε₂ * n := by apply mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)

/-- Every sequence is trivially 1-sorted -/
lemma isEpsilonSorted_one {n : ℕ} (v : Fin n → Bool) :
    IsEpsilonSorted v 1 := by
  -- Use the all-false sequence as witness
  refine ⟨fun _ ↦ false, ?_, ?_⟩
  · -- Constant false function is monotone
    intro a b _
    rfl
  · -- At most n positions can differ
    calc ((Finset.univ.filter (fun i ↦ v i ≠ false)).card : ℝ)
        ≤ Finset.univ.card := by
          exact_mod_cast Finset.card_mono (Finset.filter_subset _ _)
      _ = Fintype.card (Fin n) := by simp
      _ = n := by simp
      _ = 1 * n := by ring
