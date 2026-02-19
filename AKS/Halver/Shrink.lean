/-
  # Shrinking Bipartite Halvers

  Restricts a bipartite halver on 2M wires to 2n wires (n ≤ M), keeping only
  comparators where both endpoints are in the first n wires per half.

  The construction is purely about comparator networks — no graph theory needed.
  The quality analysis uses the padding argument: running the shrunk halver on
  input τ is equivalent to running the big halver on a padded input (M-n copies
  of -∞ in top, +∞ in bottom) and projecting to real wires. Bipartiteness
  ensures padding elements are invisible to all comparators.

  **Quality:** For segment k, the misplacement count is at most ε · (M - n + k).
  The uniform `IsEpsilonHalver` parameter is ε · (M - n + 1). The main halving
  bound (k = n) gives ε · M, i.e., quality ε · M / n as a fraction of n.
-/

import AKS.Halver.Defs

open Finset BigOperators


/-! **Bipartite Networks** -/

/-- A network on `2 * M` wires is bipartite: every comparator connects
    a top wire (`i.val < M`) to a bottom wire (`M ≤ j.val`). -/
def ComparatorNetwork.IsBipartite {M : ℕ} (net : ComparatorNetwork (2 * M)) : Prop :=
  ∀ c ∈ net.comparators, c.i.val < M ∧ M ≤ c.j.val


/-! **Shrinking Construction** -/

/-- Restrict a halver on `2 * M` wires to `2 * n` wires (`n ≤ M`).
    Keeps comparators `(i, j)` where `i < n` and `j ∈ [M, M + n)`,
    renumbering bottom wires `j ↦ n + (j - M)`. Comparators outside
    this range (including any non-bipartite ones) are dropped. -/
def shrinkHalver {M : ℕ} (net : ComparatorNetwork (2 * M)) (n : ℕ) (_hn : n ≤ M) :
    ComparatorNetwork (2 * n) :=
  { comparators := net.comparators.filterMap fun c =>
      if h : c.i.val < n ∧ M ≤ c.j.val ∧ c.j.val < M + n then
        some ⟨⟨c.i.val, by omega⟩,
              ⟨n + (c.j.val - M), by omega⟩,
              by simp [Fin.lt_def]; omega⟩
      else none }

private theorem filterMap_self {α : Type*} (f : α → Option α) (l : List α)
    (hf : ∀ x ∈ l, f x = some x) : l.filterMap f = l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    have ha := hf a (List.mem_cons.mpr (Or.inl rfl))
    simp only [List.filterMap_cons, ha]
    congr 1
    exact ih (fun x hx => hf x (List.mem_cons.mpr (Or.inr hx)))

/-- Shrinking to the same size is the identity (for bipartite networks). -/
theorem shrinkHalver_self {M : ℕ} (net : ComparatorNetwork (2 * M))
    (hbip : net.IsBipartite) :
    shrinkHalver net M le_rfl = net := by
  simp only [shrinkHalver]
  congr 1
  apply filterMap_self
  intro c hc
  cases c with
  | mk ci cj ch =>
    have hi : ci.val < M := (hbip ⟨ci, cj, ch⟩ hc).1
    have hj : M ≤ cj.val := (hbip ⟨ci, cj, ch⟩ hc).2
    have hguard : ci.val < M ∧ M ≤ cj.val ∧ cj.val < M + M := ⟨hi, hj, by omega⟩
    simp only [dif_pos hguard, Option.some.injEq, Comparator.mk.injEq, Fin.ext_iff]
    exact ⟨trivial, by omega⟩

/-- The shrunk halver is bipartite. -/
theorem shrinkHalver_isBipartite {M : ℕ} (net : ComparatorNetwork (2 * M))
    (n : ℕ) (hn : n ≤ M) :
    (shrinkHalver net n hn).IsBipartite := by
  intro c hc
  simp only [shrinkHalver, List.mem_filterMap] at hc
  obtain ⟨c', _, hf⟩ := hc
  by_cases h : c'.i.val < n ∧ M ≤ c'.j.val ∧ c'.j.val < M + n
  · rw [dif_pos h] at hf
    simp only [Option.some.injEq] at hf
    subst hf
    exact ⟨h.1, Nat.le_add_right n _⟩
  · rw [dif_neg h] at hf; exact absurd hf nofun

/-- The shrunk halver has at most as many comparators as the original. -/
theorem shrinkHalver_size_le {M : ℕ} (net : ComparatorNetwork (2 * M))
    (n : ℕ) (hn : n ≤ M) :
    (shrinkHalver net n hn).size ≤ net.size := by
  exact List.length_filterMap_le _ _


/-! **Padding Construction** -/

/-- Comparator is a no-op when values are already in order. -/
private theorem apply_eq_of_le {m : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator m) (w : Fin m → α) (h : w c.i ≤ w c.j) : c.apply w = w := by
  ext k; unfold Comparator.apply
  by_cases hki : k = c.i
  · subst hki; rw [if_pos rfl, min_eq_left h]
  · rw [if_neg hki]
    by_cases hkj : k = c.j
    · subst hkj; rw [if_pos rfl, max_eq_right h]
    · rw [if_neg hkj]

/-- Padded input: shifts real wire values by `M - n`, assigns extreme phantom values.
    - Real-top `[0, n)`: output `(M-n) + v(i)` ∈ `[M-n, M+n)`
    - Phantom-top `[n, M)`: output `i - n` ∈ `[0, M-n)`
    - Real-bottom `[M, M+n)`: output `(M-n) + v(n + (i-M))` ∈ `[M-n, M+n)`
    - Phantom-bottom `[M+n, 2M)`: output `i` ∈ `[M+n, 2M)` -/
private def padFun {M n : ℕ} (hnM : n ≤ M) (v : Fin (2 * n) → Fin (2 * n))
    (i : Fin (2 * M)) : Fin (2 * M) :=
  if h1 : i.val < n then
    ⟨(M - n) + (v ⟨i.val, by omega⟩).val, by have := (v ⟨i.val, by omega⟩).isLt; omega⟩
  else if _ : i.val < M then
    ⟨i.val - n, by omega⟩
  else if h3 : i.val < M + n then
    ⟨(M - n) + (v ⟨n + (i.val - M), by omega⟩).val,
     by have := (v ⟨n + (i.val - M), by omega⟩).isLt; omega⟩
  else
    ⟨i.val, i.isLt⟩

/-- Value-level lemma for padFun in the real-top region. -/
private theorem padFun_val_rt {M n : ℕ} (hnM : n ≤ M) (v : Fin (2 * n) → Fin (2 * n))
    (a : Fin (2 * M)) (ha : a.val < n) :
    (padFun hnM v a).val = (M - n) + (v ⟨a.val, by omega⟩).val := by
  simp [padFun, ha]

/-- Value-level lemma for padFun in the phantom-top region. -/
private theorem padFun_val_pt {M n : ℕ} (hnM : n ≤ M) (v : Fin (2 * n) → Fin (2 * n))
    (a : Fin (2 * M)) (ha1 : ¬a.val < n) (ha2 : a.val < M) :
    (padFun hnM v a).val = a.val - n := by
  simp [padFun, ha1, ha2]

/-- Value-level lemma for padFun in the real-bottom region. -/
private theorem padFun_val_rb {M n : ℕ} (hnM : n ≤ M) (v : Fin (2 * n) → Fin (2 * n))
    (a : Fin (2 * M)) (ha1 : ¬a.val < n) (ha2 : ¬a.val < M) (ha3 : a.val < M + n) :
    (padFun hnM v a).val = (M - n) + (v ⟨n + (a.val - M), by omega⟩).val := by
  simp [padFun, ha1, ha2, ha3]

/-- Value-level lemma for padFun in the phantom-bottom region. -/
private theorem padFun_val_pb {M n : ℕ} (hnM : n ≤ M) (v : Fin (2 * n) → Fin (2 * n))
    (a : Fin (2 * M)) (ha1 : ¬a.val < n) (ha2 : ¬a.val < M) (ha3 : ¬a.val < M + n) :
    (padFun hnM v a).val = a.val := by
  simp [padFun, ha1, ha2, ha3]

private theorem padFun_injective {M n : ℕ} (hnM : n ≤ M)
    (v : Equiv.Perm (Fin (2 * n))) : Function.Injective (padFun hnM v) := by
  intro a b hab
  have hv : (padFun hnM v a).val = (padFun hnM v b).val := congr_arg Fin.val hab
  ext
  -- Case analysis on region of a, then region of b
  by_cases ha1 : a.val < n
  · rw [padFun_val_rt hnM v a ha1] at hv
    by_cases hb1 : b.val < n
    · -- both real-top: use v.injective
      rw [padFun_val_rt hnM v b hb1] at hv
      have h1 : (v ⟨a.val, by omega⟩).val = (v ⟨b.val, by omega⟩).val := by omega
      have := congr_arg Fin.val (v.injective (Fin.ext h1))
      simp at this; exact this
    · by_cases hb2 : b.val < M
      · rw [padFun_val_pt hnM v b hb1 hb2] at hv
        have := (v ⟨a.val, by omega⟩).isLt; omega
      · by_cases hb3 : b.val < M + n
        · rw [padFun_val_rb hnM v b hb1 hb2 hb3] at hv
          have h1 : (v ⟨a.val, by omega⟩).val = (v ⟨n + (b.val - M), by omega⟩).val := by omega
          have := congr_arg Fin.val (v.injective (Fin.ext h1))
          simp at this; omega
        · rw [padFun_val_pb hnM v b hb1 hb2 hb3] at hv
          have := (v ⟨a.val, by omega⟩).isLt; omega
  · by_cases ha2 : a.val < M
    · rw [padFun_val_pt hnM v a ha1 ha2] at hv
      by_cases hb1 : b.val < n
      · rw [padFun_val_rt hnM v b hb1] at hv
        have := (v ⟨b.val, by omega⟩).isLt; omega
      · by_cases hb2 : b.val < M
        · rw [padFun_val_pt hnM v b hb1 hb2] at hv; omega
        · by_cases hb3 : b.val < M + n
          · rw [padFun_val_rb hnM v b hb1 hb2 hb3] at hv
            have := (v ⟨n + (b.val - M), by omega⟩).isLt; omega
          · rw [padFun_val_pb hnM v b hb1 hb2 hb3] at hv; omega
    · by_cases ha3 : a.val < M + n
      · rw [padFun_val_rb hnM v a ha1 ha2 ha3] at hv
        by_cases hb1 : b.val < n
        · rw [padFun_val_rt hnM v b hb1] at hv
          have h1 : (v ⟨n + (a.val - M), by omega⟩).val = (v ⟨b.val, by omega⟩).val := by omega
          have := congr_arg Fin.val (v.injective (Fin.ext h1))
          simp at this; omega
        · by_cases hb2 : b.val < M
          · rw [padFun_val_pt hnM v b hb1 hb2] at hv
            have := (v ⟨n + (a.val - M), by omega⟩).isLt; omega
          · by_cases hb3 : b.val < M + n
            · rw [padFun_val_rb hnM v b hb1 hb2 hb3] at hv
              have h1 : (v ⟨n + (a.val - M), by omega⟩).val = (v ⟨n + (b.val - M), by omega⟩).val := by omega
              have := congr_arg Fin.val (v.injective (Fin.ext h1))
              simp at this; omega
            · rw [padFun_val_pb hnM v b hb1 hb2 hb3] at hv
              have := (v ⟨n + (a.val - M), by omega⟩).isLt; omega
      · rw [padFun_val_pb hnM v a ha1 ha2 ha3] at hv
        by_cases hb1 : b.val < n
        · rw [padFun_val_rt hnM v b hb1] at hv
          have := (v ⟨b.val, by omega⟩).isLt; omega
        · by_cases hb2 : b.val < M
          · rw [padFun_val_pt hnM v b hb1 hb2] at hv; omega
          · by_cases hb3 : b.val < M + n
            · rw [padFun_val_rb hnM v b hb1 hb2 hb3] at hv
              have := (v ⟨n + (b.val - M), by omega⟩).isLt; omega
            · rw [padFun_val_pb hnM v b hb1 hb2 hb3] at hv; omega

private noncomputable def padPerm {M n : ℕ} (hnM : n ≤ M) (v : Equiv.Perm (Fin (2 * n))) :
    Equiv.Perm (Fin (2 * M)) :=
  Equiv.ofBijective (padFun hnM v)
    ⟨padFun_injective hnM v, Finite.injective_iff_surjective.mp (padFun_injective hnM v)⟩

/-- The shrink guard: decides which comparators survive shrinking. -/
private def shrinkGuard {M : ℕ} (n : ℕ) (c : Comparator (2 * M)) :
    Option (Comparator (2 * n)) :=
  if h : c.i.val < n ∧ M ≤ c.j.val ∧ c.j.val < M + n then
    some ⟨⟨c.i.val, by omega⟩, ⟨n + (c.j.val - M), by omega⟩,
          by simp [Fin.lt_def]; omega⟩
  else none

private lemma fin_val_min {N : ℕ} (a b : Fin N) : (min a b).val = min a.val b.val := by
  simp only [min_def, Fin.le_def]; split <;> rfl

private lemma fin_val_max {N : ℕ} (a b : Fin N) : (max a b).val = max a.val b.val := by
  simp only [max_def, Fin.le_def]; split <;> rfl

/-- Full padding invariant: all four wire-region properties are maintained through
    a list of bipartite comparators. -/
private theorem pad_invariant {M n : ℕ} (hnM : n ≤ M)
    (cs : List (Comparator (2 * M)))
    (hbip : ∀ c ∈ cs, c.i.val < M ∧ M ≤ c.j.val)
    (V : Fin (2 * M) → Fin (2 * M)) (vs : Fin (2 * n) → Fin (2 * n))
    (h_rt : ∀ (i : ℕ) (_ : i < n), (V ⟨i, by omega⟩).val = (M - n) + (vs ⟨i, by omega⟩).val)
    (h_rb : ∀ (j : ℕ) (_ : j < n), (V ⟨M + j, by omega⟩).val = (M - n) + (vs ⟨n + j, by omega⟩).val)
    (h_pt : ∀ (i : ℕ) (_ : i < M), n ≤ i → (V ⟨i, by omega⟩).val < M - n)
    (h_pb : ∀ (i : ℕ) (_ : i < 2 * M), M + n ≤ i → M + n ≤ (V ⟨i, by omega⟩).val) :
    let V' := cs.foldl (fun acc c => c.apply acc) V
    let vs' := (cs.filterMap (shrinkGuard n)).foldl (fun acc c => c.apply acc) vs
    (∀ (i : ℕ) (_ : i < n), (V' ⟨i, by omega⟩).val = (M - n) + (vs' ⟨i, by omega⟩).val) ∧
    (∀ (j : ℕ) (_ : j < n), (V' ⟨M + j, by omega⟩).val = (M - n) + (vs' ⟨n + j, by omega⟩).val) ∧
    (∀ (i : ℕ) (_ : i < M), n ≤ i → (V' ⟨i, by omega⟩).val < M - n) ∧
    (∀ (i : ℕ) (_ : i < 2 * M), M + n ≤ i → M + n ≤ (V' ⟨i, by omega⟩).val) := by
  induction cs generalizing V vs with
  | nil => exact ⟨h_rt, h_rb, h_pt, h_pb⟩
  | cons c cs ih =>
    simp only [List.foldl_cons, List.filterMap_cons, shrinkGuard]
    have ⟨hci_top, hcj_bot⟩ := hbip c (.head cs)
    have hcs_bip := fun c' hc' => hbip c' (.tail c hc')
    by_cases hguard : c.i.val < n ∧ M ≤ c.j.val ∧ c.j.val < M + n
    · -- Both endpoints are real wires: comparator survives shrinking
      rw [dif_pos hguard]; simp only [List.foldl_cons]
      set c' : Comparator (2 * n) := ⟨⟨c.i.val, by omega⟩, ⟨n + (c.j.val - M), by omega⟩,
        by simp [Fin.lt_def]; omega⟩
      -- Key: V and vs have corresponding values at c.i/c.j and c'.i/c'.j
      have hVi : (V c.i).val = (M - n) + (vs c'.i).val := by
        have h := h_rt c.i.val hguard.1
        rwa [show (⟨c.i.val, by omega⟩ : Fin (2 * M)) = c.i from Fin.ext rfl] at h
      have hVj : (V c.j).val = (M - n) + (vs c'.j).val := by
        have h := h_rb (c.j.val - M) (by omega)
        have hj_eq : (⟨M + (c.j.val - M), by omega⟩ : Fin (2 * M)) = c.j := by
          ext; show M + (c.j.val - M) = c.j.val; omega
        rwa [hj_eq] at h
      refine ih hcs_bip (c.apply V) (c'.apply vs) ?_ ?_ ?_ ?_
      · -- h_rt: real-top wires
        intro i hi
        show (c.apply V ⟨i, by omega⟩).val = (M - n) + (c'.apply vs ⟨i, by omega⟩).val
        unfold Comparator.apply
        have hne_cj : (⟨i, by omega⟩ : Fin (2 * M)) ≠ c.j := by
          intro h; have := congr_arg Fin.val h; simp at this; omega
        have hne_c'j : (⟨i, by omega⟩ : Fin (2 * n)) ≠ c'.j := by
          intro h; have := congr_arg Fin.val h; simp [c'] at this; omega
        rw [if_neg hne_cj, if_neg hne_c'j]
        by_cases hii : (⟨i, by omega⟩ : Fin (2 * M)) = c.i
        · have hii' : (⟨i, by omega⟩ : Fin (2 * n)) = c'.i := by
            ext; simp [c']; exact congr_arg Fin.val hii
          rw [if_pos hii, if_pos hii']
          rw [fin_val_min, hVi, hVj, fin_val_min]; omega
        · have hii' : (⟨i, by omega⟩ : Fin (2 * n)) ≠ c'.i := by
            intro h; apply hii; ext; simp [c'] at h; exact h
          rw [if_neg hii, if_neg hii']
          exact h_rt i hi
      · -- h_rb: real-bottom wires
        intro j hj
        show (c.apply V ⟨M + j, by omega⟩).val = (M - n) + (c'.apply vs ⟨n + j, by omega⟩).val
        unfold Comparator.apply
        have hne_ci : (⟨M + j, by omega⟩ : Fin (2 * M)) ≠ c.i := by
          intro h; have := congr_arg Fin.val h; simp at this; omega
        have hne_c'i : (⟨n + j, by omega⟩ : Fin (2 * n)) ≠ c'.i := by
          intro h; have := congr_arg Fin.val h; simp [c'] at this; omega
        rw [if_neg hne_ci, if_neg hne_c'i]
        by_cases hjj : (⟨M + j, by omega⟩ : Fin (2 * M)) = c.j
        · have hjj' : (⟨n + j, by omega⟩ : Fin (2 * n)) = c'.j := by
            ext; simp [c']; have := congr_arg Fin.val hjj; simp at this; omega
          rw [if_pos hjj, if_pos hjj']
          rw [fin_val_max, hVi, hVj, fin_val_max]; omega
        · have hjj' : (⟨n + j, by omega⟩ : Fin (2 * n)) ≠ c'.j := by
            intro h; apply hjj; ext; simp [c'] at h; simp; omega
          rw [if_neg hjj, if_neg hjj']
          exact h_rb j hj
      · -- h_pt: phantom-top wires (comparator doesn't touch them)
        intro i hi hni
        show (c.apply V ⟨i, by omega⟩).val < M - n
        unfold Comparator.apply
        have hne_ci : (⟨i, by omega⟩ : Fin (2 * M)) ≠ c.i := by
          intro h; have := congr_arg Fin.val h; simp at this; omega
        have hne_cj : (⟨i, by omega⟩ : Fin (2 * M)) ≠ c.j := by
          intro h; have := congr_arg Fin.val h; simp at this; omega
        rw [if_neg hne_ci, if_neg hne_cj]
        exact h_pt i hi hni
      · -- h_pb: phantom-bottom wires (comparator doesn't touch them)
        intro i hi hni
        show M + n ≤ (c.apply V ⟨i, by omega⟩).val
        unfold Comparator.apply
        have hne_ci : (⟨i, by omega⟩ : Fin (2 * M)) ≠ c.i := by
          intro h; have := congr_arg Fin.val h; simp at this; omega
        have hne_cj : (⟨i, by omega⟩ : Fin (2 * M)) ≠ c.j := by
          intro h; have := congr_arg Fin.val h; simp at this; omega
        rw [if_neg hne_ci, if_neg hne_cj]
        exact h_pb i hi hni
    · -- Comparator involves a phantom wire: it's a no-op
      rw [dif_neg hguard]
      have h_noop : c.apply V = V := by
        apply apply_eq_of_le
        show V c.i ≤ V c.j; rw [Fin.le_def]
        -- Either c.i is phantom-top or c.j is phantom-bottom
        by_cases hci : c.i.val < n
        · -- c.i is real-top, c.j must be phantom-bottom (c.j.val ≥ M + n)
          have hcj : M + n ≤ c.j.val := by
            push_neg at hguard; exact hguard hci hcj_bot
          have hvi := h_rt c.i.val hci
          have hvj := h_pb c.j.val c.j.isLt hcj
          have := (vs ⟨c.i.val, by omega⟩).isLt
          rw [show (⟨c.i.val, by omega⟩ : Fin (2 * M)) = c.i from Fin.ext rfl] at hvi
          rw [show (⟨c.j.val, by omega⟩ : Fin (2 * M)) = c.j from Fin.ext rfl] at hvj
          omega
        · -- c.i is phantom-top: V(c.i) < M - n ≤ any real/phantom-bottom value
          have hci_ge : n ≤ c.i.val := Nat.le_of_not_lt hci
          have hvi := h_pt c.i.val hci_top hci_ge
          rw [show (⟨c.i.val, by omega⟩ : Fin (2 * M)) = c.i from Fin.ext rfl] at hvi
          -- V(c.j) ≥ M - n (whether real-bottom or phantom-bottom)
          by_cases hcj : c.j.val < M + n
          · have hvj := h_rb (c.j.val - M) (by omega)
            have hj_eq : (⟨M + (c.j.val - M), by omega⟩ : Fin (2 * M)) = c.j := by
              ext; show M + (c.j.val - M) = c.j.val; omega
            rw [hj_eq] at hvj
            have := (vs ⟨n + (c.j.val - M), by omega⟩).isLt; omega
          · push_neg at hcj
            have hvj := h_pb c.j.val c.j.isLt hcj
            rw [show (⟨c.j.val, by omega⟩ : Fin (2 * M)) = c.j from Fin.ext rfl] at hvj
            omega
      rw [h_noop]
      exact ih hcs_bip V vs h_rt h_rb h_pt h_pb


/-! **Quality Bounds** -/

/-- **Per-segment initial bound.** If the original is a bipartite ε-halver on
    `2 * M` wires, the shrunk halver on `2 * n` wires satisfies: at most
    `ε · (M - n + k)` bottom-half positions have output rank `< k`.

    Proof sketch: embed `Perm (Fin (2n))` into `Perm (Fin (2M))` by padding:
    - Phantom-top wires (positions `n..M-1`): smallest values (ranks `0..M-n-1`)
    - Real wires: middle values (ranks `M-n..M+n-1`)
    - Phantom-bottom wires (`M+n..2M-1`): largest values (ranks `M+n..2M-1`)

    Bipartiteness ensures: a comparator between a phantom wire and a real wire
    is always a no-op (phantom-top < real, real < phantom-bottom). So the big
    halver's output on real wires equals the shrunk halver's output. The big
    halver's segment bound at threshold `M - n + k` gives the result. -/
theorem shrinkHalver_initialBound {M : ℕ} (net : ComparatorNetwork (2 * M))
    (hbip : net.IsBipartite) (ε : ℝ) (hε : IsEpsilonHalver net ε)
    (n : ℕ) (_hn : 0 < n) (hnM : n ≤ M)
    (v : Equiv.Perm (Fin (2 * n))) (k : ℕ) (hk : k ≤ n) :
    ((univ.filter (fun pos : Fin (2 * n) ↦
        n ≤ rank pos ∧
        rank ((shrinkHalver net n hnM).exec v pos) < k)).card : ℝ) ≤
      ε * (↑M - ↑n + ↑k) := by
  -- Convert rank to val
  simp_rw [rank_fin_val]
  -- Set up the padded permutation on 2*M wires
  set V₀ := padFun hnM v
  -- The initial state satisfies the 4-part invariant (verified by unfolding padFun)
  have h_rt : ∀ (i : ℕ) (_ : i < n),
      (V₀ ⟨i, by omega⟩).val = (M - n) + (v ⟨i, by omega⟩).val :=
    fun i hi => by simp only [V₀, padFun, show i < n from hi, dif_pos]
  have h_rb : ∀ (j : ℕ) (_ : j < n),
      (V₀ ⟨M + j, by omega⟩).val = (M - n) + (v ⟨n + j, by omega⟩).val :=
    fun j hj => by
      have h := padFun_val_rb hnM (↑v) ⟨M + j, by omega⟩
        (show ¬(M + j < n) by omega) (show ¬(M + j < M) by omega) (show M + j < M + n by omega)
      simp only [V₀]; rw [h]; congr 3; ext; show n + (M + j - M) = n + j; omega
  have h_pt : ∀ (i : ℕ) (_ : i < M), n ≤ i → (V₀ ⟨i, by omega⟩).val < M - n :=
    fun i hi hni => by
      have h := padFun_val_pt hnM (↑v) ⟨i, by omega⟩ (show ¬(i < n) by omega) hi
      simp only [V₀]; rw [h]; show i - n < M - n; omega
  have h_pb : ∀ (i : ℕ) (_ : i < 2 * M), M + n ≤ i → M + n ≤ (V₀ ⟨i, by omega⟩).val :=
    fun i hi hni => by
      simp only [V₀, padFun]; split_ifs <;> omega
  -- Apply pad_invariant to get correspondence after full execution
  obtain ⟨_, hinv_rb, _, _⟩ :=
    pad_invariant hnM net.comparators hbip V₀ v h_rt h_rb h_pt h_pb
  -- The big halver's ε-bound at threshold K = M - n + k
  set K := M - n + k
  have hbig := (hε (padPerm hnM v)).1
  simp only [EpsilonInitialHalved, Fintype.card_fin, show 2 * M / 2 = M from by omega] at hbig
  simp_rw [rank_fin_val] at hbig
  have hbig_K := hbig K (show K ≤ M by omega)
  -- padPerm agrees with padFun as a function
  have hV_eq : (↑(padPerm hnM v) : Fin (2 * M) → Fin (2 * M)) = V₀ := rfl
  rw [hV_eq] at hbig_K
  -- Injection: shrunk filter card ≤ big filter card
  suffices h_inj :
      (univ.filter (fun pos : Fin (2 * n) ↦
        n ≤ pos.val ∧ ((shrinkHalver net n hnM).exec (↑v) pos).val < k)).card ≤
      (univ.filter (fun pos : Fin (2 * M) ↦
        M ≤ pos.val ∧ (net.exec V₀ pos).val < K)).card by
    exact_mod_cast le_trans (Nat.cast_le.mpr h_inj) hbig_K
  apply Finset.card_le_card_of_injOn
    (fun pos => ⟨M + (pos.val - n), by have := pos.isLt; omega⟩)
  · -- Maps into the big filter
    intro pos hpos
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
    obtain ⟨hpos_bot, hpos_out⟩ := hpos
    refine ⟨by omega, ?_⟩
    -- Use pad_invariant: exec_big at M+(pos.val-n) = (M-n) + exec_shrunk at pos
    have hcorr := hinv_rb (pos.val - n) (show pos.val - n < n by omega)
    have hfin : (⟨n + (pos.val - n), by omega⟩ : Fin (2 * n)) = pos := by
      ext; show n + (pos.val - n) = pos.val; omega
    -- Unfold exec in hypothesis and goal to match foldl forms
    unfold ComparatorNetwork.exec at hpos_out ⊢
    rw [show (shrinkHalver net n hnM).comparators =
        net.comparators.filterMap (shrinkGuard n) from rfl] at hpos_out
    rw [hfin] at hcorr
    -- hcorr: big foldl = (M-n) + shrunk foldl at pos
    -- hpos_out: shrunk foldl at pos < k
    omega
  · -- Injective
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    ext; show a.val = b.val
    have h : M + (a.val - n) = M + (b.val - n) := congr_arg Fin.val hab
    omega

/-- **Per-segment final bound** (dual of initial). -/
theorem shrinkHalver_finalBound {M : ℕ} (net : ComparatorNetwork (2 * M))
    (hbip : net.IsBipartite) (ε : ℝ) (hε : IsEpsilonHalver net ε)
    (n : ℕ) (_hn : 0 < n) (hnM : n ≤ M)
    (v : Equiv.Perm (Fin (2 * n))) (k : ℕ) (hk : k ≤ n) :
    ((univ.filter (fun pos : Fin (2 * n) ↦
        pos.val < n ∧
        2 * n - k ≤ ((shrinkHalver net n hnM).exec v pos).val)).card : ℝ) ≤
      ε * (↑M - ↑n + ↑k) := by
  -- Set up the padded permutation on 2*M wires
  set V₀ := padFun hnM v
  -- The initial state satisfies the 4-part invariant
  have h_rt : ∀ (i : ℕ) (_ : i < n),
      (V₀ ⟨i, by omega⟩).val = (M - n) + (v ⟨i, by omega⟩).val :=
    fun i hi => by simp only [V₀, padFun, show i < n from hi, dif_pos]
  have h_rb : ∀ (j : ℕ) (_ : j < n),
      (V₀ ⟨M + j, by omega⟩).val = (M - n) + (v ⟨n + j, by omega⟩).val :=
    fun j hj => by
      have h := padFun_val_rb hnM (↑v) ⟨M + j, by omega⟩
        (show ¬(M + j < n) by omega) (show ¬(M + j < M) by omega) (show M + j < M + n by omega)
      simp only [V₀]; rw [h]; congr 3; ext; show n + (M + j - M) = n + j; omega
  have h_pt : ∀ (i : ℕ) (_ : i < M), n ≤ i → (V₀ ⟨i, by omega⟩).val < M - n :=
    fun i hi hni => by
      have h := padFun_val_pt hnM (↑v) ⟨i, by omega⟩ (show ¬(i < n) by omega) hi
      simp only [V₀]; rw [h]; show i - n < M - n; omega
  have h_pb : ∀ (i : ℕ) (_ : i < 2 * M), M + n ≤ i → M + n ≤ (V₀ ⟨i, by omega⟩).val :=
    fun i hi hni => by
      simp only [V₀, padFun]; split_ifs <;> omega
  -- Apply pad_invariant to get correspondence after full execution
  obtain ⟨hinv_rt, _, _, _⟩ :=
    pad_invariant hnM net.comparators hbip V₀ v h_rt h_rb h_pt h_pb
  -- The big halver's final ε-bound at threshold K = M - n + k
  set K := M - n + k
  have hbig_K := ((hε (padPerm hnM v)).2).val_bound K (show K ≤ M by omega)
  -- padPerm agrees with padFun as a function
  have hV_eq : (↑(padPerm hnM v) : Fin (2 * M) → Fin (2 * M)) = V₀ := rfl
  rw [hV_eq] at hbig_K
  -- Injection: shrunk filter card ≤ big filter card
  suffices h_inj :
      (univ.filter (fun pos : Fin (2 * n) ↦
        pos.val < n ∧ 2 * n - k ≤ ((shrinkHalver net n hnM).exec (↑v) pos).val)).card ≤
      (univ.filter (fun pos : Fin (2 * M) ↦
        pos.val < M ∧ 2 * M - K ≤ (net.exec V₀ pos).val)).card by
    exact_mod_cast le_trans (Nat.cast_le.mpr h_inj) hbig_K
  apply Finset.card_le_card_of_injOn
    (fun pos => ⟨pos.val, by have := pos.isLt; omega⟩)
  · -- Maps into the big filter
    intro pos hpos
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
    obtain ⟨hpos_top, hpos_out⟩ := hpos
    refine ⟨by omega, ?_⟩
    -- Use pad_invariant h_rt: exec_big at pos.val = (M-n) + exec_shrunk at pos.val
    have hcorr := hinv_rt pos.val hpos_top
    -- Connect shrunk foldl at ⟨pos.val, _⟩ to shrunk exec at pos
    unfold ComparatorNetwork.exec at hpos_out ⊢
    rw [show (shrinkHalver net n hnM).comparators =
        net.comparators.filterMap (shrinkGuard n) from rfl] at hpos_out
    -- hcorr mentions ⟨pos.val, _⟩ : Fin(2n) which equals pos by proof irrelevance
    -- Convert via rfl-based rewrite
    have hfin : (⟨pos.val, by omega⟩ : Fin (2 * n)) = pos := by ext; rfl
    rw [hfin] at hcorr
    -- hcorr: big foldl val = (M-n) + shrunk foldl val at pos
    -- hpos_out: 2n-k ≤ shrunk foldl val at pos
    -- Goal: 2M-K ≤ big foldl val (where K=M-n+k, so 2M-K=M+n-k)
    omega
  · -- Injective (same val → same Fin)
    intro a _ b _ hab
    simp only [Fin.mk.injEq] at hab
    exact Fin.ext hab

/-- **Uniform `IsEpsilonHalver` bound:** `ε' = ε · (M - n + 1)`.

    This is the tightest uniform bound: at `k = 1`, the per-segment bound gives
    `ε · (M - n + 1)`, and `ε · (M - n + k) ≤ ε · (M - n + 1) · k` for `k ≥ 1`.

    **Note:** `ε'` grows with `M - n`. The main halving bound (k = n) gives
    the tighter `ε · M` (i.e., quality `ε · M / n` as a fraction of `n`). -/
private lemma mk_epsilonFinalHalved {m : ℕ}
    {w : Fin (2 * m) → Fin (2 * m)} {ε : ℝ}
    (h : ∀ k : ℕ, k ≤ m →
      ((Finset.univ.filter (fun pos : Fin (2 * m) ↦
          pos.val < m ∧ 2 * m - k ≤ (w pos).val)).card : ℝ) ≤ ε * ↑k) :
    EpsilonFinalHalved w ε := by
  unfold EpsilonFinalHalved EpsilonInitialHalved
  simp only [Fintype.card_orderDual, Fintype.card_fin,
    show 2 * m / 2 = m from by omega]
  intro k hk
  -- Bridge: OD filter card = val filter card (reverse of val_bound)
  suffices hsuff : (univ.filter (fun pos : (Fin (2 * m))ᵒᵈ ↦
      m ≤ @rank (Fin (2 * m))ᵒᵈ _ _ pos ∧
      @rank (Fin (2 * m))ᵒᵈ _ _ (w pos) < k)).card =
    (univ.filter (fun pos : Fin (2 * m) ↦
      pos.val < m ∧ 2 * m - k ≤ (w pos).val)).card by
    exact_mod_cast hsuff ▸ (h k hk)
  apply Finset.card_nbij'
    (fun x ↦ OrderDual.ofDual x) (fun x ↦ OrderDual.toDual x)
  · -- OD → val: unfold rank to val conditions
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨h1, h2⟩ := hx
    have hr1 : @rank (Fin (2 * m))ᵒᵈ _ _ x =
        2 * m - 1 - (OrderDual.ofDual x).val := rank_fin_od x
    have hr2 : @rank (Fin (2 * m))ᵒᵈ _ _ (w x) =
        2 * m - 1 - (w (OrderDual.ofDual x)).val := by
      show @rank (Fin (2 * m))ᵒᵈ _ _ (w x) = _
      exact rank_fin_od (w x)
    rw [hr1] at h1; rw [hr2] at h2
    have hx_lt := (OrderDual.ofDual x).isLt
    have hwx_lt := (w (OrderDual.ofDual x)).isLt
    constructor <;> omega
  · -- val → OD: construct rank conditions from val
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨h1, h2⟩ := hx
    constructor
    · show m ≤ @rank (Fin (2 * m))ᵒᵈ _ _ (OrderDual.toDual x)
      rw [rank_fin_od_val]; omega
    · show @rank (Fin (2 * m))ᵒᵈ _ _ (OrderDual.toDual (w x)) < k
      rw [rank_fin_od_val]
      have := (w x).isLt; omega
  · intro _ _; rfl
  · intro _ _; rfl

theorem shrinkHalver_isEpsilonHalver {M : ℕ} (net : ComparatorNetwork (2 * M))
    (hbip : net.IsBipartite) (ε : ℝ) (hε : IsEpsilonHalver net ε) (hε_nn : 0 ≤ ε)
    (n : ℕ) (hn : 0 < n) (hnM : n ≤ M) :
    IsEpsilonHalver (shrinkHalver net n hnM) (ε * (↑(M - n) + 1)) := by
  set ε' := ε * (↑(M - n) + 1)
  set net' := shrinkHalver net n hnM
  have hn2 : 2 * n / 2 = n := by omega
  -- Helper: ε * (M - n + k) ≤ ε' * k for k ≥ 1
  have eps_bound : ∀ k : ℕ, 0 < k → ε * (↑M - ↑n + ↑k) ≤ ε' * ↑k := by
    intro k hk_pos
    show ε * (↑M - ↑n + ↑k) ≤ ε * (↑(M - n) + 1) * ↑k
    rw [show (↑(M - n) : ℝ) = ↑M - ↑n from Nat.cast_sub hnM]
    have h1 : (1 : ℝ) ≤ ↑k := by exact_mod_cast hk_pos
    have h2 : (0 : ℝ) ≤ ↑M - ↑n := sub_nonneg.mpr (Nat.cast_le.mpr hnM)
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hε_nn h2)]
  -- Note: rank is ℕ, so rank x < 0 is absurd via Nat.not_lt_zero
  intro v
  constructor
  · -- EpsilonInitialHalved
    show EpsilonInitialHalved (net'.exec v) ε'
    simp only [EpsilonInitialHalved, Fintype.card_fin, hn2]
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0; simp only [Nat.cast_zero, mul_zero]
      suffices h0 : (univ.filter (fun pos : Fin (2 * n) ↦
          n ≤ rank pos ∧ rank (net'.exec (↑v) pos) < 0)).card = 0 by
        rw [h0]; norm_num
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _; exact fun ⟨_, h⟩ => absurd h (Nat.not_lt_zero _)
    · calc ((univ.filter (fun pos : Fin (2 * n) ↦
                n ≤ rank pos ∧ rank (net'.exec (↑v) pos) < k)).card : ℝ)
          ≤ ε * (↑M - ↑n + ↑k) := shrinkHalver_initialBound net hbip ε hε n hn hnM v k hk
        _ ≤ ε' * ↑k := eps_bound k (Nat.pos_of_ne_zero hk0)
  · -- EpsilonFinalHalved via mk_epsilonFinalHalved (avoids exec re-elaboration)
    exact mk_epsilonFinalHalved (fun k hk ↦ by
      by_cases hk0 : k = 0
      · subst hk0; simp
      · calc ((univ.filter (fun pos : Fin (2 * n) ↦
                  pos.val < n ∧ 2 * n - k ≤ (net'.exec (↑v) pos).val)).card : ℝ)
            ≤ ε * (↑M - ↑n + ↑k) := shrinkHalver_finalBound net hbip ε hε n hn hnM v k hk
          _ ≤ ε' * ↑k := eps_bound k (Nat.pos_of_ne_zero hk0))
