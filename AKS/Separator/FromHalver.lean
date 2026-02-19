/-
  # Halver → Separator Construction

  Constructs (γ, ε)-separator networks from ε-halver families by
  iterated halving (Seiferas 2009, Section 6, Lemma 1).

  Key definitions:
  • `halverToSeparator` — computable construction reusing `halverNetwork`
  • `halverToSeparatorFamily` — bundles into a `SeparatorFamily`

  Key results:
  • `halver_isSeparator_half` — base case: ε-halver → (1/2, ε)-separator (proved)
  • `separator_halving_step` — halving refines 1/2^t → 1/2^(t+1), error += ε₁
  • `halverToSeparator_isSeparator` — t levels → (1/2^t, tε)-separation
  • `halverToSeparator_depth_le` — depth ≤ t · d
-/

import AKS.Separator.Family
import AKS.Nearsort.Construction
import Mathlib.Algebra.Order.Floor.Semifield

open Finset BigOperators


/-! **Construction** -/

/-- Build a separator from a halver family by iterating `t` levels of
    recursive halving. Reuses `halverNetwork` from `Nearsort/Construction.lean`. -/
def halverToSeparator {ε : ℝ} {d : ℕ} (n : ℕ) (family : HalverFamily ε d)
    (t : ℕ) : ComparatorNetwork n :=
  halverNetwork n family.net t


/-! **Floor/division bridging lemmas** -/

/-- `⌊(1/2) * ↑n⌋₊ = n / 2` for natural `n`. -/
private lemma floor_half_eq_div2 (n : ℕ) : ⌊(1 / 2 : ℝ) * ↑n⌋₊ = n / 2 := by
  rw [show (1 / 2 : ℝ) * ↑n = ↑n / 2 from by ring]
  exact Nat.floor_div_eq_div n 2

/-- For `0 ≤ γ' ≤ 1/2`, `⌊γ' * n⌋₊ ≤ n / 2`. -/
private lemma floor_gamma_le_div2 (n : ℕ) (γ' : ℝ) (_hγ' : 0 ≤ γ') (hle : γ' ≤ 1 / 2) :
    ⌊γ' * ↑n⌋₊ ≤ n / 2 := by
  calc ⌊γ' * ↑n⌋₊
      ≤ ⌊(1 / 2 : ℝ) * ↑n⌋₊ := by
        apply Nat.floor_le_floor
        exact mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)
    _ = n / 2 := floor_half_eq_div2 n


/-! **Base case: ε-halver is a (1/2, ε)-separator** -/

/-- Bridge: `EpsilonInitialHalved` implies `SepInitial` at γ = 1/2.
    Generalized over any linearly ordered finite type (handles both
    `Fin n` for the initial direction and `(Fin n)ᵒᵈ` for the final). -/
private lemma epsilonInitialHalved_implies_sepInitial
    {α : Type*} [Fintype α] [LinearOrder α]
    {w : α → α} {ε : ℝ} (hε : 0 ≤ ε)
    (h : EpsilonInitialHalved w ε) : SepInitial w (1 / 2) ε := by
  set N := Fintype.card α with hN_def
  show ∀ γ' : ℝ, 0 ≤ γ' → γ' ≤ 1 / 2 →
    ((Finset.univ.filter (fun pos : α ↦
        ⌊(1 / 2 : ℝ) * ↑N⌋₊ ≤ rank pos ∧ rank (w pos) < ⌊γ' * ↑N⌋₊)).card : ℝ) ≤
      ε * γ' * ↑N
  intro γ' hγ' hγ'_le
  set k := ⌊γ' * ↑N⌋₊ with hk_def
  rw [floor_half_eq_div2]
  have hk_le : k ≤ N / 2 := floor_gamma_le_div2 N γ' hγ' hγ'_le
  calc ((Finset.univ.filter (fun pos : α ↦
          N / 2 ≤ rank pos ∧ rank (w pos) < k)).card : ℝ)
      ≤ ε * ↑k := h k hk_le
    _ ≤ ε * (γ' * ↑N) := by
        apply mul_le_mul_of_nonneg_left _ hε
        exact_mod_cast Nat.floor_le (mul_nonneg hγ' (Nat.cast_nonneg _))
    _ = ε * γ' * ↑N := by ring

/-- An ε-halver provides ε-approximate (1/2)-separation (Seiferas Lemma 1 base).

    The halver bounds `EpsilonInitialHalved` quantify over `k ≤ n/2` and count
    elements with `rank pos ≥ n/2 ∧ rank (w pos) < k`. The separator bounds
    `SepInitial` at γ = 1/2 quantify over `γ' ≤ 1/2` and count elements with
    `rank pos ≥ ⌊(1/2)·n⌋₊ ∧ rank (w pos) < ⌊γ'·n⌋₊`.

    The bridge: `⌊(1/2)·n⌋₊ = n/2` (nat division) and setting `k = ⌊γ'·n⌋₊`
    gives `k ≤ n/2`. The error bound `ε·k ≤ ε·γ'·n` since `k ≤ γ'·n`. -/
theorem halver_isSeparator_half {n : ℕ} (net : ComparatorNetwork n) (ε : ℝ)
    (hε : 0 ≤ ε) (h : IsEpsilonHalver net ε) :
    IsSeparator net (1 / 2) ε := by
  intro v
  obtain ⟨h_init, h_final⟩ := h v
  exact ⟨epsilonInitialHalved_implies_sepInitial hε h_init,
         epsilonInitialHalved_implies_sepInitial hε h_final⟩


/-! **Induction step: floor/power bridging** -/

/-- `⌊(1/2^t) * ↑n⌋₊ = n / 2^t` for natural `n`. Generalizes `floor_half_eq_div2`. -/
private lemma floor_pow_half_eq_div (n t : ℕ) :
    ⌊(1 / 2 ^ t : ℝ) * ↑n⌋₊ = n / 2 ^ t := by
  rw [show (1 / 2 ^ t : ℝ) * ↑n = ↑n / 2 ^ t from by ring]
  rw [show (2 : ℝ) ^ t = ↑(2 ^ t : ℕ) from by push_cast; ring]
  exact Nat.floor_div_eq_div n (2 ^ t)

/-- For `0 ≤ γ' ≤ 1/2^t`, `⌊γ' * n⌋₊ ≤ n / 2^t`. -/
private lemma floor_gamma_le_div_pow (n t : ℕ) (γ' : ℝ) (_hγ' : 0 ≤ γ')
    (hle : γ' ≤ 1 / 2 ^ t) : ⌊γ' * ↑n⌋₊ ≤ n / 2 ^ t := by
  calc ⌊γ' * ↑n⌋₊
      ≤ ⌊(1 / 2 ^ t : ℝ) * ↑n⌋₊ := by
        apply Nat.floor_le_floor
        exact mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)
    _ = n / 2 ^ t := floor_pow_half_eq_div n t

/-- `(n / 2^t) / 2 = n / 2^(t+1)` (nat division, always true). -/
private lemma half_chunk_eq (n t : ℕ) : n / 2 ^ t / 2 = n / 2 ^ (t + 1) := by
  rw [Nat.div_div_eq_div_mul, pow_succ]

/-- Offset arithmetic: when `2*H = C` and `C ≤ n`, `n - C + i < n - H` for `i < H`. -/
private lemma offset_add_lt_sub {n C H i : ℕ} (h2H : 2 * H = C) (hCn : C ≤ n) (hiH : i < H) :
    n - C + i < n - H := by omega


/-! **Induction step: value count preservation** -/

/-- A single comparator that doesn't cross a boundary preserves the count of
    values `< k` at positions below the boundary. If both endpoints are below
    the boundary, the comparator swaps within that region (preserving the multiset).
    If both endpoints are at/above the boundary, positions below are untouched. -/
private lemma comparator_preserves_count {n : ℕ}
    (c : Comparator n) (v : Fin n → Fin n) (_hv : Function.Injective v) (boundary k : ℕ)
    (h : (c.i.val < boundary ∧ c.j.val < boundary) ∨
         (boundary ≤ c.i.val ∧ boundary ≤ c.j.val)) :
    (Finset.univ.filter (fun pos : Fin n ↦ pos.val < boundary ∧ (c.apply v pos).val < k)).card =
    (Finset.univ.filter (fun pos : Fin n ↦ pos.val < boundary ∧ (v pos).val < k)).card := by
  obtain ⟨hi, hj⟩ | ⟨hi, hj⟩ := h
  · -- Both inside: swap within [0, boundary)
    by_cases hle : v c.i ≤ v c.j
    · -- No swap
      have heq : c.apply v = v := by
        ext p; unfold Comparator.apply
        by_cases hpi : p = c.i
        · subst hpi; rw [if_pos rfl, min_eq_left hle]
        · rw [if_neg hpi]; by_cases hpj : p = c.j
          · subst hpj; rw [if_pos rfl, max_eq_right hle]
          · rw [if_neg hpj]
      rw [heq]
    · -- Swap: bijection via Equiv.swap
      push_neg at hle
      have heq : c.apply v = v ∘ ⇑(Equiv.swap c.i c.j) := by
        ext p; unfold Comparator.apply; simp only [Function.comp]
        by_cases hpi : p = c.i
        · subst hpi; rw [if_pos rfl, min_eq_right hle.le, Equiv.swap_apply_left]
        · rw [if_neg hpi]; by_cases hpj : p = c.j
          · subst hpj; rw [if_pos rfl, max_eq_left hle.le, Equiv.swap_apply_right]
          · rw [if_neg hpj, Equiv.swap_apply_of_ne_of_ne hpi hpj]
      rw [heq]
      apply Finset.card_nbij' (fun p ↦ Equiv.swap c.i c.j p) (fun p ↦ Equiv.swap c.i c.j p)
      · intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.comp] at hp ⊢
        refine ⟨?_, hp.2⟩
        by_cases hpi : p = c.i
        · subst hpi; rw [Equiv.swap_apply_left]; exact hj
        · by_cases hpj : p = c.j
          · subst hpj; rw [Equiv.swap_apply_right]; exact hi
          · rw [Equiv.swap_apply_of_ne_of_ne hpi hpj]; exact hp.1
      · intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        refine ⟨?_, ?_⟩
        · by_cases hpi : p = c.i
          · subst hpi; rw [Equiv.swap_apply_left]; exact hj
          · by_cases hpj : p = c.j
            · subst hpj; rw [Equiv.swap_apply_right]; exact hi
            · rw [Equiv.swap_apply_of_ne_of_ne hpi hpj]; exact hp.1
        · simp only [Function.comp, Equiv.swap_apply_self]; exact hp.2
      · intro _ _; simp [Equiv.swap_apply_self]
      · intro _ _; simp [Equiv.swap_apply_self]
  · -- Both outside: comparator doesn't touch [0, boundary)
    congr 1; ext pos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro ⟨hpos, hval⟩
    · refine ⟨hpos, ?_⟩
      unfold Comparator.apply at hval
      have hne_i : pos ≠ c.i := by intro heq; subst heq; omega
      have hne_j : pos ≠ c.j := by intro heq; subst heq; omega
      rw [if_neg hne_i, if_neg hne_j] at hval; exact hval
    · refine ⟨hpos, ?_⟩
      show (Comparator.apply c v pos).val < k
      unfold Comparator.apply
      have hne_i : pos ≠ c.i := by intro heq; subst heq; omega
      have hne_j : pos ≠ c.j := by intro heq; subst heq; omega
      rw [if_neg hne_i, if_neg hne_j]; exact hval

/-- Folding a list of non-crossing comparators preserves the count. -/
private lemma foldl_preserves_count {n : ℕ}
    (cs : List (Comparator n)) (v : Fin n → Fin n) (hv : Function.Injective v)
    (boundary k : ℕ)
    (hcs : ∀ c ∈ cs, (c.i.val < boundary ∧ c.j.val < boundary) ∨
                       (boundary ≤ c.i.val ∧ boundary ≤ c.j.val)) :
    (Finset.univ.filter (fun pos : Fin n ↦
      pos.val < boundary ∧ (cs.foldl (fun acc c ↦ c.apply acc) v pos).val < k)).card =
    (Finset.univ.filter (fun pos : Fin n ↦ pos.val < boundary ∧ (v pos).val < k)).card := by
  induction cs generalizing v with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [ih (c.apply v) (Comparator.apply_injective c hv)
          (fun c' hc' => hcs c' (.tail c hc'))]
    exact comparator_preserves_count c v hv boundary k (hcs c (.head cs))

/-- All comparators in `halverAtLevel` have both endpoints in the same chunk. -/
private lemma halverAtLevel_comparators_same_chunk {n : ℕ}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)} (t : ℕ)
    (c : Comparator n) (hc : c ∈ (halverAtLevel n halvers t).comparators) :
    let C := n / 2 ^ t
    (c.i.val < C ∧ c.j.val < C) ∨ (C ≤ c.i.val ∧ C ≤ c.j.val) := by
  simp only [halverAtLevel, applyHalverToSubinterval] at hc
  rw [List.mem_flatMap] at hc
  obtain ⟨k, hk_mem, hc_chunk⟩ := hc
  rw [List.mem_range] at hk_mem
  set C := n / 2 ^ t
  set H := C / 2
  by_cases hguard : k * C + 2 * H ≤ n
  · rw [dif_pos hguard] at hc_chunk
    simp only [ComparatorNetwork.shiftEmbed, List.mem_map] at hc_chunk
    obtain ⟨c₀, _, rfl⟩ := hc_chunk
    have hi₀ := c₀.i.isLt
    have hj₀ := c₀.j.isLt
    have h2H_le_C : 2 * H ≤ C := Nat.mul_div_le C 2
    by_cases hk0 : k = 0
    · left; subst hk0; constructor <;> dsimp <;> omega
    · right
      have hkC : C ≤ k * C := le_mul_of_one_le_left (Nat.zero_le _) (Nat.pos_of_ne_zero hk0)
      constructor <;> dsimp <;> omega
  · rw [dif_neg hguard] at hc_chunk; simp at hc_chunk

/-- Count of values `< k` at positions `< C` is preserved by `halverAtLevel`.

    The halver at level `t` only uses comparators within each chunk of size
    `C = n / 2^t`. Since chunk-0 comparators stay in `[0, C)` and all other
    chunks' comparators have indices `≥ C`, the multiset of values in
    `[0, C)` is preserved. Hence the count of values `< k` is preserved.

    Combined with `|{pos : w(pos) < k}| = k` (since `w` is a bijection),
    this implies `|{pos ≥ C : w₂(pos) < k}| = |{pos ≥ C : w₁(pos) < k}|`
    (the count of small values at positions outside chunk 0 is preserved). -/
private lemma halverAtLevel_chunk0_count_eq {n : ℕ}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)} (t : ℕ)
    (w₁ : Fin n → Fin n) (hw₁ : Function.Injective w₁) (k : ℕ) :
    let C := n / 2 ^ t
    let w₂ := (halverAtLevel n halvers t).exec w₁
    (Finset.univ.filter (fun pos : Fin n ↦ pos.val < C ∧ (w₂ pos).val < k)).card =
    (Finset.univ.filter (fun pos : Fin n ↦ pos.val < C ∧ (w₁ pos).val < k)).card := by
  intro C
  show (Finset.univ.filter (fun pos : Fin n ↦
    pos.val < C ∧ ((halverAtLevel n halvers t).comparators.foldl
      (fun acc c ↦ c.apply acc) w₁ pos).val < k)).card = _
  exact foldl_preserves_count _ w₁ hw₁ C k
    (fun c hc => halverAtLevel_comparators_same_chunk t c hc)


/-! **Induction step: near outsider bound — helpers** -/

/-- Strictly monotone threshold: for strictly monotone `g : Fin C → Fin n`,
    the count `a := |{r : (g r).val < k}|` satisfies `(g r).val < k ↔ r.val < a`. -/
private lemma strictMono_threshold {C n : ℕ} {g : Fin C → Fin n}
    (hg : StrictMono g) (k : ℕ) :
    let a := (Finset.univ.filter (fun r : Fin C ↦ (g r).val < k)).card
    ∀ r : Fin C, (g r).val < k ↔ r.val < a := by
  intro a r
  constructor
  · intro hr
    have hsub : Finset.Iic r ⊆ Finset.univ.filter (fun s : Fin C ↦ (g s).val < k) := by
      intro s hs
      simp only [Finset.mem_Iic] at hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have : (g s).val ≤ (g r).val := by
        rcases eq_or_lt_of_le hs with heq | hlt
        · rw [heq]
        · exact le_of_lt (hg hlt)
      omega
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this; omega
  · intro hr
    by_contra hk; push_neg at hk
    have hsub : Finset.univ.filter (fun s : Fin C ↦ (g s).val < k) ⊆ Finset.Iio r := by
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      simp only [Finset.mem_Iio]
      by_contra hge; push_neg at hge
      have : (g r).val ≤ (g s).val := by
        rcases eq_or_lt_of_le hge with heq | hlt
        · rw [heq]
        · exact le_of_lt (hg hlt)
      omega
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this; omega

/-- Reverse threshold: for strictly monotone `g : Fin C → Fin n`,
    `threshold ≤ (g r).val ↔ C - a ≤ r.val` where
    `a := |{r : threshold ≤ (g r).val}|`. -/
private lemma strictMono_reverse_threshold {C n : ℕ} {g : Fin C → Fin n}
    (hg : StrictMono g) (threshold : ℕ) :
    let a := (Finset.univ.filter (fun r : Fin C ↦ threshold ≤ (g r).val)).card
    ∀ r : Fin C, threshold ≤ (g r).val ↔ C - a ≤ r.val := by
  intro a r
  have hlt_count : (Finset.univ.filter (fun r : Fin C ↦ (g r).val < threshold)).card = C - a := by
    have htotal := Finset.card_filter_add_card_filter_not
      (fun r : Fin C ↦ threshold ≤ (g r).val) (s := Finset.univ)
    simp only [Finset.card_univ, Fintype.card_fin, not_le] at htotal
    omega
  have hthresh := strictMono_threshold hg threshold
  rw [show (Finset.univ.filter (fun r : Fin C ↦ (g r).val < threshold)).card = C - a
    from hlt_count] at hthresh
  constructor
  · intro h; by_contra hlt; push_neg at hlt
    have := (hthresh r).mpr hlt; omega
  · intro h; by_contra hlt; push_neg at hlt
    have := (hthresh r).mp hlt; omega

/-- Halver bound for injective (not just permutation) inputs: decompose
    `u = g ∘ σ` where `g` is the sorted enumeration (strictly monotone)
    and `σ` is a permutation, then use `exec_comp_mono` to reduce to `σ`. -/
private lemma halver_injective_initial_halved {m n : ℕ}
    {net : ComparatorNetwork (2 * m)} {ε : ℝ}
    (hnet : IsEpsilonHalver net ε) (_hε : 0 ≤ ε)
    (u : Fin (2 * m) → Fin n) (hu : Function.Injective u) (k : ℕ) :
    let C := 2 * m
    let a := (Finset.univ.filter (fun i : Fin C ↦ (u i).val < k)).card
    a ≤ m →
    ((Finset.univ.filter (fun pos : Fin C ↦
        m ≤ pos.val ∧ (net.exec u pos).val < k)).card : ℝ) ≤ ε * ↑a := by
  intro C a ha
  -- Decompose u = g ∘ σ
  set S := Finset.univ.image u with hS_def
  have hcard : S.card = C := by
    rw [Finset.card_image_of_injective _ hu, Finset.card_univ, Fintype.card_fin]
  set g_iso := S.orderIsoOfFin hcard
  set g : Fin C → Fin n := fun i ↦ (g_iso i).val with hg_def
  have hg_strict : StrictMono g := by
    intro a b hab; exact g_iso.strictMono hab
  have hmem : ∀ j, u j ∈ S := fun j ↦ Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  set σ_fun : Fin C → Fin C := fun j ↦ g_iso.symm ⟨u j, hmem j⟩
  have hσ_inj : Function.Injective σ_fun := by
    intro j₁ j₂ heq
    have h' : (⟨u j₁, hmem j₁⟩ : ↥S) = ⟨u j₂, hmem j₂⟩ :=
      g_iso.symm.injective heq
    exact hu (Subtype.ext_iff.mp h')
  set σ : Equiv.Perm (Fin C) := Equiv.ofBijective σ_fun
    ((Finite.injective_iff_bijective).mp hσ_inj)
  -- u = g ∘ σ
  have hu_eq : ∀ j, u j = g (σ j) := by
    intro j
    show u j = (g_iso (g_iso.symm ⟨u j, hmem j⟩)).val
    simp [g_iso.apply_symm_apply]
  -- exec_comp_mono: net.exec u = g ∘ net.exec σ
  have hexec : net.exec u = g ∘ net.exec (⇑σ) := by
    have heq : u = g ∘ ⇑σ := funext hu_eq
    rw [heq]
    exact ComparatorNetwork.exec_comp_mono net (StrictMono.monotone hg_strict) (⇑σ)
  -- g-based count equals a (via bijection σ)
  have ha_eq : a = (Finset.univ.filter (fun r : Fin C ↦ (g r).val < k)).card := by
    apply Finset.card_nbij' σ σ.symm
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rw [← hu_eq i]; exact hi
    · intro r hr
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      rw [hu_eq (σ.symm r), σ.apply_symm_apply]; exact hr
    · intro _ _; simp
    · intro _ _; simp
  -- Threshold: (g r).val < k ↔ r.val < a
  have hthresh : ∀ r : Fin C, (g r).val < k ↔ r.val < a := by
    rw [ha_eq]; exact strictMono_threshold hg_strict k
  -- Rewrite filter using threshold
  have hfilter_eq : Finset.univ.filter (fun pos : Fin C ↦
      m ≤ pos.val ∧ (net.exec u pos).val < k) =
    Finset.univ.filter (fun pos : Fin C ↦
      m ≤ pos.val ∧ (net.exec (⇑σ) pos).val < a) := by
    ext pos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ⟨hm, hk'⟩
      refine ⟨hm, ?_⟩
      have := congr_fun hexec pos
      simp only [Function.comp] at this
      rw [this] at hk'
      exact (hthresh _).mp hk'
    · intro ⟨hm, ha'⟩
      refine ⟨hm, ?_⟩
      have := congr_fun hexec pos
      simp only [Function.comp] at this
      rw [this]
      exact (hthresh _).mpr ha'
  rw [hfilter_eq]
  -- Apply EpsilonInitialHalved
  have hhalved := (hnet σ).1
  have hC : Fintype.card (Fin C) = C := Fintype.card_fin C
  have hC2 : C / 2 = m := by omega
  have := hhalved a (by rw [hC, hC2]; exact ha)
  suffices hsuff : Finset.univ.filter (fun pos : Fin C ↦
      m ≤ pos.val ∧ (net.exec (⇑σ) pos).val < a) =
    Finset.univ.filter (fun pos : Fin C ↦
      Fintype.card (Fin C) / 2 ≤ rank pos ∧ rank (net.exec (⇑σ) pos) < a) by
    rw [hsuff]; exact this
  ext pos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, rank_fin_val, hC, hC2]

/-- For injective `u : Fin m → Fin n`, the count of `i` with `(u i).val < k` is at most `k`. -/
private lemma injective_count_lt_le {m n : ℕ}
    (u : Fin m → Fin n) (hu : Function.Injective u) (k : ℕ) :
    (Finset.univ.filter (fun i : Fin m ↦ (u i).val < k)).card ≤ k := by
  have hinj : Function.Injective (fun i : Fin m ↦ (u i).val) :=
    Fin.val_injective.comp hu
  calc (Finset.univ.filter (fun i : Fin m ↦ (u i).val < k)).card
      = ((Finset.univ.filter (fun i : Fin m ↦ (u i).val < k)).image (fun i ↦ (u i).val)).card := by
        rw [Finset.card_image_of_injOn (fun a _ b _ h ↦ hinj h)]
    _ ≤ (Finset.range k).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact Finset.mem_range.mpr hi
    _ = k := Finset.card_range k

/-- For injective `u : Fin m → Fin n`, at most `k` positions have value `≥ n - k`. -/
private lemma injective_count_ge_le {m n : ℕ}
    (u : Fin m → Fin n) (hu : Function.Injective u) (k : ℕ) :
    (Finset.univ.filter (fun i : Fin m ↦ n - k ≤ (u i).val)).card ≤ k := by
  by_cases hk : k ≥ n
  · have hm : m ≤ n := by
      have := Fintype.card_le_of_injective u hu
      simp only [Fintype.card_fin] at this; exact this
    calc (Finset.univ.filter _).card ≤ Finset.univ.card := Finset.card_filter_le _ _
      _ = m := Finset.card_fin m
      _ ≤ n := hm
      _ ≤ k := hk
  · push_neg at hk
    have hinj : Function.Injective (fun i : Fin m ↦ (u i).val) :=
      Fin.val_injective.comp hu
    calc (Finset.univ.filter (fun i : Fin m ↦ n - k ≤ (u i).val)).card
        = ((Finset.univ.filter (fun i : Fin m ↦ n - k ≤ (u i).val)).image
            (fun i ↦ (u i).val)).card := by
          rw [Finset.card_image_of_injOn (fun a _ b _ h ↦ hinj h)]
      _ ≤ (Finset.Ico (n - k) n).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_Ico] at hx ⊢
          obtain ⟨i, hi, rfl⟩ := hx
          exact ⟨hi, (u i).isLt⟩
      _ = k := by simp only [Nat.card_Ico]; omega

/-- Halver bound for injective inputs, FINAL direction: decompose
    `u = g ∘ σ`, use `exec_comp_mono`, apply `EpsilonFinalHalved` from `(hnet σ).2`. -/
private lemma halver_injective_final_halved {m n : ℕ}
    {net : ComparatorNetwork (2 * m)} {ε : ℝ}
    (hnet : IsEpsilonHalver net ε) (_hε : 0 ≤ ε)
    (u : Fin (2 * m) → Fin n) (hu : Function.Injective u) (threshold : ℕ) :
    let C := 2 * m
    let a := (Finset.univ.filter (fun i : Fin C ↦ threshold ≤ (u i).val)).card
    a ≤ m →
    ((Finset.univ.filter (fun pos : Fin C ↦
        pos.val < m ∧ threshold ≤ (net.exec u pos).val)).card : ℝ) ≤ ε * ↑a := by
  intro C a ha
  -- Decompose u = g ∘ σ (same as initial version)
  set S := Finset.univ.image u with hS_def
  have hcard : S.card = C := by
    rw [Finset.card_image_of_injective _ hu, Finset.card_univ, Fintype.card_fin]
  set g_iso := S.orderIsoOfFin hcard
  set g : Fin C → Fin n := fun i ↦ (g_iso i).val with hg_def
  have hg_strict : StrictMono g := by
    intro a b hab; exact g_iso.strictMono hab
  have hmem : ∀ j, u j ∈ S := fun j ↦ Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  set σ_fun : Fin C → Fin C := fun j ↦ g_iso.symm ⟨u j, hmem j⟩
  have hσ_inj : Function.Injective σ_fun := by
    intro j₁ j₂ heq
    have h' : (⟨u j₁, hmem j₁⟩ : ↥S) = ⟨u j₂, hmem j₂⟩ :=
      g_iso.symm.injective heq
    exact hu (Subtype.ext_iff.mp h')
  set σ : Equiv.Perm (Fin C) := Equiv.ofBijective σ_fun
    ((Finite.injective_iff_bijective).mp hσ_inj)
  -- u = g ∘ σ
  have hu_eq : ∀ j, u j = g (σ j) := by
    intro j
    show u j = (g_iso (g_iso.symm ⟨u j, hmem j⟩)).val
    simp [g_iso.apply_symm_apply]
  -- exec_comp_mono: net.exec u = g ∘ net.exec σ
  have hexec : net.exec u = g ∘ net.exec (⇑σ) := by
    have heq : u = g ∘ ⇑σ := funext hu_eq
    rw [heq]
    exact ComparatorNetwork.exec_comp_mono net (StrictMono.monotone hg_strict) (⇑σ)
  -- g-based count equals a (via bijection σ)
  have ha_eq : a = (Finset.univ.filter (fun r : Fin C ↦ threshold ≤ (g r).val)).card := by
    apply Finset.card_nbij' σ σ.symm
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rw [← hu_eq i]; exact hi
    · intro r hr
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      rw [hu_eq (σ.symm r), σ.apply_symm_apply]; exact hr
    · intro _ _; simp
    · intro _ _; simp
  -- Reverse threshold: threshold ≤ (g r).val ↔ C - a ≤ r.val
  have hthresh : ∀ r : Fin C, threshold ≤ (g r).val ↔ C - a ≤ r.val := by
    rw [ha_eq]; exact strictMono_reverse_threshold hg_strict threshold
  -- Rewrite filter using threshold
  have hfilter_eq : Finset.univ.filter (fun pos : Fin C ↦
      pos.val < m ∧ threshold ≤ (net.exec u pos).val) =
    Finset.univ.filter (fun pos : Fin C ↦
      pos.val < m ∧ C - a ≤ (net.exec (⇑σ) pos).val) := by
    ext pos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ⟨hm, hge⟩
      refine ⟨hm, ?_⟩
      have := congr_fun hexec pos
      simp only [Function.comp] at this
      rw [this] at hge
      exact (hthresh _).mp hge
    · intro ⟨hm, hge⟩
      refine ⟨hm, ?_⟩
      have := congr_fun hexec pos
      simp only [Function.comp] at this
      rw [this]
      exact (hthresh _).mpr hge
  rw [hfilter_eq]
  -- Apply EpsilonFinalHalved.val_bound
  have hhalved := (hnet σ).2
  exact EpsilonFinalHalved.val_bound hhalved a ha

/-- Rest-of-chunks comparators (chunks 1, 2, ...) have both endpoints `≥ C`. -/
private lemma rest_chunks_endpoints_ge {n : ℕ}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)} (t : ℕ) :
    let C := n / 2 ^ t
    let H := C / 2
    ∀ c ∈ (List.range' 1 (2 ^ t - 1)).flatMap (fun k ↦
      let offset := k * C
      if h : offset + 2 * H ≤ n then
        (applyHalverToSubinterval n halvers H offset h).comparators
      else []),
    C ≤ c.i.val ∧ C ≤ c.j.val := by
  intro C H c hc
  rw [List.mem_flatMap] at hc
  obtain ⟨k, hk_mem, hc_chunk⟩ := hc
  rw [List.mem_range'] at hk_mem
  obtain ⟨i, hi_lt, hk_eq⟩ := hk_mem
  have hk_ge : 1 ≤ k := by omega
  have hkC_ge : C ≤ k * C := le_mul_of_one_le_left (Nat.zero_le _) hk_ge
  have h2H_le_C : 2 * H ≤ C := Nat.mul_div_le C 2
  by_cases hguard : k * C + 2 * H ≤ n
  · rw [dif_pos hguard] at hc_chunk
    simp only [applyHalverToSubinterval, ComparatorNetwork.shiftEmbed, List.mem_map] at hc_chunk
    obtain ⟨c₀, _, rfl⟩ := hc_chunk
    have hi₀ := c₀.i.isLt
    have hj₀ := c₀.j.isLt
    constructor <;> dsimp <;> omega
  · rw [dif_neg hguard] at hc_chunk; simp at hc_chunk

/-- Local view: for `pos < 2*H`, `halverAtLevel` execution equals the chunk-0
    halver's local execution on the restricted input. -/
private lemma halverAtLevel_local_eq {n : ℕ}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)} (t : ℕ)
    (w : Fin n → Fin n) :
    let C := n / 2 ^ t
    let H := C / 2
    ∀ (pos : Fin n) (hpos : pos.val < 2 * H),
    have h2H_le : 2 * H ≤ n :=
      calc 2 * H ≤ C := Nat.mul_div_le C 2
        _ ≤ n := Nat.div_le_self n _
    (halverAtLevel n halvers t).exec w pos =
    (halvers H).exec
      (fun j : Fin (2 * H) ↦ w ⟨j.val, by have := j.isLt; omega⟩) ⟨pos.val, hpos⟩ := by
  intro C H pos hpos h2H_le
  show (halverAtLevel n halvers t).comparators.foldl (fun acc c ↦ c.apply acc) w pos = _
  unfold halverAtLevel
  simp only
  -- Decompose List.range (2^t) = [0] ++ List.range' 1 (2^t - 1)
  have hpow_pos : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by omega)
  have h_split : List.range (2 ^ t) = List.range' 0 1 ++ List.range' 1 (2 ^ t - 1) := by
    conv_lhs => rw [List.range_eq_range', show 2 ^ t = 1 + (2 ^ t - 1) from by omega]
    exact List.range'_append.symm
  rw [h_split, List.flatMap_append, List.foldl_append]
  -- Rest comparators don't touch pos
  have h2H_le_C : 2 * H ≤ C := Nat.mul_div_le C 2
  have hrest : ∀ c ∈ (List.range' 1 (2 ^ t - 1)).flatMap (fun k ↦
      let offset := k * C
      if h : offset + 2 * H ≤ n then
        (applyHalverToSubinterval n halvers H offset h).comparators
      else []),
    pos ≠ c.i ∧ pos ≠ c.j := by
    intro c hc
    have ⟨hi, hj⟩ := rest_chunks_endpoints_ge t c hc
    exact ⟨by intro heq; subst heq; omega, by intro heq; subst heq; omega⟩
  rw [foldl_comparators_outside _ _ pos hrest]
  -- Chunk 0: range' 0 1 = [0], flatMap gives f(0) with offset = 0
  simp only [List.range', List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Nat.zero_mul, Nat.zero_add]
  rw [dif_pos h2H_le]
  simp only [applyHalverToSubinterval]
  -- Use shiftEmbed_exec_inside
  have h_shift := ComparatorNetwork.shiftEmbed_exec_inside (halvers H) n 0
    (by omega : 0 + 2 * H ≤ n) w ⟨pos.val, hpos⟩
  simp only [Nat.zero_add] at h_shift
  convert h_shift using 2


/-! **Induction step: near outsider bound** -/

/-- Bound on near outsiders (positions in `[H, C)` of chunk 0 with small values).

    Uses `exec_comp_mono` to relate the halver's output on the actual values
    (injective `Fin C → Fin n`) to its output on the local permutation
    (`Perm (Fin C)`), then applies `EpsilonInitialHalved` from `hhalver`.

    The count `a := |{pos < C : w₁(pos) < k}|` is the number of chunk-0
    values that are globally `< k`. By order-preservation, the halver's
    local bound `ε₁ · a` translates directly to the global bound. -/
private lemma halverAtLevel_near_outsider_le {n : ℕ}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)} {ε₁ : ℝ} (t : ℕ)
    (w₁ : Fin n → Fin n) (hw₁ : Function.Injective w₁)
    (hhalver : ∀ m, IsEpsilonHalver (halvers m) ε₁) (hε₁ : 0 ≤ ε₁)
    (h_even : 2 ∣ n / 2 ^ t) (k : ℕ) (hk : k ≤ n / 2 ^ t / 2) :
    let C := n / 2 ^ t
    let H := C / 2
    let w₂ := (halverAtLevel n halvers t).exec w₁
    let a := (Finset.univ.filter (fun pos : Fin n ↦ pos.val < C ∧ (w₁ pos).val < k)).card
    ((Finset.univ.filter (fun pos : Fin n ↦
        H ≤ pos.val ∧ pos.val < C ∧ (w₂ pos).val < k)).card : ℝ) ≤ ε₁ * ↑a := by
  intro C H w₂ a
  have h2H_eq : 2 * H = C := by have := Nat.div_mul_cancel h_even; omega
  have hC_le_n : C ≤ n := Nat.div_le_self n _
  have h2H_le_n : 2 * H ≤ n := by omega
  -- Trivial when H = 0
  by_cases hH : H = 0
  · have hC0 : C = 0 := by omega
    have hempty : (Finset.univ.filter (fun pos : Fin n ↦
        H ≤ pos.val ∧ pos.val < C ∧ (w₂ pos).val < k)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro pos _ ⟨_, h, _⟩; omega
    simp [hempty]; exact mul_nonneg hε₁ (Nat.cast_nonneg _)
  · -- H > 0
    have hH_pos : 0 < H := Nat.pos_of_ne_zero hH
    have h2H_pos : 0 < 2 * H := by omega
    -- Define local restriction u : Fin (2*H) → Fin n
    set u : Fin (2 * H) → Fin n :=
      fun j ↦ w₁ ⟨j.val, by have := j.isLt; omega⟩ with hu_def
    -- u is injective
    have hu_inj : Function.Injective u := by
      intro j₁ j₂ heq
      have h := hw₁ heq
      exact Fin.ext (by have := congr_arg Fin.val h; dsimp at this; exact this)
    -- Count a on Fin (2*H) = count a on Fin n restricted to [0, C)
    have ha_eq : a = (Finset.univ.filter (fun i : Fin (2 * H) ↦ (u i).val < k)).card := by
      apply Finset.card_nbij'
        (fun pos : Fin n ↦
          if h : pos.val < 2 * H then ⟨pos.val, h⟩ else ⟨0, h2H_pos⟩)
        (fun i : Fin (2 * H) ↦ ⟨i.val, by have := i.isLt; omega⟩)
      · intro pos hpos
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
        rw [dif_pos (show pos.val < 2 * H by omega)]
        exact hpos.2
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact ⟨by show i.val < C; have := i.isLt; omega, hi⟩
      · intro pos hpos
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos
        ext; simp only [dif_pos (show pos.val < 2 * H by omega)]
      · intro i _
        ext; dsimp only; split_ifs with h
        · rfl
        · exact absurd i.isLt h
    -- a ≤ H (injection: a ≤ k ≤ H)
    have ha_le : (Finset.univ.filter (fun i : Fin (2 * H) ↦ (u i).val < k)).card ≤ H := by
      calc _ ≤ k := injective_count_lt_le u hu_inj k
        _ ≤ H := hk
    -- LHS card on Fin n = LHS card on Fin (2*H)
    have hcard_eq : (Finset.univ.filter (fun pos : Fin n ↦
        H ≤ pos.val ∧ pos.val < C ∧ (w₂ pos).val < k)).card =
      (Finset.univ.filter (fun pos : Fin (2 * H) ↦
        H ≤ pos.val ∧ ((halvers H).exec u pos).val < k)).card := by
      apply Finset.card_nbij'
        (fun pos : Fin n ↦
          if h : pos.val < 2 * H then ⟨pos.val, h⟩ else ⟨0, h2H_pos⟩)
        (fun i : Fin (2 * H) ↦ ⟨i.val, by have := i.isLt; omega⟩)
      · intro pos hpos
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
        have hlt : pos.val < 2 * H := by omega
        rw [dif_pos hlt]
        refine ⟨hpos.1, ?_⟩
        have hlocal := halverAtLevel_local_eq (halvers := halvers) t w₁ pos hlt
        show ((halvers H).exec u ⟨pos.val, hlt⟩).val < k
        rw [← hlocal]; exact hpos.2.2
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        refine ⟨hi.1, by show i.val < C; have := i.isLt; omega, ?_⟩
        change ((halverAtLevel n halvers t).exec w₁ ⟨i.val, _⟩).val < k
        rw [halverAtLevel_local_eq (halvers := halvers) t w₁
          (⟨i.val, by have := i.isLt; omega⟩ : Fin n) i.isLt]
        convert hi.2 using 2
      · intro pos hpos
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos
        ext; simp only [dif_pos (show pos.val < 2 * H by omega)]
      · intro i _
        ext; dsimp only; split_ifs with h
        · rfl
        · exact absurd i.isLt h
    -- Apply halver_injective_initial_halved
    have hhalved := halver_injective_initial_halved (hhalver H) hε₁ u hu_inj k ha_le
    calc ((Finset.univ.filter (fun pos : Fin n ↦
          H ≤ pos.val ∧ pos.val < C ∧ (w₂ pos).val < k)).card : ℝ)
        = ↑(Finset.univ.filter (fun pos : Fin (2 * H) ↦
            H ≤ pos.val ∧ ((halvers H).exec u pos).val < k)).card := by
          exact_mod_cast hcard_eq
      _ ≤ ε₁ * ↑(Finset.univ.filter (fun i : Fin (2 * H) ↦ (u i).val < k)).card := hhalved
      _ = ε₁ * ↑a := by rw [← ha_eq]


/-! **Induction step: far outsider preservation** -/

/-- For injective `w : Fin n → Fin n`, the count of positions with
    `(w pos).val < k` equals the count of positions with `pos.val < k`.
    Since `w` is a bijection on a finite type, it permutes `{0,...,n-1}`. -/
private lemma bijection_count_val_lt {n : ℕ}
    (w : Fin n → Fin n) (hw : Function.Injective w) (k : ℕ) :
    (Finset.univ.filter (fun pos : Fin n ↦ (w pos).val < k)).card =
    (Finset.univ.filter (fun pos : Fin n ↦ pos.val < k)).card := by
  set e := Equiv.ofBijective w ((Finite.injective_iff_bijective).mp hw)
  apply Finset.card_nbij' (fun pos ↦ w pos) (fun i ↦ e.symm i)
  · intro pos hpos
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
    exact hpos
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    show (w (e.symm i)).val < k
    have : w (e.symm i) = i := e.apply_symm_apply i
    rw [this]; exact hi
  · intro pos _; exact e.symm_apply_apply pos
  · intro i _; show w (e.symm i) = i; exact e.apply_symm_apply i

/-- Partition: total count of positions with `(w pos).val < k` equals the sum
    of counts at positions `< C` and positions `≥ C`. -/
private lemma count_val_partition {n : ℕ} (w : Fin n → Fin n) (C k : ℕ) :
    (Finset.univ.filter (fun pos : Fin n ↦ (w pos).val < k)).card =
    (Finset.univ.filter (fun pos : Fin n ↦ pos.val < C ∧ (w pos).val < k)).card +
    (Finset.univ.filter (fun pos : Fin n ↦ C ≤ pos.val ∧ (w pos).val < k)).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext pos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h; by_cases hlt : pos.val < C
      · left; exact ⟨hlt, h⟩
      · right; exact ⟨by omega, h⟩
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
  · rw [Finset.disjoint_filter]; intro _ _ ⟨h1, _⟩ ⟨h2, _⟩; omega

/-- Count of values `< k` at positions `≥ C` is preserved by `halverAtLevel`.

    Since the halver only uses within-chunk comparators, the multiset of
    values at positions `< C` (chunk 0) is preserved. Both `w₁` and `w₂`
    are bijections, so their total counts of values `< k` are equal.
    Hence the count at positions `≥ C` (all other chunks) is also preserved. -/
private lemma far_outsider_count_preserved {n : ℕ}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)} (t : ℕ)
    (w₁ : Fin n → Fin n) (hw₁ : Function.Injective w₁) (k : ℕ) :
    let C := n / 2 ^ t
    let w₂ := (halverAtLevel n halvers t).exec w₁
    (Finset.univ.filter (fun pos : Fin n ↦ C ≤ pos.val ∧ (w₂ pos).val < k)).card =
    (Finset.univ.filter (fun pos : Fin n ↦ C ≤ pos.val ∧ (w₁ pos).val < k)).card := by
  intro C w₂
  have hw₂_inj : Function.Injective w₂ :=
    ComparatorNetwork.exec_injective _ hw₁
  have htotal : (Finset.univ.filter (fun pos : Fin n ↦ (w₂ pos).val < k)).card =
    (Finset.univ.filter (fun pos : Fin n ↦ (w₁ pos).val < k)).card := by
    rw [bijection_count_val_lt w₂ hw₂_inj, bijection_count_val_lt w₁ hw₁]
  have hnear : (Finset.univ.filter (fun pos : Fin n ↦
        pos.val < C ∧ (w₂ pos).val < k)).card =
      (Finset.univ.filter (fun pos : Fin n ↦
        pos.val < C ∧ (w₁ pos).val < k)).card :=
    halverAtLevel_chunk0_count_eq (halvers := halvers) t w₁ hw₁ k
  have hpart_w₂ := count_val_partition w₂ C k
  have hpart_w₁ := count_val_partition w₁ C k
  omega


/-! **Induction step: SepFinal direction helpers** -/

/-- Endpoints of non-last-chunk comparators (chunks 0, ..., 2^t-2) are below `n - C`. -/
private lemma non_last_chunk_endpoints_below {n : ℕ}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)} (t : ℕ)
    (h_pow_div : 2 ^ t ∣ n) :
    let C := n / 2 ^ t
    let H := C / 2
    ∀ c ∈ ((List.range (2 ^ t - 1)).flatMap (fun k ↦
      let offset := k * C
      if h : offset + 2 * H ≤ n then
        (applyHalverToSubinterval n halvers H offset h).comparators
      else [])),
    c.i.val < n - C ∧ c.j.val < n - C := by
  intro C H c hc
  rw [List.mem_flatMap] at hc
  obtain ⟨k, hk_mem, hc_chunk⟩ := hc
  rw [List.mem_range] at hk_mem
  have h_exact : C * 2 ^ t = n := Nat.div_mul_cancel h_pow_div
  have hpow_pos : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by omega)
  have h2H_le_C : 2 * H ≤ C := Nat.mul_div_le C 2
  have h_last_offset : (2 ^ t - 1) * C = n - C := by
    have : (2 ^ t - 1) * C + C = n := by
      calc (2 ^ t - 1) * C + C = (2 ^ t - 1 + 1) * C := by rw [Nat.add_mul]; ring
        _ = 2 ^ t * C := by rw [Nat.sub_add_cancel hpow_pos]
        _ = n := by rw [mul_comm]; exact h_exact
    omega
  by_cases hguard : k * C + 2 * H ≤ n
  · rw [dif_pos hguard] at hc_chunk
    simp only [applyHalverToSubinterval, ComparatorNetwork.shiftEmbed, List.mem_map] at hc_chunk
    obtain ⟨c₀, _, rfl⟩ := hc_chunk
    have hi₀ := c₀.i.isLt
    have hj₀ := c₀.j.isLt
    have hkC_bound : k * C + C ≤ n - C := by
      have : (k + 1) * C ≤ (2 ^ t - 1) * C :=
        Nat.mul_le_mul_right C (by omega)
      rw [Nat.add_mul] at this; simp only [Nat.one_mul] at this; omega
    have hci : c₀.i.val < C := by have := hi₀; have := h2H_le_C; omega
    have hcj : c₀.j.val < C := by have := hj₀; have := h2H_le_C; omega
    exact ⟨by dsimp; omega, by dsimp; omega⟩
  · rw [dif_neg hguard] at hc_chunk; simp at hc_chunk

/-- Non-crossing at boundary `n - C`: when `2^t ∣ n`, all `halverAtLevel` comparators
    have both endpoints `< n - C` or both `≥ n - C`. -/
private lemma halverAtLevel_comparators_non_crossing_last {n : ℕ}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)} (t : ℕ)
    (h_pow_div : 2 ^ t ∣ n)
    (c : Comparator n) (hc : c ∈ (halverAtLevel n halvers t).comparators) :
    let C := n / 2 ^ t
    (c.i.val < n - C ∧ c.j.val < n - C) ∨ (n - C ≤ c.i.val ∧ n - C ≤ c.j.val) := by
  simp only [halverAtLevel, applyHalverToSubinterval] at hc
  rw [List.mem_flatMap] at hc
  obtain ⟨k, hk_mem, hc_chunk⟩ := hc
  rw [List.mem_range] at hk_mem
  set C := n / 2 ^ t
  set H := C / 2
  have h_exact : C * 2 ^ t = n := Nat.div_mul_cancel h_pow_div
  have hpow_pos : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by omega)
  have h2H_le_C : 2 * H ≤ C := Nat.mul_div_le C 2
  have h_last_offset : (2 ^ t - 1) * C = n - C := by
    have : (2 ^ t - 1) * C + C = n := by
      calc (2 ^ t - 1) * C + C = (2 ^ t - 1 + 1) * C := by rw [Nat.add_mul]; ring
        _ = 2 ^ t * C := by rw [Nat.sub_add_cancel hpow_pos]
        _ = n := by rw [mul_comm]; exact h_exact
    omega
  by_cases hguard : k * C + 2 * H ≤ n
  · rw [dif_pos hguard] at hc_chunk
    simp only [ComparatorNetwork.shiftEmbed, List.mem_map] at hc_chunk
    obtain ⟨c₀, _, rfl⟩ := hc_chunk
    have hi₀ := c₀.i.isLt
    have hj₀ := c₀.j.isLt
    by_cases hk_last : k = 2 ^ t - 1
    · right
      have hkC_eq : k * C = n - C := by rw [hk_last]; exact h_last_offset
      exact ⟨by dsimp; omega, by dsimp; omega⟩
    · left
      have hkC_bound : k * C + C ≤ n - C := by
        have : (k + 1) * C ≤ (2 ^ t - 1) * C :=
          Nat.mul_le_mul_right C (by omega)
        rw [Nat.add_mul] at this; simp only [Nat.one_mul] at this; omega
      have hci : c₀.i.val < C := by have := hi₀; have := h2H_le_C; omega
      have hcj : c₀.j.val < C := by have := hj₀; have := h2H_le_C; omega
      exact ⟨by dsimp; omega, by dsimp; omega⟩
  · rw [dif_neg hguard] at hc_chunk; simp at hc_chunk

/-- Count of values `< k` at positions `< n - C` is preserved by `halverAtLevel`.
    Mirror of `halverAtLevel_chunk0_count_eq` for the last-chunk boundary. -/
private lemma halverAtLevel_non_last_count_eq {n : ℕ}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)} (t : ℕ)
    (h_pow_div : 2 ^ t ∣ n)
    (w₁ : Fin n → Fin n) (hw₁ : Function.Injective w₁) (k : ℕ) :
    let C := n / 2 ^ t
    let w₂ := (halverAtLevel n halvers t).exec w₁
    (Finset.univ.filter (fun pos : Fin n ↦ pos.val < n - C ∧ (w₂ pos).val < k)).card =
    (Finset.univ.filter (fun pos : Fin n ↦ pos.val < n - C ∧ (w₁ pos).val < k)).card := by
  intro C
  show (Finset.univ.filter (fun pos : Fin n ↦
    pos.val < n - C ∧ ((halverAtLevel n halvers t).comparators.foldl
      (fun acc c ↦ c.apply acc) w₁ pos).val < k)).card = _
  exact foldl_preserves_count _ w₁ hw₁ (n - C) k
    (fun c hc => halverAtLevel_comparators_non_crossing_last t h_pow_div c hc)

/-- Local view for the LAST chunk: `halverAtLevel` execution at position `pos`
    in `[n-C, n-C+2H)` equals the last-chunk halver's local execution. -/
private lemma halverAtLevel_local_eq_last {n : ℕ}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)} (t : ℕ)
    (h_pow_div : 2 ^ t ∣ n)
    (w : Fin n → Fin n) :
    let C := n / 2 ^ t
    let H := C / 2
    ∀ (pos : Fin n) (hge : n - C ≤ pos.val) (hlt : pos.val < n - C + 2 * H),
    have h2H_le : n - C + 2 * H ≤ n := by
      have := Nat.mul_div_le C 2; have := Nat.div_le_self n (2^t); omega
    (halverAtLevel n halvers t).exec w pos =
    (halvers H).exec
      (fun j : Fin (2 * H) ↦ w ⟨(n - C) + j.val, by
        have := j.isLt; have := Nat.div_le_self n (2^t)
        have := Nat.mul_div_le C 2; omega⟩)
      ⟨pos.val - (n - C), by omega⟩ := by
  intro C H pos hge hlt h2H_le
  show (halverAtLevel n halvers t).comparators.foldl (fun acc c ↦ c.apply acc) w pos = _
  unfold halverAtLevel; simp only
  change ((List.range (2 ^ t)).flatMap (fun k ↦
      if h : k * C + 2 * H ≤ n then
        (applyHalverToSubinterval n halvers H (k * C) h).comparators
      else [])).foldl (fun acc c ↦ c.apply acc) w pos = _
  have hpow_pos : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by omega)
  have h_exact : C * 2 ^ t = n := Nat.div_mul_cancel h_pow_div
  have h2H_le_C : 2 * H ≤ C := Nat.mul_div_le C 2
  have hC_le_n : C ≤ n := Nat.div_le_self n _
  have h_last_sum : (2 ^ t - 1) * C + C = n := by
    calc (2 ^ t - 1) * C + C
        = (2 ^ t - 1) * C + 1 * C := by rw [one_mul]
      _ = (2 ^ t - 1 + 1) * C := by rw [Nat.add_mul]
      _ = 2 ^ t * C := by rw [Nat.sub_add_cancel hpow_pos]
      _ = C * 2 ^ t := by rw [mul_comm]
      _ = n := h_exact
  have hoffset_eq : (2 ^ t - 1) * C = n - C := by omega
  have h_split : List.range (2 ^ t) = List.range (2 ^ t - 1) ++ [2 ^ t - 1] := by
    conv_lhs => rw [show 2 ^ t = (2 ^ t - 1) + 1 from by omega]
    exact List.range_succ
  rw [h_split, List.flatMap_append, List.foldl_append]
  set w' := ((List.range (2 ^ t - 1)).flatMap (fun k ↦
      if h : k * C + 2 * H ≤ n then
        (applyHalverToSubinterval n halvers H (k * C) h).comparators
      else [])).foldl (fun acc c ↦ c.apply acc) w with hw'_def
  have hw'_agree : ∀ j : Fin n, n - C ≤ j.val → w' j = w j := by
    intro j hj
    exact foldl_comparators_outside _ w j (fun c hc ↦ by
      have ⟨hi, hj_bound⟩ := non_last_chunk_endpoints_below t h_pow_div c hc
      exact ⟨by intro heq; subst heq; omega, by intro heq; subst heq; omega⟩)
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hguard : (2 ^ t - 1) * C + 2 * H ≤ n := by omega
  rw [dif_pos hguard]
  simp only [applyHalverToSubinterval]
  show ((halvers H).shiftEmbed n ((2 ^ t - 1) * C) hguard).exec w' pos = _
  have hoffset_le_pos : (2 ^ t - 1) * C ≤ pos.val := by omega
  have hpos_in : pos.val - (2 ^ t - 1) * C < 2 * H := by omega
  have h_shift := ComparatorNetwork.shiftEmbed_exec_inside (halvers H) n
    ((2 ^ t - 1) * C) hguard w' ⟨pos.val - (2 ^ t - 1) * C, hpos_in⟩
  have hfin_eq : ((halvers H).shiftEmbed n ((2 ^ t - 1) * C) hguard).exec w'
      ⟨(2 ^ t - 1) * C + (pos.val - (2 ^ t - 1) * C), by omega⟩ =
    ((halvers H).shiftEmbed n ((2 ^ t - 1) * C) hguard).exec w' pos := by
    congr 1; exact Fin.ext (Nat.add_sub_cancel' hoffset_le_pos)
  rw [← hfin_eq, h_shift]
  congr 1
  · funext j
    have hge_j : n - C ≤ (2 ^ t - 1) * C + j.val := by omega
    rw [hw'_agree ⟨(2 ^ t - 1) * C + j.val, by omega⟩ hge_j]
    congr 1; exact Fin.ext (show (2 ^ t - 1) * C + j.val = (n - C) + j.val by rw [hoffset_eq])
  · exact Fin.ext (show pos.val - (2 ^ t - 1) * C = pos.val - (n - C) by rw [hoffset_eq])

/-- Count of values `≥ threshold` at positions `< n - C` is preserved by `halverAtLevel`.
    Derives from `halverAtLevel_non_last_count_eq` via complementary counting. -/
private lemma far_outsider_count_preserved_final {n : ℕ}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)} (t : ℕ)
    (h_pow_div : 2 ^ t ∣ n)
    (w₁ : Fin n → Fin n) (hw₁ : Function.Injective w₁) (threshold : ℕ) :
    let C := n / 2 ^ t
    let w₂ := (halverAtLevel n halvers t).exec w₁
    (Finset.univ.filter (fun pos : Fin n ↦ pos.val < n - C ∧ threshold ≤ (w₂ pos).val)).card =
    (Finset.univ.filter (fun pos : Fin n ↦ pos.val < n - C ∧ threshold ≤ (w₁ pos).val)).card := by
  intro C w₂
  have hpart : ∀ w : Fin n → Fin n,
      (Finset.univ.filter (fun pos : Fin n ↦ pos.val < n - C ∧ (w pos).val < threshold)).card +
      (Finset.univ.filter (fun pos : Fin n ↦ pos.val < n - C ∧ threshold ≤ (w pos).val)).card =
      (Finset.univ.filter (fun pos : Fin n ↦ pos.val < n - C)).card := by
    intro w
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext pos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h; by_cases hlt : (w pos).val < threshold
        · left; exact ⟨h, hlt⟩
        · right; exact ⟨h, by omega⟩
    · rw [Finset.disjoint_filter]; intro _ _ ⟨_, h1⟩ ⟨_, h2⟩; omega
  have hlt_eq := halverAtLevel_non_last_count_eq (halvers := halvers) t h_pow_div w₁ hw₁ threshold
  change (Finset.univ.filter (fun pos : Fin n ↦
    pos.val < n - C ∧ (w₂ pos).val < threshold)).card =
    (Finset.univ.filter (fun pos : Fin n ↦
    pos.val < n - C ∧ (w₁ pos).val < threshold)).card at hlt_eq
  linarith [hpart w₂, hpart w₁]

/-- Near outsider bound for the FINAL direction: positions in `[n-C, n-H)` of
    the last chunk with large output values are bounded by `ε₁ * a`. -/
private lemma halverAtLevel_near_outsider_le_final {n : ℕ}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)} {ε₁ : ℝ} (t : ℕ)
    (w₁ : Fin n → Fin n) (hw₁ : Function.Injective w₁)
    (hhalver : ∀ m, IsEpsilonHalver (halvers m) ε₁) (hε₁ : 0 ≤ ε₁)
    (h_even : 2 ∣ n / 2 ^ t) (h_pow_div : 2 ^ t ∣ n)
    (k : ℕ) (hk : k ≤ n / 2 ^ t / 2) :
    let C := n / 2 ^ t
    let H := C / 2
    let w₂ := (halverAtLevel n halvers t).exec w₁
    let a := (Finset.univ.filter (fun pos : Fin n ↦
        n - C ≤ pos.val ∧ n - k ≤ (w₁ pos).val)).card
    ((Finset.univ.filter (fun pos : Fin n ↦
        n - C ≤ pos.val ∧ pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card : ℝ) ≤ ε₁ * ↑a := by
  intro C H w₂ a
  have h2H_eq : 2 * H = C := by have := Nat.div_mul_cancel h_even; omega
  have hC_le_n : C ≤ n := Nat.div_le_self n _
  have h2H_le_n : 2 * H ≤ n := by omega
  -- Trivial when H = 0
  by_cases hH : H = 0
  · have hC0 : C = 0 := by omega
    have hempty : (Finset.univ.filter (fun pos : Fin n ↦
        n - C ≤ pos.val ∧ pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro pos _ ⟨_, h, _⟩; omega
    rw [hempty]; simp; exact mul_nonneg hε₁ (Nat.cast_nonneg _)
  · -- H > 0
    have hH_pos : 0 < H := Nat.pos_of_ne_zero hH
    have h2H_pos : 0 < 2 * H := by omega
    -- Local restriction u : Fin (2*H) → Fin n
    set u : Fin (2 * H) → Fin n :=
      fun j ↦ w₁ ⟨(n - C) + j.val, by have := j.isLt; omega⟩ with hu_def
    have hu_inj : Function.Injective u := by
      intro j₁ j₂ heq
      have h := hw₁ heq
      exact Fin.ext (by have := congr_arg Fin.val h; dsimp at this; omega)
    -- ha_eq: count a on Fin (2*H) = count a on Fin n restricted to [n-C, n)
    have ha_eq : a = (Finset.univ.filter (fun i : Fin (2 * H) ↦ n - k ≤ (u i).val)).card := by
      apply Finset.card_nbij'
        (fun pos : Fin n ↦
          if h : n - C ≤ pos.val then ⟨pos.val - (n - C), by omega⟩ else ⟨0, h2H_pos⟩)
        (fun i : Fin (2 * H) ↦ ⟨(n - C) + i.val, by have := i.isLt; omega⟩)
      · intro pos hpos
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
        rw [dif_pos hpos.1]
        show n - k ≤ (u ⟨pos.val - (n - C), _⟩).val
        simp only [hu_def]
        have heq : (⟨(n - C) + (pos.val - (n - C)), (by omega)⟩ : Fin n) = pos := by
          ext; show (n - C) + (pos.val - (n - C)) = pos.val; omega
        rw [heq]; exact hpos.2
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact ⟨by omega, hi⟩
      · intro pos hpos
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos
        ext; simp only [dif_pos hpos.1]
        show (n - C) + (pos.val - (n - C)) = pos.val; omega
      · intro i _
        ext; simp only [dif_pos (show n - C ≤ (n - C) + i.val from by omega)]
        show (n - C) + i.val - (n - C) = i.val; omega
    -- a ≤ H
    have ha_le : (Finset.univ.filter (fun i : Fin (2 * H) ↦ n - k ≤ (u i).val)).card ≤ H := by
      calc _ ≤ k := injective_count_ge_le u hu_inj k
        _ ≤ H := hk
    -- hcard_eq: LHS on Fin n = LHS on Fin (2*H)
    have hcard_eq : (Finset.univ.filter (fun pos : Fin n ↦
        n - C ≤ pos.val ∧ pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card =
      (Finset.univ.filter (fun pos : Fin (2 * H) ↦
        pos.val < H ∧ n - k ≤ ((halvers H).exec u pos).val)).card := by
      apply Finset.card_nbij'
        (fun pos : Fin n ↦
          if h : n - C ≤ pos.val then ⟨pos.val - (n - C), by omega⟩ else ⟨0, h2H_pos⟩)
        (fun i : Fin (2 * H) ↦ ⟨(n - C) + i.val, by have := i.isLt; omega⟩)
      · -- forward
        intro pos hpos
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
        rw [dif_pos hpos.1]
        refine ⟨by show pos.val - (n - C) < H; omega, ?_⟩
        -- Use halverAtLevel_local_eq_last
        have hlocal := halverAtLevel_local_eq_last (halvers := halvers) t h_pow_div w₁ pos hpos.1
          (show pos.val < n - C + 2 * H by omega)
        show n - k ≤ ((halvers H).exec u ⟨pos.val - (n - C), _⟩).val
        simp only [hu_def]
        rw [← hlocal]; exact hpos.2.2
      · -- backward
        intro i hi
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        obtain ⟨hi_lt, hi_val⟩ := hi
        refine ⟨by omega, offset_add_lt_sub h2H_eq hC_le_n hi_lt, ?_⟩
        change n - k ≤ ((halverAtLevel n halvers t).exec w₁ ⟨(n - C) + i.val, _⟩).val
        have hlocal := halverAtLevel_local_eq_last (halvers := halvers) t h_pow_div w₁
          (⟨(n - C) + i.val, by have := i.isLt; omega⟩ : Fin n)
          (show n - C ≤ (n - C) + i.val from by omega)
          (show (n - C) + i.val < n - C + 2 * H from by have := i.isLt; omega)
        rw [hlocal]
        have hfin : (⟨(n - C) + i.val - (n - C), (by omega)⟩ : Fin (2 * H)) = i := by
          ext; show (n - C) + i.val - (n - C) = i.val; omega
        rw [hfin]
        exact hi_val
      · -- left inverse
        intro pos hpos
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos
        ext; simp only [dif_pos hpos.1]
        show (n - C) + (pos.val - (n - C)) = pos.val; omega
      · -- right inverse
        intro i _
        ext; simp only [dif_pos (show n - C ≤ (n - C) + i.val from by omega)]
        show (n - C) + i.val - (n - C) = i.val; omega
    -- Apply halver_injective_final_halved
    have hhalved := halver_injective_final_halved (hhalver H) hε₁ u hu_inj (n - k) ha_le
    calc ((Finset.univ.filter (fun pos : Fin n ↦
          n - C ≤ pos.val ∧ pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card : ℝ)
        = ↑(Finset.univ.filter (fun pos : Fin (2 * H) ↦
            pos.val < H ∧ n - k ≤ ((halvers H).exec u pos).val)).card := by
          exact_mod_cast hcard_eq
      _ ≤ ε₁ * ↑(Finset.univ.filter (fun i : Fin (2 * H) ↦ n - k ≤ (u i).val)).card := hhalved
      _ = ε₁ * ↑a := by rw [← ha_eq]


/-! **Induction step: SepFinal assembly** -/

/-- SepFinal direction of the halving step. -/
private lemma separator_halving_step_final {n : ℕ} {ε' ε₁ : ℝ} (t : ℕ)
    {net : ComparatorNetwork n}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)}
    (hsep : IsSeparator net (1 / 2 ^ t) ε')
    (hhalver : ∀ m, IsEpsilonHalver (halvers m) ε₁)
    (hε₁ : 0 ≤ ε₁)
    (h_even : 2 ∣ n / 2 ^ t)
    (h_pow_div : 2 ^ t ∣ n)
    (v : Equiv.Perm (Fin n)) :
    SepFinal
      ((⟨net.comparators ++ (halverAtLevel n halvers t).comparators⟩ :
        ComparatorNetwork n).exec (v : Fin n → Fin n))
      (1 / 2 ^ (t + 1))
      (ε' + ε₁) := by
  rw [ComparatorNetwork.exec_append]
  set w₁ := net.exec (v : Fin n → Fin n) with hw₁_def
  have hw₁_inj : Function.Injective w₁ :=
    ComparatorNetwork.exec_injective net (Equiv.injective v)
  set w₂ := (halverAtLevel n halvers t).exec w₁ with hw₂_def
  set C := n / 2 ^ t with hC_def
  set H := C / 2 with hH_def
  have hC_le_n : C ≤ n := Nat.div_le_self n _
  have hH_le_C : H ≤ C := Nat.div_le_self C 2
  show SepInitial (α := (Fin n)ᵒᵈ) _ _ _
  intro γ' hγ' hγ'_le
  simp only [Fintype.card_orderDual, Fintype.card_fin, rank_fin_od]
  rw [floor_pow_half_eq_div n (t + 1), ← half_chunk_eq n t]
  set k := ⌊γ' * (n : ℝ)⌋₊ with hk_def
  have hk_le : k ≤ H := by
    calc k ≤ n / 2 ^ (t + 1) := floor_gamma_le_div_pow n (t + 1) γ' hγ' hγ'_le
      _ = H := (half_chunk_eq n t).symm
  suffices h : ((Finset.univ.filter (fun pos : Fin n ↦
      pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card : ℝ) ≤ (ε' + ε₁) * γ' * ↑n by
    calc ((Finset.univ.filter (fun pos : (Fin n)ᵒᵈ ↦
          H ≤ n - 1 - (pos : Fin n).val ∧
          n - 1 - (w₂ pos : Fin n).val < k)).card : ℝ)
        = ((Finset.univ.filter (fun pos : Fin n ↦
            pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card : ℝ) := by
          congr 1
          apply Finset.card_nbij'
            (fun a : (Fin n)ᵒᵈ ↦ (a : Fin n))
            (fun b : Fin n ↦ (b : (Fin n)ᵒᵈ))
          · intro a ha
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
            exact ⟨by have := (a : Fin n).isLt; omega, by have := (w₂ a : Fin n).isLt; omega⟩
          · intro b hb
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
            exact ⟨by have := b.isLt; omega, by have := (w₂ b).isLt; omega⟩
          · intro _ _; rfl
          · intro _ _; rfl
      _ ≤ _ := h
  have hpart : (Finset.univ.filter (fun pos : Fin n ↦
      pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card =
    (Finset.univ.filter (fun pos : Fin n ↦
      n - C ≤ pos.val ∧ pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card +
    (Finset.univ.filter (fun pos : Fin n ↦
      pos.val < n - C ∧ n - k ≤ (w₂ pos).val)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext pos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro ⟨hlt, hval⟩
        by_cases hpos : n - C ≤ pos.val
        · left; exact ⟨hpos, hlt, hval⟩
        · right; exact ⟨by omega, hval⟩
      · rintro (⟨_, hlt, hval⟩ | ⟨hlt, hval⟩)
        · exact ⟨hlt, hval⟩
        · exact ⟨by omega, hval⟩
    · rw [Finset.disjoint_filter]
      intro pos _ ⟨hge, _, _⟩ ⟨hlt, _⟩; omega
  have hnear : ((Finset.univ.filter (fun pos : Fin n ↦
      n - C ≤ pos.val ∧ pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card : ℝ) ≤
    ε₁ * ↑(Finset.univ.filter (fun pos : Fin n ↦
      n - C ≤ pos.val ∧ n - k ≤ (w₁ pos).val)).card := by
    rw [hw₂_def]
    exact halverAtLevel_near_outsider_le_final t w₁ hw₁_inj hhalver hε₁ h_even h_pow_div k hk_le
  have hfar_eq : (Finset.univ.filter (fun pos : Fin n ↦
      pos.val < n - C ∧ n - k ≤ (w₂ pos).val)).card =
    (Finset.univ.filter (fun pos : Fin n ↦
      pos.val < n - C ∧ n - k ≤ (w₁ pos).val)).card := by
    rw [hw₂_def]; exact far_outsider_count_preserved_final t h_pow_div w₁ hw₁_inj (n - k)
  have hγ'_le_t : γ' ≤ 1 / 2 ^ t := by
    calc γ' ≤ 1 / 2 ^ (t + 1) := hγ'_le
      _ ≤ 1 / 2 ^ t :=
        div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) < 2 ^ t)
          (by exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.le_succ t))
  have hsep_far : ((Finset.univ.filter (fun pos : Fin n ↦
      pos.val < n - C ∧ n - k ≤ (w₁ pos).val)).card : ℝ) ≤ ε' * γ' * ↑n := by
    have hfinal := (hsep v).2 γ' hγ' hγ'_le_t
    simp only [Fintype.card_orderDual, Fintype.card_fin, rank_fin_od] at hfinal
    rw [floor_pow_half_eq_div n t, ← hw₁_def, ← hk_def] at hfinal
    have hconv : (Finset.univ.filter (fun pos : (Fin n)ᵒᵈ ↦
        C ≤ n - 1 - (pos : Fin n).val ∧
        n - 1 - (w₁ pos : Fin n).val < k)).card =
      (Finset.univ.filter (fun pos : Fin n ↦
        pos.val < n - C ∧ n - k ≤ (w₁ pos).val)).card := by
      apply Finset.card_nbij'
        (fun a : (Fin n)ᵒᵈ ↦ (a : Fin n))
        (fun b : Fin n ↦ (b : (Fin n)ᵒᵈ))
      · intro a ha
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        exact ⟨by have := (a : Fin n).isLt; omega, by have := (w₁ a : Fin n).isLt; omega⟩
      · intro b hb
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        exact ⟨by have := b.isLt; omega, by have := (w₁ b).isLt; omega⟩
      · intro _ _; rfl
      · intro _ _; rfl
    rw [← hconv]; exact hfinal
  set a := (Finset.univ.filter (fun pos : Fin n ↦
      n - C ≤ pos.val ∧ n - k ≤ (w₁ pos).val)).card with ha_def
  have ha_le_k : a ≤ k := by
    calc a ≤ (Finset.univ.filter (fun pos : Fin n ↦ n - k ≤ (w₁ pos).val)).card := by
          apply Finset.card_le_card; intro pos
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact And.right
      _ ≤ k := injective_count_ge_le w₁ hw₁_inj k
  have ha_le : (a : ℝ) ≤ γ' * ↑n := by
    calc (a : ℝ) ≤ ↑k := by exact_mod_cast ha_le_k
      _ ≤ γ' * ↑n := Nat.floor_le (mul_nonneg hγ' (Nat.cast_nonneg _))
  calc ((Finset.univ.filter (fun pos : Fin n ↦
        pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card : ℝ)
      = ↑(Finset.univ.filter (fun pos : Fin n ↦
          n - C ≤ pos.val ∧ pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card +
        ↑(Finset.univ.filter (fun pos : Fin n ↦
          pos.val < n - C ∧ n - k ≤ (w₂ pos).val)).card := by exact_mod_cast hpart
    _ ≤ ε₁ * ↑a + ε' * γ' * ↑n := by
        have : ((Finset.univ.filter (fun pos : Fin n ↦
            pos.val < n - C ∧ n - k ≤ (w₂ pos).val)).card : ℝ) ≤ ε' * γ' * ↑n := by
          rw [hfar_eq]; exact hsep_far
        linarith [hnear]
    _ ≤ ε₁ * (γ' * ↑n) + ε' * γ' * ↑n := by
        linarith [mul_le_mul_of_nonneg_left ha_le hε₁]
    _ = (ε' + ε₁) * γ' * ↑n := by ring


/-! **Induction step: assembly** -/

/-- SepInitial direction of the halving step. -/
private lemma separator_halving_step_initial {n : ℕ} {ε' ε₁ : ℝ} (t : ℕ)
    {net : ComparatorNetwork n}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)}
    (hsep : IsSeparator net (1 / 2 ^ t) ε')
    (hhalver : ∀ m, IsEpsilonHalver (halvers m) ε₁)
    (hε₁ : 0 ≤ ε₁)
    (h_even : 2 ∣ n / 2 ^ t)
    (v : Equiv.Perm (Fin n)) :
    SepInitial
      ((⟨net.comparators ++ (halverAtLevel n halvers t).comparators⟩ :
        ComparatorNetwork n).exec (v : Fin n → Fin n))
      (1 / 2 ^ (t + 1))
      (ε' + ε₁) := by
  rw [ComparatorNetwork.exec_append]
  set w₁ := net.exec (v : Fin n → Fin n) with hw₁_def
  have hw₁_inj : Function.Injective w₁ :=
    ComparatorNetwork.exec_injective net (Equiv.injective v)
  intro γ' hγ' hγ'_le
  simp only [Fintype.card_fin, rank_fin_val]
  rw [floor_pow_half_eq_div n (t + 1), ← half_chunk_eq n t]
  set k := ⌊γ' * (n : ℝ)⌋₊ with hk_def
  set w₂ := (halverAtLevel n halvers t).exec w₁ with hw₂_def
  have hk_le : k ≤ n / 2 ^ t / 2 := by
    calc k ≤ n / 2 ^ (t + 1) := floor_gamma_le_div_pow n (t + 1) γ' hγ' hγ'_le
      _ = n / 2 ^ t / 2 := (half_chunk_eq n t).symm
  -- Split {pos ≥ n/2^t/2 : w₂(pos) < k} into near [n/2^t/2, n/2^t) and far [n/2^t, n)
  have hpart : (Finset.univ.filter (fun pos : Fin n ↦
      n / 2 ^ t / 2 ≤ pos.val ∧ (w₂ pos).val < k)).card =
    (Finset.univ.filter (fun pos : Fin n ↦
      n / 2 ^ t / 2 ≤ pos.val ∧ pos.val < n / 2 ^ t ∧ (w₂ pos).val < k)).card +
    (Finset.univ.filter (fun pos : Fin n ↦
      n / 2 ^ t ≤ pos.val ∧ (w₂ pos).val < k)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext pos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro ⟨hge, hlt⟩
        by_cases hpos : pos.val < n / 2 ^ t
        · left; exact ⟨hge, hpos, hlt⟩
        · right; exact ⟨by omega, hlt⟩
      · rintro (⟨hge, _, hlt⟩ | ⟨hge, hlt⟩)
        · exact ⟨hge, hlt⟩
        · exact ⟨le_trans (Nat.div_le_self _ 2) hge, hlt⟩
    · rw [Finset.disjoint_filter]
      intro pos _ ⟨_, hlt, _⟩ ⟨hge, _⟩; omega
  -- Near outsider bound
  have hnear : ((Finset.univ.filter (fun pos : Fin n ↦
      n / 2 ^ t / 2 ≤ pos.val ∧ pos.val < n / 2 ^ t ∧ (w₂ pos).val < k)).card : ℝ) ≤
    ε₁ * ↑(Finset.univ.filter (fun pos : Fin n ↦
      pos.val < n / 2 ^ t ∧ (w₁ pos).val < k)).card := by
    rw [hw₂_def]
    exact halverAtLevel_near_outsider_le t w₁ hw₁_inj hhalver hε₁ h_even k hk_le
  -- Far outsider preservation
  have hfar_eq : (Finset.univ.filter (fun pos : Fin n ↦
      n / 2 ^ t ≤ pos.val ∧ (w₂ pos).val < k)).card =
    (Finset.univ.filter (fun pos : Fin n ↦
      n / 2 ^ t ≤ pos.val ∧ (w₁ pos).val < k)).card := by
    rw [hw₂_def]; exact far_outsider_count_preserved t w₁ hw₁_inj k
  -- γ' ≤ 1/2^t
  have hγ'_le_t : γ' ≤ 1 / 2 ^ t := by
    calc γ' ≤ 1 / 2 ^ (t + 1) := hγ'_le
      _ ≤ 1 / 2 ^ t :=
        div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) < 2 ^ t)
          (by exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.le_succ t))
  -- From hsep: far outsiders bounded by ε' * γ' * n
  have hsep_far : ((Finset.univ.filter (fun pos : Fin n ↦
      n / 2 ^ t ≤ pos.val ∧ (w₁ pos).val < k)).card : ℝ) ≤ ε' * γ' * ↑n := by
    have h := (hsep v).1 γ' hγ' hγ'_le_t
    simp only [Fintype.card_fin, rank_fin_val] at h
    rw [floor_pow_half_eq_div n t, ← hw₁_def, ← hk_def] at h
    exact h
  -- a = count at positions < n/2^t with values < k
  set a := (Finset.univ.filter (fun pos : Fin n ↦
      pos.val < n / 2 ^ t ∧ (w₁ pos).val < k)).card with ha_def
  have ha_le_k : a ≤ k := by
    calc a ≤ (Finset.univ.filter (fun pos : Fin n ↦ (w₁ pos).val < k)).card := by
          apply Finset.card_le_card; intro pos
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact And.right
      _ ≤ k := injective_count_lt_le w₁ hw₁_inj k
  have ha_le : (a : ℝ) ≤ γ' * ↑n := by
    calc (a : ℝ) ≤ ↑k := by exact_mod_cast ha_le_k
      _ ≤ γ' * ↑n := Nat.floor_le (mul_nonneg hγ' (Nat.cast_nonneg _))
  calc ((Finset.univ.filter (fun pos : Fin n ↦
        n / 2 ^ t / 2 ≤ pos.val ∧ (w₂ pos).val < k)).card : ℝ)
      = ↑(Finset.univ.filter (fun pos : Fin n ↦
          n / 2 ^ t / 2 ≤ pos.val ∧ pos.val < n / 2 ^ t ∧ (w₂ pos).val < k)).card +
        ↑(Finset.univ.filter (fun pos : Fin n ↦
          n / 2 ^ t ≤ pos.val ∧ (w₂ pos).val < k)).card := by exact_mod_cast hpart
    _ ≤ ε₁ * ↑a + ε' * γ' * ↑n := by
        have : ((Finset.univ.filter (fun pos : Fin n ↦
            n / 2 ^ t ≤ pos.val ∧ (w₂ pos).val < k)).card : ℝ) ≤ ε' * γ' * ↑n := by
          rw [hfar_eq]; exact hsep_far
        linarith [hnear]
    _ ≤ ε₁ * (γ' * ↑n) + ε' * γ' * ↑n := by
        linarith [mul_le_mul_of_nonneg_left ha_le hε₁]
    _ = (ε' + ε₁) * γ' * ↑n := by ring

/-- Halving refines separation: given (1/2^t, ε')-separation, applying
    ε₁-halvers at level `t` gives (1/2^(t+1), ε' + ε₁)-separation.

    Requires `2 ∣ n / 2^t` (chunk size is even) so that `2 * halfChunk`
    covers the full chunk — without this, the last position of each chunk
    is uncovered and can strand a small value (confirmed counterexample:
    n=3, t=0 with perfect halvers).

    The level must match the separation parameter (γ = 1/2^t aligns with
    chunk size n/2^t at level t). Within each chunk, the halver pushes
    the smaller half to the first half-chunk, creating the finer boundary.

    Error analysis (SepInitial direction, γ' ≤ 1/2^(t+1)):
    • Positions ≥ n/2^t (other chunks): unchanged from old separation → ≤ ε'·γ'·n
    • Positions [n/2^(t+1), n/2^t) (second half of chunk 0): by the halver's
      EpsilonInitialHalved, at most ε₁·a displaced, where a ≤ k = ⌊γ'n⌋.
    Total: (ε' + ε₁)·γ'·n. SepFinal is symmetric.
    (Seiferas 2009, Section 6, proof of Lemma 1) -/
theorem separator_halving_step {n : ℕ} {ε' ε₁ : ℝ} (t : ℕ)
    {net : ComparatorNetwork n}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)}
    (hsep : IsSeparator net (1 / 2 ^ t) ε')
    (hhalver : ∀ m, IsEpsilonHalver (halvers m) ε₁)
    (hε₁ : 0 ≤ ε₁)
    (h_even : 2 ∣ n / 2 ^ t)
    (h_pow_div : 2 ^ t ∣ n) :
    IsSeparator
      { comparators := net.comparators ++ (halverAtLevel n halvers t).comparators }
      (1 / 2 ^ (t + 1))
      (ε' + ε₁) := by
  intro v
  exact ⟨separator_halving_step_initial t hsep hhalver hε₁ h_even v,
         separator_halving_step_final t hsep hhalver hε₁ h_even h_pow_div v⟩


/-! **Iterated halving** -/

/-- `t` levels of iterated ε-halving give (t·ε)-approximate (1/2^t)-separation.

    Requires `2 ^ t ∣ n` to ensure all chunk sizes at levels 0, ..., t-1
    are even (needed by `separator_halving_step`). This is satisfied when
    n is a power of 2 ≥ 2^t, as in the standard AKS construction.

    Proof: induction on `t` using `halver_isSeparator_half` (base) and
    `separator_halving_step` (step). At each level, the halver introduces
    ε error (one application of EpsilonInitialHalved + EpsilonFinalHalved),
    giving +ε per level, total t·ε.
    (Seiferas 2009, Section 6, Lemma 1) -/
theorem halverToSeparator_isSeparator {ε : ℝ} {d : ℕ}
    (n : ℕ) (family : HalverFamily ε d) (t : ℕ) (hε : 0 ≤ ε)
    (h_div : 2 ^ t ∣ n) :
    IsSeparator (halverToSeparator n family t) (1 / 2 ^ t) (↑t * ε) := by
  sorry


/-! **Depth bound** -/

/-- Per-level depth bound: halvers at one tree level operate on disjoint
    wire ranges (different sub-intervals), so they run in parallel. -/
theorem halverAtLevel_depth_le {ε : ℝ} {d : ℕ}
    (n : ℕ) (family : HalverFamily ε d) (level : ℕ) :
    (halverAtLevel n family.net level).depth ≤ d := by
  sorry

/-- Iterated separator depth ≤ t · d. At each of `t` levels, halvers at the
    same level operate on disjoint wire ranges, giving depth ≤ d per level.
    Levels are sequential (concatenated), so total depth ≤ t · d. -/
theorem halverToSeparator_depth_le {ε : ℝ} {d : ℕ}
    (n : ℕ) (family : HalverFamily ε d) (t : ℕ) :
    (halverToSeparator n family t).depth ≤ t * d := by
  sorry


/-! **Bundle into SeparatorFamily** -/

/-- Separator property for a specific `n` with divisibility.
    Use this instead of `SeparatorFamily` when the divisibility condition
    `2 ^ t ∣ n` is not universally satisfied.
    (Seiferas 2009, Section 6, Lemma 1) -/
theorem halverToSeparator_props {ε : ℝ} {d : ℕ} (family : HalverFamily ε d)
    (n t : ℕ) (hε : 0 ≤ ε) (h_div : 2 ^ t ∣ n) :
    IsSeparator (halverToSeparator n family t) (1 / 2 ^ t) (↑t * ε) ∧
    (halverToSeparator n family t).depth ≤ t * d :=
  ⟨halverToSeparator_isSeparator n family t hε h_div,
   halverToSeparator_depth_le n family t⟩
