/-
  # Stranger Bounds for the Split

  Proves the stranger-count hypotheses of `invariant_maintained` for any
  split where `toParent ⊆ bags` (Seiferas 2009, Section 5).

  All theorems in this file are **sorry-free**: the separator-dependent
  bounds (`hfilter`, `hcnative`) are taken as explicit parameters.
  Concrete-split-specific instantiations (with sorry's) are in
  `SplitStranger` section below and assembled in `SplitProof.lean`.

  Key results:
  - `jStrangerCount_level_shift`: j-strangers at (l-1, i/2) = (j+1)-strangers at (l, i)
  - `kick_stranger_bound`: fringe items have ≤ λε^j·cap strangers at parent level
  - `parent_stranger_bound`: items from parent have ≤ λε^(j-1)·cap strangers
  - `parent_1stranger_from_inv`: 1-strangers from parent ≤ parentStrangerCoeff·cap
-/

import AKS.Bags.Invariant
import AKS.Bags.Split

open Finset

/-! **Level-Shift Identity**

Being j-strange at (l-1, i/2) is the same as being (j+1)-strange at (l, i).
This is the key identity connecting parent-level and child-level stranger counts.
Proof: both reduce to `nativeBagIdx n (l-j) r ≠ i / 2^j` after Nat arithmetic. -/

/-- `i / 2 / 2^(j-1) = i / 2^j` for `j ≥ 1`. -/
private theorem div2_div_pow_eq {i j : ℕ} (hj : 1 ≤ j) :
    i / 2 / 2 ^ (j - 1) = i / 2 ^ j := by
  rw [Nat.div_div_eq_div_mul]
  congr 1
  calc 2 * 2 ^ (j - 1) = 2 ^ 1 * 2 ^ (j - 1) := by norm_num
    _ = 2 ^ (1 + (j - 1)) := (pow_add 2 1 (j - 1)).symm
    _ = 2 ^ j := by congr 1; omega

/-- Level-shift for stranger counts: j-strangers at parent (l-1, i/2)
    equal (j+1)-strangers at child (l, i). Both reduce to
    `nativeBagIdx n (l-j) r ≠ i / 2^j`. -/
theorem jStrangerCount_level_shift {n : ℕ} (perm : Fin n → Fin n)
    (S : Finset (Fin n)) {l i j : ℕ} (hj : 1 ≤ j) (hl : 1 ≤ l) :
    jStrangerCount n perm S (l - 1) (i / 2) j = jStrangerCount n perm S l i (j + 1) := by
  simp only [jStrangerCount]
  congr 1; ext x; simp only [mem_filter, isJStranger]
  -- After unfolding, both sides have the form:
  --   x ∈ S ∧ (bound₁ ∧ bound₂ ∧ nativeBagIdx n (l-j) r ≠ i / 2^j)
  -- Rewrite Nat expressions to canonical form
  have hlj : l - 1 - (j - 1) = l - j := by omega
  have hjl : j + 1 - 1 = j := by omega
  have hdiv : i / 2 / 2 ^ (j - 1) = i / 2 ^ j := div2_div_pow_eq hj
  rw [hlj, hjl, hdiv]
  -- Now both sides differ only in numeric bounds, which are equivalent
  constructor
  · rintro ⟨hm, -, h2, hne⟩; exact ⟨hm, by omega, by omega, hne⟩
  · rintro ⟨hm, -, h2, hne⟩; exact ⟨hm, hj, by omega, hne⟩

/-! **Kick Stranger Bound**

Fringe items kicked from child (l, i) to parent (l-1, i/2) have few
strangers at the parent level. The bound follows from:
1. `toParent ⊆ bags l i` (structural)
2. Level shift: j-strangers at parent = (j+1)-strangers at child
3. Subset monotonicity
4. Invariant's stranger bound at j+1 -/

/-- Stranger count of kicked items at the parent level is bounded by the
    invariant's stranger bound at the child level with shifted index.
    This is the `hkick_stranger` hypothesis of `invariant_maintained`. -/
theorem kick_stranger_bound {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (split : ℕ → ℕ → SplitResult n)
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hlam : 0 ≤ lam) (hε : 0 ≤ ε) (hν : 0 ≤ ν)
    (hsplit_sub : ∀ l i,
      (split l i).toParent ⊆ bags l i ∧
      (split l i).toLeftChild ⊆ bags l i ∧
      (split l i).toRightChild ⊆ bags l i)
    (l i j : ℕ) (hj : 1 ≤ j) :
    (jStrangerCount n perm (split l i).toParent (l - 1) (i / 2) j : ℝ) ≤
    lam * ε ^ j * bagCapacity n A ν t l := by
  by_cases hl : l = 0
  · -- Level 0: (l-1) = 0, j ≥ 1 > 0 = level, so no j-strangers
    subst hl
    rw [jStrangerCount_zero_gt_level perm _ (by omega : 0 < j)]
    simp only [Nat.cast_zero]
    apply mul_nonneg (mul_nonneg hlam (pow_nonneg hε _))
    unfold bagCapacity; positivity
  · -- Level ≥ 1: use level shift + subset monotonicity + invariant
    have hl1 : 1 ≤ l := by omega
    calc (jStrangerCount n perm (split l i).toParent (l - 1) (i / 2) j : ℝ)
        ≤ (jStrangerCount n perm (bags l i) (l - 1) (i / 2) j : ℝ) := by
          exact_mod_cast jStrangerCount_mono (hsplit_sub l i).1 _ _ _
      _ = (jStrangerCount n perm (bags l i) l i (j + 1) : ℝ) := by
          rw [jStrangerCount_level_shift perm _ hj hl1]
      _ ≤ lam * ε ^ j * bagCapacity n A ν t l :=
          inv.stranger_bound l i (j + 1) (by omega)

/-! **Parent Stranger Bound (j ≥ 2)**

Items received from parent have few j-strangers (j ≥ 2) at the child level.
The bound requires the separator's filtering property (`hfilter`): the fringe
captures most strangers from the parent bag, and only an ε fraction leak
through to the children.

Seiferas (2009, Section 5): "at most fraction ε of the few smallest (or
largest) are permuted far out of place." -/

/-- Parent stranger bound for j ≥ 2: the `hparent_stranger` hypothesis
    of `invariant_maintained`.

    **Proof** (Seiferas Section 5):
    1. Level shift: j-strangers at (level, idx) = (j-1)-strangers at parent
    2. Filtering (`hfilter`): at most ε fraction of parent's strangers leak
    3. Invariant: parent has ≤ `lam·ε^(j-2)·cap(parent)` strangers
    Combining: `ε · lam·ε^(j-2) · cap = lam·ε^(j-1) · cap`. -/
theorem parent_stranger_bound {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (split : ℕ → ℕ → SplitResult n)
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hlam : 0 ≤ lam) (hε : 0 ≤ ε)
    (hfilter : ∀ level idx j, 1 ≤ j → 1 ≤ level →
      (jStrangerCount n perm (fromParent split level idx)
        (level - 1) (idx / 2) j : ℝ) ≤
      ε * ↑(jStrangerCount n perm (bags (level - 1) (idx / 2))
        (level - 1) (idx / 2) j))
    (level idx j : ℕ) (hj : 2 ≤ j) :
    (jStrangerCount n perm (fromParent split level idx) level idx j : ℝ) ≤
    lam * ε ^ (j - 1) * bagCapacity n A ν t (level - 1) := by
  by_cases hlev : level = 0
  · -- Level 0: fromParent = ∅
    subst hlev; simp only [fromParent, ite_true]
    rw [jStrangerCount_empty]; simp only [Nat.cast_zero]
    apply mul_nonneg (mul_nonneg hlam (pow_nonneg hε _))
    -- Derive 0 ≤ cap from invariant: card ≥ 0 and card ≤ cap
    have hcap := inv.capacity_bound 0 (idx / 2)
    have hcard : (0 : ℝ) ≤ ↑(bags 0 (idx / 2)).card := Nat.cast_nonneg _
    linarith
  · -- Level ≥ 1: level shift + filtering + invariant
    have hl : 1 ≤ level := by omega
    -- Step 1: j-strangers at child = (j-1)-strangers at parent
    have h_shift : jStrangerCount n perm (fromParent split level idx) level idx j =
        jStrangerCount n perm (fromParent split level idx) (level - 1) (idx / 2) (j - 1) := by
      have h := jStrangerCount_level_shift (i := idx) perm (fromParent split level idx)
        (show 1 ≤ j - 1 from by omega) hl
      have : (j - 1) + 1 = j := by omega
      rw [this] at h; exact h.symm
    calc (jStrangerCount n perm (fromParent split level idx) level idx j : ℝ)
        = (jStrangerCount n perm (fromParent split level idx)
            (level - 1) (idx / 2) (j - 1) : ℝ) := by exact_mod_cast h_shift
      _ ≤ ε * ↑(jStrangerCount n perm (bags (level - 1) (idx / 2))
            (level - 1) (idx / 2) (j - 1)) :=
          hfilter level idx (j - 1) (by omega) hl
      _ ≤ ε * (lam * ε ^ ((j - 1) - 1) * bagCapacity n A ν t (level - 1)) :=
          mul_le_mul_of_nonneg_left
            (inv.stranger_bound (level - 1) (idx / 2) (j - 1) (by omega)) hε
      _ = lam * ε ^ (j - 1) * bagCapacity n A ν t (level - 1) := by
          have h1 : (j - 1) - 1 = j - 2 := by omega
          have h2 : j - 1 = 1 + (j - 2) := by omega
          rw [h1, h2, pow_add, pow_one]; ring

/-! **Parent 1-Stranger Bound**

The hardest case: bounding 1-strangers among items from parent.
Decomposes via `parent_1stranger_bound` (proved in `Invariant.lean`) into:
- 2-strangers among fromParent (from `parent_stranger_bound` at j=2)
- Sibling-native items among fromParent (`hcnative`) -/

/-- Parent 1-stranger bound: the `hparent_1stranger` hypothesis of
    `invariant_maintained`. Assembles via `parent_1stranger_bound`
    from the 2-stranger bound and sibling-native bound.

    The two separator-dependent hypotheses:
    - `hfilter`: ε-filtering of parent-level strangers (gates j=2 bound)
    - `hcnative`: sibling-native items from parent ≤ cnativeCoeff·cap -/
theorem parent_1stranger_from_inv {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (split : ℕ → ℕ → SplitResult n)
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hparams : SatisfiesConstraints A ν lam ε)
    (hfilter : ∀ level idx j, 1 ≤ j → 1 ≤ level →
      (jStrangerCount n perm (fromParent split level idx)
        (level - 1) (idx / 2) j : ℝ) ≤
      ε * ↑(jStrangerCount n perm (bags (level - 1) (idx / 2))
        (level - 1) (idx / 2) j))
    (hcnative : ∀ level idx,
      (siblingNativeCount n perm (fromParent split level idx) level idx : ℝ) ≤
      cnativeCoeff A lam ε * bagCapacity n A ν t (level - 1))
    (level idx : ℕ) :
    (jStrangerCount n perm (fromParent split level idx) level idx 1 : ℝ) ≤
    parentStrangerCoeff A lam ε * bagCapacity n A ν t level := by
  obtain ⟨hA, hν, hν1, hlam, _, hε, _, hC4, _⟩ := hparams
  -- Derive (2εA)² < 1 from C4_gt1 + ν < 1
  have h2εA : (2 * ε * A) ^ 2 < 1 := by
    have hA_pos : (0 : ℝ) < A := by linarith
    have hεA : 2 * ε * A < 1 := by
      have := hC4; unfold SatisfiesC4_gt1 at this
      have : 1 / A > 0 := div_pos one_pos hA_pos
      linarith
    have hεA0 : 0 ≤ 2 * ε * A := by positivity
    calc (2 * ε * A) ^ 2 = (2 * ε * A) * (2 * ε * A) := sq (2 * ε * A)
      _ < 1 * 1 := mul_lt_mul hεA (le_of_lt hεA) (by positivity) (by linarith)
      _ = 1 := one_mul 1
  have hj2 : ∀ l i,
      (jStrangerCount n perm (fromParent split l i) l i 2 : ℝ) ≤
      lam * ε * bagCapacity n A ν t (l - 1) := by
    intro l i
    have h := parent_stranger_bound split inv hlam.le hε.le hfilter l i 2 (by omega)
    simpa using h
  exact parent_1stranger_bound split hA hν hlam.le hε.le h2εA hj2 hcnative level idx

/-! **Concrete Split: Stranger Bound Instantiations**

The following sorry'd lemmas specialize the abstract framework to
`concreteSplit` from `Split.lean`. They capture the two separator-dependent
properties needed by `parent_stranger_bound` and `parent_1stranger_from_inv`.

**Proof strategies** (validated by `rust/test-filtering-and-cnative.rs`):

For `concreteSplit_fromParent_filtered`:
  Parent-level j-strangers have `perm` values outside the parent's native
  interval, giving them extreme `rankInBag` values (lowest or highest ranks).
  The fringe captures items with extreme ranks, so most strangers go to
  `toParent`, not to children. The ε factor bounds the leakage when the fringe
  size `⌊λ·b⌋` doesn't quite capture all strangers on one side.
  Rust experiment: LHS = 0 in all tested cases (max ratio 0.0000).

For `concreteSplit_cnative_bound`:
  Sibling-native items in `fromParent` are items native to the parent but
  assigned to the wrong child. The concrete split assigns middle-left items
  to the left child and middle-right to the right child. The halving error
  (ε/2 term in cnativeCoeff) captures items whose native child doesn't match
  their rank-based assignment. Sources (c) and (d) in cnativeCoeff are zero
  for the concrete split (Rust experiment: max ratio 0.0000). -/

/-- Items with perm value below the parent's native interval are 1-strangers. -/
private theorem perm_below_isJStranger_one {n rank level idx : ℕ}
    (hlev : 1 ≤ level)
    (hbs : 0 < bagSize n level)
    (hlt : rank < idx * bagSize n level) :
    isJStranger n rank level idx 1 := by
  refine ⟨le_refl 1, hlev, ?_⟩
  simp only [Nat.sub_self, pow_zero, Nat.div_one, nativeBagIdx]
  exact Nat.ne_of_lt ((Nat.div_lt_iff_lt_mul hbs).mpr hlt)

/-- Items with perm value above the parent's native interval are 1-strangers. -/
private theorem perm_above_isJStranger_one {n rank level idx : ℕ}
    (hlev : 1 ≤ level)
    (hbs : 0 < bagSize n level)
    (hge : (idx + 1) * bagSize n level ≤ rank) :
    isJStranger n rank level idx 1 := by
  refine ⟨le_refl 1, hlev, ?_⟩
  simp only [Nat.sub_self, pow_zero, Nat.div_one, nativeBagIdx]
  exact Nat.ne_of_gt ((Nat.le_div_iff_mul_le hbs).mpr hge)

/-- Below-interval items in a bag form a subset of 1-strangers. -/
private theorem filter_below_subset_stranger {n : ℕ} (perm : Fin n → Fin n)
    (regs : Finset (Fin n)) {level idx : ℕ} (hlev : 1 ≤ level)
    (hbs : 0 < bagSize n level) :
    regs.filter (fun i ↦ (perm i).val < idx * bagSize n level) ⊆
    regs.filter (fun i ↦ isJStranger n (perm i).val level idx 1) := by
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, perm_below_isJStranger_one hlev hbs hx.2⟩

/-- Above-interval items in a bag form a subset of 1-strangers. -/
private theorem filter_above_subset_stranger {n : ℕ} (perm : Fin n → Fin n)
    (regs : Finset (Fin n)) {level idx : ℕ} (hlev : 1 ≤ level)
    (hbs : 0 < bagSize n level) :
    regs.filter (fun i ↦ (idx + 1) * bagSize n level ≤ (perm i).val) ⊆
    regs.filter (fun i ↦ isJStranger n (perm i).val level idx 1) := by
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, perm_above_isJStranger_one hlev hbs hx.2⟩

/-- Separator filtering for the concrete split: among items sent from parent
    to child, the stranger count at the parent level is at most `ε` times
    the full parent bag's stranger count.

    **Proof**: LHS = 0 because all j-strangers get extreme ranks (captured by
    the fringe), while fromParent items have middle ranks.
    Requires `n = 2^k` for `isJStranger_antitone` (j ≥ 2 case). -/
theorem concreteSplit_fromParent_filtered {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hn : ∃ k, n = 2 ^ k)
    (hlam : 0 ≤ lam) (hε : 0 ≤ ε)
    (level idx j : ℕ) (hj : 1 ≤ j) (hlev : 1 ≤ level) :
    (jStrangerCount n perm
      (fromParent (concreteSplit lam perm bags) level idx)
      (level - 1) (idx / 2) j : ℝ) ≤
    ε * ↑(jStrangerCount n perm (bags (level - 1) (idx / 2))
      (level - 1) (idx / 2) j) := by
  -- It suffices to show LHS = 0 (since 0 ≤ ε * RHS)
  suffices hsuff : jStrangerCount n perm
      (fromParent (concreteSplit lam perm bags) level idx)
      (level - 1) (idx / 2) j = 0 by
    rw [hsuff]; simp only [Nat.cast_zero]
    exact mul_nonneg hε (Nat.cast_nonneg _)
  -- Show the filter set is empty: no item in fromParent is a j-stranger
  rw [jStrangerCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi
  -- Unfold fromParent: i ∈ toLeftChild or toRightChild of parent split
  unfold fromParent at hi
  rw [if_neg (show level ≠ 0 by omega)] at hi
  -- Extract i ∈ parent bag, and rank bounds, from concreteSplit filter
  -- In both even/odd branches, after unfolding concreteSplit:
  -- toLeftChild items have f ≤ rank < f + h
  -- toRightChild items have f + h ≤ rank < f + 2h
  -- where h = childSendSize, f = fringeSize, all computed on bags (level-1) (idx/2)
  have h_mem : i ∈ bags (level - 1) (idx / 2) := by
    simp only [concreteSplit] at hi; split_ifs at hi <;> simp at hi <;> exact hi.1
  have h_rank_lb : fringeSize lam (bags (level - 1) (idx / 2)).card ≤
      rankInBag perm (bags (level - 1) (idx / 2)) i := by
    simp only [concreteSplit] at hi; split_ifs at hi <;> simp at hi
    · exact hi.2.1
    · exact le_trans (Nat.le_add_right _ _) hi.2.1
  have h_rank_ub : rankInBag perm (bags (level - 1) (idx / 2)) i <
      fringeSize lam (bags (level - 1) (idx / 2)).card +
      2 * childSendSize lam (bags (level - 1) (idx / 2)).card := by
    simp only [concreteSplit] at hi; split_ifs at hi <;> simp at hi
    · calc rankInBag perm (bags (level - 1) (idx / 2)) i
          < fringeSize lam (bags (level - 1) (idx / 2)).card +
            childSendSize lam (bags (level - 1) (idx / 2)).card := hi.2.2
        _ ≤ _ := by omega
    · exact hi.2.2
  -- Case: j > level - 1 → trivially not j-strange
  by_cases hjp : level - 1 < j
  · exact not_isJStranger_gt_level hjp
  push_neg at hjp
  -- Case: level = 1 (parent at level 0) → not strange at root
  by_cases hlev1 : level = 1
  · subst hlev1; exact not_isJStranger_at_root n (perm i).val (idx / 2) j
  have hplev1 : 1 ≤ level - 1 := by omega
  -- Derive n = 2^k, bagSize > 0, and level-1 ≤ k
  obtain ⟨k, rfl⟩ := hn
  have hkp : level - 1 ≤ k := by
    by_contra hc; push_neg at hc
    have hml : maxLevel (2 ^ k) < level - 1 := by
      unfold maxLevel; rw [Nat.log_pow (by omega : 1 < 2)]; omega
    have := inv.bounded_depth (level - 1) (idx / 2) hml
    rw [this] at h_mem; simp at h_mem
  have hbs : 0 < bagSize (2 ^ k) (level - 1) :=
    bagSize_pos (Nat.pow_le_pow_right (by omega : 0 < 2) hkp)
  -- Core: assume j-stranger, derive contradiction with middle rank
  intro hstr
  -- Reduce to 1-stranger
  have h1str : isJStranger (2 ^ k) (perm i).val (level - 1) (idx / 2) 1 := by
    rcases eq_or_lt_of_le hj with rfl | hj2
    · exact hstr
    · -- j ≥ 2: apply antitone repeatedly to reduce to 1-strange
      suffices ∀ m, 1 ≤ m → m ≤ level - 1 →
          isJStranger (2 ^ k) (perm i).val (level - 1) (idx / 2) m →
          isJStranger (2 ^ k) (perm i).val (level - 1) (idx / 2) 1 from
        this j hj hjp hstr
      intro m hm hmp hm_str
      induction m with
      | zero => omega
      | succ m' ihm =>
        rcases eq_or_lt_of_le hm with h1 | h2
        · rwa [show m' + 1 = 1 from by omega] at hm_str
        · exact ihm (by omega) (by omega)
            (isJStranger_antitone ⟨k, rfl⟩ (Nat.pow_le_pow_right (by omega) hkp)
              (by omega) (by omega) hm_str)
  -- 1-stranger → perm outside parent interval
  have h_outside := isJStranger_one_perm_bound h1str hbs
  -- stranger_fringe_bound: 1-stranger count ≤ lam * card → ≤ ⌊lam * card⌋₊ = fringeSize
  have hsfb := inv.stranger_fringe_bound (level - 1) (idx / 2)
  have h_str_le_f : jStrangerCount (2 ^ k) perm (bags (level - 1) (idx / 2))
      (level - 1) (idx / 2) 1 ≤ fringeSize lam (bags (level - 1) (idx / 2)).card := by
    rw [fringeSize, Nat.le_floor_iff (mul_nonneg hlam (Nat.cast_nonneg _))]
    exact_mod_cast hsfb
  -- Abbreviate for readability
  set regs := bags (level - 1) (idx / 2)
  set b := regs.card
  set f := fringeSize lam b
  set cs := childSendSize lam b
  -- If cs = 0, the middle range [f, f+2*0) = [f, f) is empty, so h_rank_lb/h_rank_ub
  -- give f ≤ rank < f, which is absurd.
  suffices hcs_pos : 0 < cs by
    -- Now cs > 0, so f < b/2, and we can do the fringe argument
    have hcs_def : cs = b / 2 - f := rfl
    have hf_le_half : f ≤ b / 2 := by omega
    rcases h_outside with hbelow | habove
    · -- perm(i) < lo → rank < count_below ≤ f
      have ha := rankInBag_lt_count_below h_mem hbelow
      have hb : (Finset.filter (fun j ↦ (perm j).val <
          idx / 2 * bagSize (2 ^ k) (level - 1)) regs).card ≤ f :=
        le_trans (Finset.card_le_card
          (filter_below_subset_stranger perm _ hplev1 hbs)) h_str_le_f
      omega  -- rank < f contradicts f ≤ rank
    · -- perm(i) ≥ hi → rank ≥ b - count_above ≥ b - f ≥ f + 2cs
      have ha := rankInBag_ge_count_below h_mem habove
      -- count_above ≤ f
      have hb : (Finset.filter (fun j ↦
          (idx / 2 + 1) * bagSize (2 ^ k) (level - 1) ≤ (perm j).val) regs).card ≤ f :=
        le_trans (Finset.card_le_card
          (filter_above_subset_stranger perm _ hplev1 hbs)) h_str_le_f
      -- Partition: count_lt + count_above = b
      have hc : (Finset.filter (fun j ↦ (perm j).val <
            (idx / 2 + 1) * bagSize (2 ^ k) (level - 1)) regs).card +
          (Finset.filter (fun j ↦
            (idx / 2 + 1) * bagSize (2 ^ k) (level - 1) ≤ (perm j).val) regs).card = b := by
        have h := @Finset.card_filter_add_card_filter_not _ regs
          (fun j ↦ (perm j).val < (idx / 2 + 1) * bagSize (2 ^ k) (level - 1)) _ _
        rwa [show (Finset.filter (fun j ↦ ¬(perm j).val <
          (idx / 2 + 1) * bagSize (2 ^ k) (level - 1)) regs) =
          Finset.filter (fun j ↦ (idx / 2 + 1) * bagSize (2 ^ k) (level - 1) ≤ (perm j).val)
          regs from by congr 1; ext x; simp [not_lt]] at h
      -- rank ≥ count_lt ≥ b - f ≥ f + 2cs, contradicts rank < f + 2cs
      have hd : 2 * (b / 2) ≤ b := by linarith [Nat.div_mul_le_self b 2]
      omega
  -- Prove cs > 0 (or show the middle range is empty → contradiction)
  by_contra hcs0; push_neg at hcs0
  have hcs_eq : cs = 0 := Nat.eq_zero_of_le_zero hcs0
  show False
  have : 2 * cs = 0 := by omega
  omega  -- h_rank_lb : f ≤ rank, h_rank_ub : rank < f + 0 = f

/-- Sibling-native bound for the concrete split: items from parent that are
    native to the sibling child are bounded by `cnativeCoeff · cap(parent)`.

    The dominant contribution is the halving error (ε/2 term): items native
    to the parent but assigned to the wrong child by the rank-based partition.
    The geometric-series and above-parent terms in `cnativeCoeff` are zero
    for this concrete split (validated empirically). -/
theorem concreteSplit_cnative_bound {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (level idx : ℕ) :
    (siblingNativeCount n perm
      (fromParent (concreteSplit lam perm bags) level idx)
      level idx : ℝ) ≤
    cnativeCoeff A lam ε * bagCapacity n A ν t (level - 1) := by
  sorry

/-! **Concrete Split: Assembled Stranger Bounds**

Wire the abstract framework to the concrete split. -/

/-- Concrete parent stranger bound for j ≥ 2. -/
theorem concreteSplit_parent_stranger_bound {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hn : ∃ k, n = 2 ^ k)
    (hlam : 0 ≤ lam) (hε : 0 ≤ ε)
    (level idx j : ℕ) (hj : 2 ≤ j) :
    (jStrangerCount n perm
      (fromParent (concreteSplit lam perm bags) level idx)
      level idx j : ℝ) ≤
    lam * ε ^ (j - 1) * bagCapacity n A ν t (level - 1) :=
  parent_stranger_bound _ inv hlam hε
    (fun l i j hj hl ↦ concreteSplit_fromParent_filtered inv hn hlam hε l i j hj hl)
    level idx j hj

/-- Concrete parent 1-stranger bound. -/
theorem concreteSplit_parent_1stranger {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hn : ∃ k, n = 2 ^ k)
    (hparams : SatisfiesConstraints A ν lam ε)
    (level idx : ℕ) :
    (jStrangerCount n perm
      (fromParent (concreteSplit lam perm bags) level idx)
      level idx 1 : ℝ) ≤
    parentStrangerCoeff A lam ε * bagCapacity n A ν t level :=
  parent_1stranger_from_inv _ inv hparams
    (fun l i j hj hl ↦ concreteSplit_fromParent_filtered inv hn
      (le_of_lt hparams.2.2.2.1) (le_of_lt hparams.2.2.2.2.2.1) l i j hj hl)
    (fun l i ↦ concreteSplit_cnative_bound inv l i)
    level idx
