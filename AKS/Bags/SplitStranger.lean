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

/-- Separator filtering for the concrete split: among items sent from parent
    to child, the stranger count at the parent level is at most `ε` times
    the full parent bag's stranger count.

    This captures the structural property that `concreteSplit` sends extreme-
    ranked items (which are the parent-level strangers) to the fringe
    (`toParent`), not to children (`toLeftChild`/`toRightChild`). -/
theorem concreteSplit_fromParent_filtered {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (level idx j : ℕ) (hj : 1 ≤ j) (hlev : 1 ≤ level) :
    (jStrangerCount n perm
      (fromParent (concreteSplit lam perm bags) level idx)
      (level - 1) (idx / 2) j : ℝ) ≤
    ε * ↑(jStrangerCount n perm (bags (level - 1) (idx / 2))
      (level - 1) (idx / 2) j) := by
  sorry

/-- The count of items in a bag with perm value below a threshold is
    approximately half the bag size. The deviation is bounded by
    `cnativeCoeff * cap(parent)`.

    This is the core deviation bound (Seiferas 2009, Section 5, p.5):
    benchmark distribution comparison shows the "below-boundary count"
    C = |{i ∈ B : perm(i) < boundary}| satisfies |C - ⌊b/2⌋| ≤ cnativeCoeff·cap.

    Validated by `rust/test-cnative-upper-bound.rs` (220K checks, 0 violations).
    See `docs/seiferas-plan.md` Instance I3 for the full proof decomposition. -/
theorem below_boundary_deviation {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hparams : SatisfiesConstraints A ν lam ε)
    (hperm : Function.Injective perm)
    (level idx : ℕ) (hlev : 1 ≤ level) :
    let B := bags (level - 1) (idx / 2)
    let boundary := (idx / 2) * bagSize n (level - 1) + bagSize n level
    let C := (B.filter (fun i ↦ (perm i).val < boundary)).card
    (Int.natAbs (↑C - ↑(B.card / 2)) : ℝ) ≤
    cnativeCoeff A lam ε * bagCapacity n A ν t (level - 1) := by
  sorry

/-- Sibling-native bound for the concrete split: items from parent that are
    native to the sibling child are bounded by `cnativeCoeff · cap(parent)`.

    Proof structure:
    - Level 0: `fromParent = ∅`, so siblingNativeCount = 0.
    - Level ≥ 1: Uses `below_boundary_deviation` (sorry'd) which bounds
      the deviation of the "below-boundary count" from half the bag size.

    The dominant contribution is the halving error (ε/2 term): items native
    to the parent but assigned to the wrong child by the rank-based partition.
    The geometric-series and above-parent terms in `cnativeCoeff` are zero
    for this concrete split (validated empirically). -/
theorem concreteSplit_cnative_bound {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hparams : SatisfiesConstraints A ν lam ε)
    (level idx : ℕ) :
    (siblingNativeCount n perm
      (fromParent (concreteSplit lam perm bags) level idx)
      level idx : ℝ) ≤
    cnativeCoeff A lam ε * bagCapacity n A ν t (level - 1) := by
  obtain ⟨hA, hν, hν1, hlam, _, hε, _, hC4, _⟩ := hparams
  have hA_pos : (0 : ℝ) < A := by linarith
  -- Derive (2εA)² < 1 from C4_gt1 + ν < 1
  have h2εA : (2 * ε * A) ^ 2 < 1 := by
    have hεA : 2 * ε * A < 1 := by
      unfold SatisfiesC4_gt1 at hC4
      have : 1 / A > 0 := div_pos one_pos hA_pos
      linarith
    have : 0 ≤ 2 * ε * A := by positivity
    calc (2 * ε * A) ^ 2 = (2 * ε * A) * (2 * ε * A) := sq _
      _ < 1 * 1 := mul_lt_mul hεA (le_of_lt hεA) (by positivity) (by linarith)
      _ = 1 := one_mul 1
  have hcnc : 0 ≤ cnativeCoeff A lam ε :=
    cnativeCoeff_nonneg hA hlam.le hε.le h2εA
  -- Level 0: fromParent = ∅, so siblingNativeCount = 0
  by_cases hlev : level = 0
  · subst hlev; simp only [fromParent, ite_true]
    rw [siblingNativeCount_empty]; simp only [Nat.cast_zero]
    exact mul_nonneg hcnc (by unfold bagCapacity; positivity)
  -- Level ≥ 1: the core deviation bound (sorry'd via below_boundary_deviation)
  · sorry

/-! **Concrete Split: Assembled Stranger Bounds**

Wire the abstract framework to the concrete split. -/

/-- Concrete parent stranger bound for j ≥ 2. -/
theorem concreteSplit_parent_stranger_bound {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hlam : 0 ≤ lam) (hε : 0 ≤ ε)
    (level idx j : ℕ) (hj : 2 ≤ j) :
    (jStrangerCount n perm
      (fromParent (concreteSplit lam perm bags) level idx)
      level idx j : ℝ) ≤
    lam * ε ^ (j - 1) * bagCapacity n A ν t (level - 1) :=
  parent_stranger_bound _ inv hlam hε
    (fun l i ↦ concreteSplit_fromParent_filtered inv l i) level idx j hj

/-- Concrete parent 1-stranger bound. -/
theorem concreteSplit_parent_1stranger {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (hparams : SatisfiesConstraints A ν lam ε)
    (level idx : ℕ) :
    (jStrangerCount n perm
      (fromParent (concreteSplit lam perm bags) level idx)
      level idx 1 : ℝ) ≤
    parentStrangerCoeff A lam ε * bagCapacity n A ν t level :=
  parent_1stranger_from_inv _ inv hparams
    (fun l i j hj hl ↦ concreteSplit_fromParent_filtered inv l i j hj hl)
    (fun l i ↦ concreteSplit_cnative_bound inv hparams l i)
    level idx
