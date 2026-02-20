/-
  # Concrete Split Definition

  Defines the position-based split of bag items for the Seiferas (2009)
  separator-based sorting network (Section 7).

  Items in each bag are ranked by their sorted position (`perm` value).
  The fringe (lowest and highest ranked items) is kicked to the parent bag;
  the middle items are sent to the left and right child bags.

  At leaf levels (≥ maxLevel), no items are sent to children.
-/

import AKS.Bags.Invariant

open Finset

/-! **Rank Within Bag** -/

/-- Rank of register `i` among items in `regs`, ordered by `perm` value.
    Counts how many items in `regs` have strictly smaller `perm` value. -/
def rankInBag {n : ℕ} (perm : Fin n → Fin n) (regs : Finset (Fin n))
    (i : Fin n) : ℕ :=
  (regs.filter (fun j ↦ (perm j).val < (perm i).val)).card

/-- Rank of any item in the bag is strictly less than the bag size. -/
theorem rankInBag_lt_card {n : ℕ} {perm : Fin n → Fin n}
    {regs : Finset (Fin n)} {i : Fin n} (hi : i ∈ regs) :
    rankInBag perm regs i < regs.card := by
  simp only [rankInBag]
  calc (regs.filter (fun j ↦ (perm j).val < (perm i).val)).card
      ≤ (regs.erase i).card := by
        apply card_le_card
        intro k hk
        simp only [mem_filter] at hk
        exact mem_erase.mpr ⟨by intro heq; subst heq; exact lt_irrefl _ hk.2, hk.1⟩
    _ < regs.card := by
        rw [card_erase_of_mem hi]
        exact Nat.sub_lt (card_pos.mpr ⟨i, hi⟩) Nat.one_pos

/-- Rank is strictly monotone in `perm` value for items in the bag. -/
theorem rankInBag_strictMono {n : ℕ} {perm : Fin n → Fin n}
    {regs : Finset (Fin n)} {i j : Fin n} (hi : i ∈ regs)
    (hlt : (perm i).val < (perm j).val) :
    rankInBag perm regs i < rankInBag perm regs j := by
  simp only [rankInBag]
  apply card_lt_card
  refine ⟨fun k hk ↦ ?_, fun hsub ↦ ?_⟩
  · simp only [mem_filter] at hk ⊢
    exact ⟨hk.1, hk.2.trans hlt⟩
  · have hmem : i ∈ regs.filter (fun k ↦ (perm k).val < (perm j).val) :=
      mem_filter.mpr ⟨hi, hlt⟩
    have hmem' := hsub hmem
    simp only [mem_filter] at hmem'
    exact absurd hmem'.2 (lt_irrefl _)

/-- Rank is injective on `regs` when `perm` is injective. -/
theorem rankInBag_injOn {n : ℕ} {perm : Fin n → Fin n}
    {regs : Finset (Fin n)} (hperm : Function.Injective perm) :
    Set.InjOn (rankInBag perm regs) ↑regs := by
  intro i hi j hj heq
  by_contra hne
  have hpne : (perm i).val ≠ (perm j).val := by
    intro h; exact hne (hperm (Fin.ext h))
  rcases Nat.lt_or_gt_of_ne hpne with hlt | hgt
  · exact absurd heq (Nat.ne_of_lt (rankInBag_strictMono hi hlt))
  · exact absurd heq (Nat.ne_of_gt (rankInBag_strictMono hj hgt))

/-! **Rank Ordering by Perm Value**

Items with perm values below a threshold have lower ranks than items
at or above the threshold. This is the structural basis for showing
that parent-level strangers (with extreme perm values) occupy extreme
ranks and are thus captured by the fringe. -/

/-- Items with perm value below threshold have rank strictly less than the
    count of below-threshold items. Follows from: the items counted by
    `rankInBag i` form a strict subset of the below-threshold items
    (since `i` itself is below but not counted). -/
theorem rankInBag_lt_count_below {n : ℕ} {perm : Fin n → Fin n}
    {regs : Finset (Fin n)} {i : Fin n} {a : ℕ}
    (hi : i ∈ regs) (hlt : (perm i).val < a) :
    rankInBag perm regs i <
      (regs.filter (fun j ↦ (perm j).val < a)).card := by
  simp only [rankInBag]
  apply card_lt_card
  refine ⟨fun k hk ↦ ?_, fun hsub ↦ ?_⟩
  · simp only [mem_filter] at hk ⊢
    exact ⟨hk.1, hk.2.trans hlt⟩
  · have hmem : i ∈ regs.filter (fun j ↦ (perm j).val < a) :=
      mem_filter.mpr ⟨hi, hlt⟩
    exact absurd (mem_filter.mp (hsub hmem)).2 (lt_irrefl _)

/-- Items with perm value at or above threshold have rank at least the
    count of below-threshold items. Follows from: all below-threshold
    items have perm value strictly less than `perm i`, so they are all
    counted by `rankInBag i`. -/
theorem rankInBag_ge_count_below {n : ℕ} {perm : Fin n → Fin n}
    {regs : Finset (Fin n)} {i : Fin n} {a : ℕ}
    (_ : i ∈ regs) (hge : a ≤ (perm i).val) :
    (regs.filter (fun j ↦ (perm j).val < a)).card ≤
      rankInBag perm regs i := by
  simp only [rankInBag]
  apply card_le_card
  intro k hk
  simp only [mem_filter] at hk ⊢
  exact ⟨hk.1, hk.2.trans_le hge⟩


/-! **Split Parameters** -/

/-- Fringe size: number of items kicked to parent from each end. -/
noncomputable def fringeSize (lam : ℝ) (b : ℕ) : ℕ := ⌊lam * ↑b⌋₊

/-- Number of items sent to each child bag. -/
noncomputable def childSendSize (lam : ℝ) (b : ℕ) : ℕ := b / 2 - fringeSize lam b

/-! **Concrete Split** -/

/-- Concrete position-based split of a bag's items (Seiferas 2009).
    Items are ranked within the bag by `perm` value:
    - Fringe (rank < f or rank ≥ f + 2h) → parent
    - Middle-left (rank ∈ [f, f+h)) → left child (non-leaf only)
    - Middle-right (rank ∈ [f+h, f+2h)) → right child (non-leaf only)
    where f = ⌊λ·b⌋ and h = ⌊b/2⌋ - f.
    At leaf levels (≥ maxLevel), children components are ∅. -/
noncomputable def concreteSplit {n : ℕ} (lam : ℝ) (perm : Fin n → Fin n)
    (bags : BagAssignment n) (level idx : ℕ) : SplitResult n :=
  let regs := bags level idx
  let b := regs.card
  let f := fringeSize lam b
  let h := childSendSize lam b
  { toParent := regs.filter (fun i ↦
      rankInBag perm regs i < f ∨ f + 2 * h ≤ rankInBag perm regs i)
    toLeftChild := if maxLevel n ≤ level then ∅
      else regs.filter (fun i ↦
        f ≤ rankInBag perm regs i ∧ rankInBag perm regs i < f + h)
    toRightChild := if maxLevel n ≤ level then ∅
      else regs.filter (fun i ↦
        f + h ≤ rankInBag perm regs i ∧ rankInBag perm regs i < f + 2 * h) }

/-! **Basic Properties** -/

theorem concreteSplit_hsplit_sub {n : ℕ} (lam : ℝ) (perm : Fin n → Fin n)
    (bags : BagAssignment n) :
    ∀ l i,
      (concreteSplit lam perm bags l i).toParent ⊆ bags l i ∧
      (concreteSplit lam perm bags l i).toLeftChild ⊆ bags l i ∧
      (concreteSplit lam perm bags l i).toRightChild ⊆ bags l i := by
  intro l i
  simp only [concreteSplit]
  refine ⟨filter_subset _ _, ?_, ?_⟩ <;>
    split_ifs <;> [exact empty_subset _; exact filter_subset _ _;
                    exact empty_subset _; exact filter_subset _ _]

theorem concreteSplit_hsplit_leaf {n : ℕ} (lam : ℝ) (perm : Fin n → Fin n)
    (bags : BagAssignment n) :
    ∀ l i, maxLevel n ≤ l →
      (concreteSplit lam perm bags l i).toLeftChild = ∅ ∧
      (concreteSplit lam perm bags l i).toRightChild = ∅ := by
  intro l i hl
  constructor <;> {
    show (if maxLevel n ≤ l then ∅ else _) = ∅
    exact if_pos hl }
