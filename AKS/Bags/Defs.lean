/-
  # Bag Definitions for Separator-Based Sorting

  Defines the binary bag tree structure and j-stranger counting for the
  Seiferas (2009) separator-based sorting network proof (Sections 2–5).

  Key definitions:
  - `bagSize`, `nativeBagIdx`: bag structure in the binary tree
  - `isJStranger`: whether an item diverges from its native path
  - `jStrangerCount`: count of j-strangers among items in a bag

  All definitions validated by Rust simulation (`rust/test-bags.rs`):
  - Invariant holds with adversarial separator for n = 8..16384
  - j-stranger monotonicity confirmed: (j+1)-strange → j-strange
  - Parity convention: (t + level) % 2 ≠ 0 → empty
-/

import AKS.Sort.Defs

open Finset

/-! **Bag Tree Structure** -/

/-- Size of each bag's native interval at a given level: `n / 2^level`.
    At level 0 (root): `bagSize n 0 = n`. At level `k`: each bag covers
    `n / 2^k` items. -/
def bagSize (n level : ℕ) : ℕ := n / 2 ^ level

/-- The bag index that an item with sorted rank `r` is native to at a given
    level. `nativeBagIdx n level r = r / (n / 2^level)`. -/
def nativeBagIdx (n level : ℕ) (r : ℕ) : ℕ := r / bagSize n level

/-! **j-Strangers (Seiferas Section 3)** -/

/-- An item with sorted rank `r` is `j`-strange at bag `(level, idx)` if its
    native bag index disagrees with the bag's ancestry at level `level - (j - 1)`.

    This is Seiferas's convention (shifted indexing):
    - `j = 1`: not native to this bag (`nativeBagIdx n level rank != idx`)
    - `j = 2`: not native to parent (`nativeBagIdx n (level-1) rank != idx/2`)
    - `j = k`: diverges at level `level - (k-1)`

    Guards (validated by Rust simulation):
    - `j >= 1`: 0-strange is vacuously false
    - `j <= level`: can't diverge above root

    Key properties:
    - `(j+1)`-strange -> `j`-strange (divergence propagates: `a/2 != b/2 -> a != b`)
    - Native items (rank in bag's interval) are not `j`-strange for any `j`

    Note: earlier versions used an unshifted definition (`level - j`, `idx / 2^j`)
    which missed sibling leakage at `j = 1`. The shifted definition is essential
    for Seiferas's three-source decomposition of 1-strangers. -/
@[reducible] def isJStranger (n rank level idx j : ℕ) : Prop :=
  1 ≤ j ∧ j ≤ level ∧ nativeBagIdx n (level - (j - 1)) rank ≠ idx / 2 ^ (j - 1)

/-- Count of `j`-strangers among items in a bag.
    `perm` maps register positions to sorted ranks.
    `regs` is the set of register positions assigned to this bag. -/
def jStrangerCount (n : ℕ) (perm : Fin n → Fin n)
    (regs : Finset (Fin n)) (level idx j : ℕ) : ℕ :=
  (regs.filter (fun i ↦ isJStranger n (perm i).val level idx j)).card

/-- Items that are 1-strangers but not 2-strangers: native to parent's bag
    but native to sibling at child level. -/
def siblingNativeCount (n : ℕ) (perm : Fin n → Fin n)
    (regs : Finset (Fin n)) (level idx : ℕ) : ℕ :=
  (regs.filter (fun i ↦ isJStranger n (perm i).val level idx 1 ∧
    ¬isJStranger n (perm i).val level idx 2)).card

/-! **Basic Lemmas** -/

@[simp] theorem bagSize_zero (n : ℕ) : bagSize n 0 = n := by
  simp [bagSize]

theorem bagSize_pos {n level : ℕ} (hn : 2 ^ level ≤ n) : 0 < bagSize n level := by
  exact Nat.div_pos hn (pow_pos (by omega) level)

@[simp] theorem nativeBagIdx_root {n r : ℕ} (hr : r < n) :
    nativeBagIdx n 0 r = 0 := by
  simp only [nativeBagIdx, bagSize_zero]
  exact Nat.div_eq_of_lt hr

theorem not_isJStranger_zero (n rank level idx : ℕ) :
    ¬isJStranger n rank level idx 0 := by
  simp [isJStranger]

theorem not_isJStranger_gt_level {n rank level idx j : ℕ} (h : level < j) :
    ¬isJStranger n rank level idx j := by
  simp only [isJStranger, not_and, not_not]
  omega

/-- `bagSize (2^k) (ℓ+1) * 2 = bagSize (2^k) ℓ`: each level doubles the bag size. -/
theorem bagSize_succ_mul_two {k ℓ : ℕ} (h : ℓ + 1 ≤ k) :
    bagSize (2 ^ k) (ℓ + 1) * 2 = bagSize (2 ^ k) ℓ := by
  simp only [bagSize]
  rw [Nat.pow_div h (by positivity), Nat.pow_div (by omega) (by positivity), ← pow_succ]
  congr 1; omega

/-- `nativeBagIdx (2^k) (ℓ+1) r / 2 = nativeBagIdx (2^k) ℓ r`: going up a level divides
    the bag index by 2. -/
private theorem nativeBagIdx_div_two {k ℓ r : ℕ} (h : ℓ + 1 ≤ k) :
    nativeBagIdx (2 ^ k) (ℓ + 1) r / 2 = nativeBagIdx (2 ^ k) ℓ r := by
  simp only [nativeBagIdx]
  rw [Nat.div_div_eq_div_mul, bagSize_succ_mul_two h]

/-- `idx / 2^(j-1) / 2 = idx / 2^j` for `j ≥ 1`. -/
private theorem div_pow_pred_div_two {idx j : ℕ} (hj : 1 ≤ j) :
    idx / 2 ^ (j - 1) / 2 = idx / 2 ^ j := by
  rw [Nat.div_div_eq_div_mul, ← pow_succ, Nat.sub_add_cancel hj]

/-- `(j+1)`-strange → `j`-strange: divergence at ancestor level `level - j` implies
    divergence at descendant level `level - (j-1)`. Uses `a/2 ≠ b/2 → a ≠ b` and
    `nativeBagIdx n ℓ r = (nativeBagIdx n (ℓ+1) r) / 2` (for power-of-2 `n`). -/
theorem isJStranger_antitone {n rank level idx j : ℕ}
    (hn : ∃ k, n = 2 ^ k) (hlev : 2 ^ level ≤ n) (hj : 1 ≤ j) (hjl : j + 1 ≤ level)
    (h : isJStranger n rank level idx (j + 1)) :
    isJStranger n rank level idx j := by
  obtain ⟨k, rfl⟩ := hn
  have hkl : level ≤ k := by
    by_contra hc; push_neg at hc
    exact absurd hlev (not_le.mpr (Nat.pow_lt_pow_right (by omega) hc))
  obtain ⟨_, _, hne⟩ := h
  refine ⟨hj, by omega, fun heq => hne ?_⟩
  show nativeBagIdx (2 ^ k) (level - j) rank = idx / 2 ^ j
  have hlj : level - (j - 1) = (level - j) + 1 := by omega
  rw [hlj] at heq
  rw [← nativeBagIdx_div_two (show (level - j) + 1 ≤ k by omega), heq,
      div_pow_pred_div_two hj]

/-- At the root level, all items are native (since `j ≤ 0` forces `j = 0`). -/
theorem not_isJStranger_at_root (n rank idx j : ℕ) :
    ¬isJStranger n rank 0 idx j := by
  simp only [isJStranger, not_and, not_not]
  omega

/-- 1-strangers = 2-strangers + sibling-native (for power-of-2 `n`, level ≥ 2). -/
theorem jStrangerCount_one_eq_two_plus_sibling {n : ℕ} (perm : Fin n → Fin n)
    (regs : Finset (Fin n)) {level idx : ℕ}
    (hn : ∃ k, n = 2 ^ k) (hlev : 2 ≤ level) (hpow : 2 ^ level ≤ n) :
    jStrangerCount n perm regs level idx 1 =
    jStrangerCount n perm regs level idx 2 + siblingNativeCount n perm regs level idx := by
  simp only [jStrangerCount, siblingNativeCount]
  -- Partition filter(isJ 1) into filter(isJ 2) ∪ filter(isJ 1 ∧ ¬isJ 2)
  have hdisj : Disjoint
      (regs.filter (fun i ↦ isJStranger n (perm i).val level idx 2))
      (regs.filter (fun i ↦ isJStranger n (perm i).val level idx 1 ∧
        ¬isJStranger n (perm i).val level idx 2)) := by
    simp only [Finset.disjoint_filter]
    exact fun _ _ h2 ⟨_, h2'⟩ ↦ h2' h2
  have hunion :
      regs.filter (fun i ↦ isJStranger n (perm i).val level idx 1) =
      regs.filter (fun i ↦ isJStranger n (perm i).val level idx 2) ∪
      regs.filter (fun i ↦ isJStranger n (perm i).val level idx 1 ∧
        ¬isJStranger n (perm i).val level idx 2) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro ⟨hm, h1⟩
      by_cases h2 : isJStranger n (perm x).val level idx 2
      · exact Or.inl ⟨hm, h2⟩
      · exact Or.inr ⟨hm, h1, h2⟩
    · rintro (⟨hm, h2⟩ | ⟨hm, h1, _⟩)
      · exact ⟨hm, isJStranger_antitone hn hpow (by omega) (by omega) h2⟩
      · exact ⟨hm, h1⟩
  rw [hunion, Finset.card_union_of_disjoint hdisj]

theorem jStrangerCount_empty (n : ℕ) (perm : Fin n → Fin n)
    (level idx j : ℕ) : jStrangerCount n perm ∅ level idx j = 0 := by
  simp [jStrangerCount]

/-- Stranger count is monotone in the register set. -/
theorem jStrangerCount_mono {n : ℕ} {perm : Fin n → Fin n}
    {s t : Finset (Fin n)} (hst : s ⊆ t) (level idx j : ℕ) :
    jStrangerCount n perm s level idx j ≤ jStrangerCount n perm t level idx j := by
  simp only [jStrangerCount]
  exact Finset.card_le_card (Finset.filter_subset_filter _ hst)

/-- Stranger count of a union is at most the sum of stranger counts. -/
theorem jStrangerCount_union_le {n : ℕ} (perm : Fin n → Fin n)
    (s₁ s₂ : Finset (Fin n)) (level idx j : ℕ) :
    jStrangerCount n perm (s₁ ∪ s₂) level idx j ≤
    jStrangerCount n perm s₁ level idx j + jStrangerCount n perm s₂ level idx j := by
  simp only [jStrangerCount, Finset.filter_union]
  exact Finset.card_union_le _ _

/-- The number of `j`-strangers is at most the number of items in the bag. -/
theorem jStrangerCount_le_card {n : ℕ} (perm : Fin n → Fin n)
    (regs : Finset (Fin n)) (level idx j : ℕ) :
    jStrangerCount n perm regs level idx j ≤ regs.card := by
  simp only [jStrangerCount]
  exact Finset.card_filter_le _ _

/-- No items are `j`-strange for `j = 0`. -/
theorem jStrangerCount_zero_j {n : ℕ} (perm : Fin n → Fin n)
    (regs : Finset (Fin n)) (level idx : ℕ) :
    jStrangerCount n perm regs level idx 0 = 0 := by
  simp only [jStrangerCount, isJStranger, show ¬(1 ≤ 0) by omega, false_and, filter_false,
    card_empty]

/-- No items are `j`-strange for `j > level`. -/
theorem jStrangerCount_zero_gt_level {n : ℕ} (perm : Fin n → Fin n)
    (regs : Finset (Fin n)) {level idx j : ℕ} (h : level < j) :
    jStrangerCount n perm regs level idx j = 0 := by
  simp only [jStrangerCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun _ _ ↦ not_isJStranger_gt_level h

/-- No sibling-native items in an empty set. -/
theorem siblingNativeCount_empty {n : ℕ} (perm : Fin n → Fin n) (level idx : ℕ) :
    siblingNativeCount n perm ∅ level idx = 0 := by
  simp [siblingNativeCount]

/-- Sibling-native count is at most the set size. -/
theorem siblingNativeCount_le_card {n : ℕ} (perm : Fin n → Fin n)
    (regs : Finset (Fin n)) (level idx : ℕ) :
    siblingNativeCount n perm regs level idx ≤ regs.card := by
  simp only [siblingNativeCount]
  exact Finset.card_filter_le _ _

/-! **Stranger → Perm Value Bounds**

j-strangers have perm values outside their ancestor's native interval.
This is the structural basis for showing that strangers get extreme ranks
in the bag, and thus are captured by the fringe in the concrete split. -/

/-- j-strangers have perm values outside their ancestor's native interval.
    If `isJStranger n rank level idx j`, then `rank` falls outside the interval
    `[lo * bs, (lo + 1) * bs)` where `lo = idx / 2^(j-1)` is the ancestor
    index and `bs = bagSize n (level - (j-1))` is the ancestor bag size. -/
theorem isJStranger_perm_bound {n rank level idx j : ℕ}
    (hs : isJStranger n rank level idx j)
    (hbs : 0 < bagSize n (level - (j - 1))) :
    rank < (idx / 2 ^ (j - 1)) * bagSize n (level - (j - 1)) ∨
    ((idx / 2 ^ (j - 1)) + 1) * bagSize n (level - (j - 1)) ≤ rank := by
  obtain ⟨_, _, hne⟩ := hs
  simp only [nativeBagIdx] at hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · left; exact (Nat.div_lt_iff_lt_mul hbs).mp hlt
  · right; exact (Nat.le_div_iff_mul_le hbs).mp hgt

/-- 1-strangers have perm values outside their bag's native interval. -/
theorem isJStranger_one_perm_bound {n rank level idx : ℕ}
    (hs : isJStranger n rank level idx 1) (hbs : 0 < bagSize n level) :
    rank < idx * bagSize n level ∨ (idx + 1) * bagSize n level ≤ rank := by
  have h := isJStranger_perm_bound hs (by simpa using hbs)
  simpa using h

/-! **Sibling-Native Perm Value Characterization**

For `n = 2^k`, sibling-native items (1-stranger but not 2-stranger) have
perm values on the "wrong side" of the child boundary. This is the structural
basis for bounding sibling-native counts by the deviation |C - b/2|. -/

/-- For even idx with valid parent index: sibling-native items have perm ≥ boundary. -/
theorem siblingNative_even_perm_ge {k level idx rank : ℕ}
    (hlev : 1 ≤ level) (hk : level ≤ k) (heven : idx % 2 = 0)
    (hidx : idx / 2 < 2 ^ (level - 1))
    (h1 : isJStranger (2 ^ k) rank level idx 1)
    (h2 : ¬isJStranger (2 ^ k) rank level idx 2) :
    (idx / 2) * bagSize (2 ^ k) (level - 1) + bagSize (2 ^ k) level ≤ rank := by
  have hbs : 0 < bagSize (2 ^ k) level :=
    bagSize_pos (Nat.pow_le_pow_right (by omega) hk)
  have hbs_par : 0 < bagSize (2 ^ k) (level - 1) :=
    bagSize_pos (Nat.pow_le_pow_right (by omega) (by omega : level - 1 ≤ k))
  have hbag2 : bagSize (2 ^ k) level * 2 = bagSize (2 ^ k) (level - 1) := by
    have : (level - 1) + 1 = level := by omega
    rw [← this]; exact bagSize_succ_mul_two (by omega)
  -- Key fact: (idx/2)*2 = idx for even idx
  have heven_mul : idx / 2 * 2 = idx :=
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero heven)
  -- From 1-stranger: rank / bagSize(level) ≠ idx
  obtain ⟨_, _, hne1⟩ := h1
  simp only [Nat.sub_self, pow_zero, Nat.div_one, nativeBagIdx] at hne1
  -- Show: idx * bagSize(level) ≤ rank
  -- Then: rank / bagSize(level) ≥ idx, but ≠ idx, so ≥ idx+1
  -- Hence rank ≥ (idx+1) * bagSize(level) = boundary
  suffices hge : idx * bagSize (2 ^ k) level ≤ rank by
    have hdiv : rank / bagSize (2 ^ k) level ≠ idx := hne1
    have hdiv_ge : idx ≤ rank / bagSize (2 ^ k) level :=
      (Nat.le_div_iff_mul_le hbs).mpr hge
    have hdiv_gt : idx + 1 ≤ rank / bagSize (2 ^ k) level := by omega
    have hrank : (idx + 1) * bagSize (2 ^ k) level ≤ rank :=
      (Nat.le_div_iff_mul_le hbs).mp hdiv_gt
    calc (idx / 2) * bagSize (2 ^ k) (level - 1) + bagSize (2 ^ k) level
        = (idx / 2) * (bagSize (2 ^ k) level * 2) + bagSize (2 ^ k) level := by
          rw [hbag2]
      _ = idx * bagSize (2 ^ k) level + bagSize (2 ^ k) level := by
          rw [Nat.mul_comm (bagSize _ _) 2, ← Nat.mul_assoc, heven_mul]
      _ = (idx + 1) * bagSize (2 ^ k) level := by ring
      _ ≤ rank := hrank
  -- Prove: idx * bagSize(level) ≤ rank
  by_cases hlev2 : 2 ≤ level
  · -- Level ≥ 2: from not-2-stranger → nativeBagIdx(level-1) rank = idx/2
    have h2' : ¬isJStranger (2 ^ k) rank level idx 2 := h2
    simp only [isJStranger, not_and, not_not] at h2'
    have hnat : nativeBagIdx (2 ^ k) (level - 1) rank = idx / 2 := by
      have := h2' (by omega) hlev2
      simp only [nativeBagIdx] at this ⊢; exact this
    have : (idx / 2) * bagSize (2 ^ k) (level - 1) ≤ rank := by
      simp only [nativeBagIdx] at hnat
      rw [← hnat]; exact Nat.div_mul_le_self _ _
    calc idx * bagSize (2 ^ k) level
        = (idx / 2) * (bagSize (2 ^ k) level * 2) := by
          rw [Nat.mul_comm (bagSize _ _) 2, ← Nat.mul_assoc, heven_mul]
      _ = (idx / 2) * bagSize (2 ^ k) (level - 1) := by rw [hbag2]
      _ ≤ rank := this
  · -- Level = 1: idx = 0 (only even value with idx/2 < 2^0 = 1)
    have : level = 1 := by omega
    subst this
    have : idx / 2 = 0 := by omega
    have : idx = 0 := by omega
    subst this; simp

/-- For odd idx with valid parent index: sibling-native items have perm < boundary. -/
theorem siblingNative_odd_perm_lt {k level idx rank : ℕ}
    (hlev : 1 ≤ level) (hk : level ≤ k) (hodd : idx % 2 ≠ 0)
    (hidx : idx / 2 < 2 ^ (level - 1))
    (hrn : rank < 2 ^ k)
    (h1 : isJStranger (2 ^ k) rank level idx 1)
    (h2 : ¬isJStranger (2 ^ k) rank level idx 2) :
    rank < (idx / 2) * bagSize (2 ^ k) (level - 1) + bagSize (2 ^ k) level := by
  have hbs : 0 < bagSize (2 ^ k) level :=
    bagSize_pos (Nat.pow_le_pow_right (by omega) hk)
  have hbs_par : 0 < bagSize (2 ^ k) (level - 1) :=
    bagSize_pos (Nat.pow_le_pow_right (by omega) (by omega : level - 1 ≤ k))
  have hbag2 : bagSize (2 ^ k) level * 2 = bagSize (2 ^ k) (level - 1) := by
    have : (level - 1) + 1 = level := by omega
    rw [← this]; exact bagSize_succ_mul_two (by omega)
  -- Key fact: (idx/2)*2 + 1 = idx for odd idx
  have hodd_mul : idx / 2 * 2 + 1 = idx := by omega
  -- From 1-stranger: rank / bagSize(level) ≠ idx (keep h1 for later)
  have hne1 : rank / bagSize (2 ^ k) level ≠ idx := by
    have := h1.2.2; simp only [nativeBagIdx] at this; simpa using this
  -- Show: rank < (idx/2)*bagSize(level-1) + bagSize(level) = idx*bagSize(level)
  suffices hlt : rank < idx * bagSize (2 ^ k) level by
    have heq : idx * bagSize (2 ^ k) level =
        idx / 2 * bagSize (2 ^ k) (level - 1) + bagSize (2 ^ k) level := by
      rw [← hbag2]; nlinarith [hodd_mul]
    linarith
  -- Prove: rank < idx * bagSize(level)
  by_cases hlev2 : 2 ≤ level
  · -- Level ≥ 2: from not-2-stranger, rank ∈ [(idx/2)*bs_par, (idx/2+1)*bs_par)
    have h2' : ¬isJStranger (2 ^ k) rank level idx 2 := h2
    simp only [isJStranger, not_and, not_not] at h2'
    have hnat : nativeBagIdx (2 ^ k) (level - 1) rank = idx / 2 := by
      have := h2' (by omega) hlev2
      simp only [nativeBagIdx] at this ⊢; exact this
    -- rank / bagSize(level-1) = idx/2, so rank ∈ parent interval
    have hlo : (idx / 2) * bagSize (2 ^ k) (level - 1) ≤ rank := by
      simp only [nativeBagIdx] at hnat
      rw [← hnat]; exact Nat.div_mul_le_self _ _
    have hhi : rank < (idx / 2 + 1) * bagSize (2 ^ k) (level - 1) := by
      simp only [nativeBagIdx] at hnat
      rw [← hnat, Nat.add_mul, Nat.one_mul]; exact Nat.lt_div_mul_add hbs_par
    -- Convert to level bounds: rank < (idx+1)*bs
    have hhi' : rank < (idx + 1) * bagSize (2 ^ k) level := by
      calc rank < (idx / 2 + 1) * bagSize (2 ^ k) (level - 1) := hhi
        _ = (idx / 2 + 1) * (bagSize (2 ^ k) level * 2) := by rw [hbag2]
        _ = (idx / 2 * 2 + 2) * bagSize (2 ^ k) level := by ring
        _ = (idx + 1) * bagSize (2 ^ k) level := by rw [show idx / 2 * 2 + 2 = idx + 1 by omega]
    rcases isJStranger_one_perm_bound h1 hbs with hbelow | habove
    · exact hbelow
    · omega
  · -- Level = 1: idx ∈ {1} (only odd value with idx/2 < 2^0 = 1)
    have hlev1 : level = 1 := by omega
    subst hlev1
    have hidx0 : idx / 2 = 0 := by omega
    have hidx1 : idx = 1 := by omega
    subst hidx1
    -- Goal: rank < 1 * bagSize (2 ^ k) 1
    rcases isJStranger_one_perm_bound h1 hbs with hbelow | habove
    · exact hbelow  -- rank < idx * bagSize = rank < 1 * bagSize
    · -- rank ≥ 2*bagSize(1) = n, contradicts rank < n
      have : bagSize (2 ^ k) 1 * 2 = bagSize (2 ^ k) 0 := bagSize_succ_mul_two (by omega)
      simp only [bagSize_zero] at this
      omega
