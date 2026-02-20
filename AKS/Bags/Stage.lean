/-
  # One-Stage Separator Network

  Defines one stage of the bag-tree sorting network: apply a separator to all
  contiguous chunks at a given level (Seiferas 2009, Section 7).

  At stage `stageIdx`, there are `2^stageIdx` chunks of size `⌊n / 2^stageIdx⌋`.
  The separator is applied to each chunk via `shiftEmbed`. Since chunks are at
  non-overlapping wire ranges, all separator applications run in parallel.

  Key results:
  - `separatorStage`: computable network for one stage
  - `active_bags_disjoint`: active bags have disjoint registers
  - `separatorStage_depth_le`: depth per stage ≤ separator depth (parallel)
-/

import AKS.Bags.Invariant
import AKS.Separator.Family
import AKS.Sort.Depth

/-! **Active Bags** -/

/-- A bag is active at stage `t` if `(t + level) % 2 = 0` (from parity convention). -/
def bagActive (t level : ℕ) : Prop := (t + level) % 2 = 0

instance (t level : ℕ) : Decidable (bagActive t level) :=
  inferInstanceAs (Decidable ((t + level) % 2 = 0))

/-! **Disjointness** -/

/-- Active bags at different (level, idx) pairs have disjoint register sets.
    This follows from the alternating-empty invariant: at any given stage,
    active bags exist only at even or odd levels, and bags at the same level
    partition the register space. -/
theorem active_bags_disjoint {n : ℕ} {A ν lam ε : ℝ} {t : ℕ}
    {perm : Fin n → Fin n} {bags : BagAssignment n}
    (inv : SeifInvariant n A ν lam ε t perm bags)
    (l₁ l₂ i₁ i₂ : ℕ) (hne : (l₁, i₁) ≠ (l₂, i₂))
    (h₁ : bagActive t l₁) (h₂ : bagActive t l₂) :
    Disjoint (bags l₁ i₁) (bags l₂ i₂) :=
  inv.bags_disjoint l₁ l₂ i₁ i₂ hne

/-! **One-Stage Network Construction** -/

/-- Apply the separator to all contiguous chunks at level `stageIdx`.

    At stage `stageIdx`, the `n`-wire array is divided into `2^stageIdx` chunks
    of size `⌊n / 2^stageIdx⌋`. The separator `sep.net chunkSize` is embedded
    at offset `k * chunkSize` for each chunk `k`.

    Chunks at the same level have **disjoint wire ranges**, so all separator
    applications run in **parallel** (depth = `d_sep`). -/
def separatorStage (n : ℕ) {gam eps : ℝ} {d_sep : ℕ}
    (sep : SeparatorFamily gam eps d_sep) (stageIdx : ℕ) : ComparatorNetwork n where
  comparators :=
    let chunkSize := n / 2 ^ stageIdx
    let numChunks := 2 ^ stageIdx
    (List.range numChunks).flatMap fun k ↦
      let offset := k * chunkSize
      if h : offset + chunkSize ≤ n then
        ((sep.net chunkSize).shiftEmbed n offset h).comparators
      else []

/-- One stage has depth at most the separator depth, since all chunks
    have disjoint wire ranges and their separators run in parallel. -/
theorem separatorStage_depth_le (n : ℕ) {gam eps : ℝ} {d_sep : ℕ}
    (sep : SeparatorFamily gam eps d_sep) (stageIdx : ℕ) :
    (separatorStage n sep stageIdx).depth ≤ d_sep := by
  unfold separatorStage
  apply depth_flatMap_disjoint
  · -- Per-chunk depth ≤ d_sep
    intro k _; simp only
    split
    · rename_i h
      exact le_trans (depth_shiftEmbed_le _ _ _ h) (sep.depth_le _)
    · simp [ComparatorNetwork.depth]
  · -- Pairwise wire disjointness: chunks at offsets k₁·C, k₂·C have non-overlapping
    -- wire ranges [ki·C, ki·C + C) since k₁ < k₂ implies k₁·C + C ≤ k₂·C.
    exact List.pairwise_lt_range.imp fun {k₁ k₂} (hlt : k₁ < k₂) ↦ by
      simp only
      intro c₁ hc₁ c₂ hc₂
      by_cases h₁ : k₁ * (n / 2 ^ stageIdx) + (n / 2 ^ stageIdx) ≤ n
      · by_cases h₂ : k₂ * (n / 2 ^ stageIdx) + (n / 2 ^ stageIdx) ≤ n
        · -- Both conditions hold: extract the base comparators
          simp only [h₁, h₂, dite_true, ComparatorNetwork.shiftEmbed,
            List.mem_map] at hc₁ hc₂
          obtain ⟨c₁₀, _, rfl⟩ := hc₁; obtain ⟨c₂₀, _, rfl⟩ := hc₂
          have h1i := c₁₀.i.isLt; have h1j := c₁₀.j.isLt
          have h2i := c₂₀.i.isLt; have h2j := c₂₀.j.isLt
          -- Key: k₁ < k₂ implies k₁·C + C ≤ k₂·C
          have hk : k₁ * (n / 2 ^ stageIdx) + (n / 2 ^ stageIdx) ≤
              k₂ * (n / 2 ^ stageIdx) := by
            have := Nat.mul_le_mul_right (n / 2 ^ stageIdx) hlt
            rw [Nat.succ_mul] at this; exact this
          constructor <;> constructor <;> intro heq <;> {
            simp only [Fin.mk.injEq] at heq; omega }
        · simp only [h₂, dite_false] at hc₂
          exact absurd hc₂ (List.not_mem_nil)
      · simp only [h₁, dite_false] at hc₁
        exact absurd hc₁ (List.not_mem_nil)
