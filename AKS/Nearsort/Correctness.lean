/-
  # Halver Network Correctness

  Proves that the recursive halving network produces ε·depth-nearsorted output
  for every permutation input.
  (AKS Section 4, page 5: "it is easy to see")

  ## Structure

  The proof is decomposed into:
  1. **Reformulation** (`sdiff_image_card_eq_far_count`): Convert the nearsort
     condition |S \ Sδ.image w| to counting "far positions with small values":
     positions p ≥ k + ⌊δn⌋ where the output value w(p) has rank < k.
     This uses injectivity of the network output.

  2. **Core counting bound** (`halverNetwork_far_small_bound`): The halver network
     produces at most δ·k small values at far positions. This is the mathematical
     heart, requiring IsEpsilonHalver on sub-intervals at each level.

  3. **Assembly** (`halverNetwork_initialNearsorted`): Combines 1 and 2.

  ## Proof sketch for the core bound

  Track individual element trajectories through the recursive halving:

  • **Correctly classified.** Value `a` is "correctly classified at level `l`" if
    the halver at level `l` places it in the sub-interval half containing `a.val`
    at the level-`(l+1)` partition.

  • **All-correct → near target.** If correctly classified at every level
    `0, ..., depth-1`, then the final position is within `n/2^depth` of `a.val`.

  • **Blow-up covers displacement.** The hypothesis `1 ≤ ε · depth · 2^depth`
    ensures `n/2^depth ≤ ⌊(ε · depth) · n⌋`.

  • **Per-level misclassification bound.** At level `l`, the halver at the
    boundary sub-interval misclassifies at most `ε · k` values from `{val < k}`.
    This uses `IsEpsilonHalver` applied to the local permutation within the
    sub-interval, connected to global displacement via `exec_comp_monotone`.

  • **Union bound.** Total misclassified ≤ `Σ_l ε·k = depth · ε · k`.
-/

import AKS.Nearsort.Construction

open Finset BigOperators


/-! **Network composition** -/

/-- The halver network decomposes as previous levels followed by the new level. -/
theorem halverNetwork_exec_succ (n : ℕ)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    {α : Type*} [LinearOrder α] (depth : ℕ) (v : Fin n → α) :
    (halverNetwork n halvers (depth + 1)).exec v =
    (halverAtLevel n halvers depth).exec ((halverNetwork n halvers depth).exec v) := by
  unfold halverNetwork
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  exact ComparatorNetwork.exec_append ⟨_⟩ ⟨_⟩ v


/-! **Blow-up arithmetic** -/

/-- When `1 ≤ ε · depth · 2^depth`, the sub-interval resolution `n / 2^depth`
    is within the blow-up radius `⌊ε · depth · n⌋₊`. -/
private lemma blowup_covers_displacement {n : ℕ} {ε : ℝ} {depth : ℕ}
    (hdepth : (1 : ℝ) ≤ ε * ↑depth * 2 ^ depth) :
    n / 2 ^ depth ≤ ⌊ε * ↑depth * ↑n⌋₊ := by
  apply Nat.le_floor
  have h2pos : (0 : ℝ) < ↑(2 ^ depth : ℕ) := by positivity
  have hle : (↑(n / 2 ^ depth) : ℝ) ≤ ↑n / ↑(2 ^ depth : ℕ) := by
    rw [le_div_iff₀ h2pos]
    exact_mod_cast Nat.div_mul_le_self n (2 ^ depth)
  calc (↑(n / 2 ^ depth) : ℝ)
      ≤ ↑n / ↑(2 ^ depth : ℕ) := hle
    _ ≤ ε * ↑depth * ↑n := by
        rw [div_le_iff₀ h2pos]
        have h2eq : (↑(2 ^ depth : ℕ) : ℝ) = (2 : ℝ) ^ depth := by push_cast; ring
        rw [h2eq]
        nlinarith [Nat.cast_nonneg (α := ℝ) n]


/-! **Displacement reformulation** -/

/-- When w is injective on `Fin n`, |S \ Sε.image w| equals the number of
    positions `p ≥ k + R` that hold values `w(p) < k`.

    Intuition: `S \ Sε.image w` counts small values (< k) not reachable from
    nearby positions (< k + R). Since w is bijective on `Fin n`, each such value
    `a` has a unique preimage `p = w⁻¹(a)` with `p ≥ k + R` and `w(p) = a < k`.
    This bijection gives the cardinality equality. -/
private lemma sdiff_image_card_eq_far_count {n : ℕ}
    {w : Fin n → Fin n} (hw : Function.Injective w)
    {k R : ℕ} :
    (univ.filter (fun a : Fin n ↦ a.val < k) \
      (univ.filter (fun a : Fin n ↦ a.val < k + R)).image w).card =
    (univ.filter (fun p : Fin n ↦ k + R ≤ p.val ∧ (w p).val < k)).card := by
  have hw_surj : Function.Surjective w := Finite.surjective_of_injective hw
  set S := univ.filter (fun a : Fin n ↦ a.val < k)
  set Sε := univ.filter (fun a : Fin n ↦ a.val < k + R)
  set T := univ.filter (fun p : Fin n ↦ k + R ≤ p.val ∧ (w p).val < k)
  apply Finset.card_nbij' (fun a ↦ (hw_surj a).choose) (fun p ↦ w p)
  · -- MapsTo forward: a ∈ S \ Sε.image w → w⁻¹(a) ∈ T
    intro a ha
    rw [Finset.mem_coe, Finset.mem_sdiff] at ha
    have ha_small := (Finset.mem_filter.mp ha.1).2
    have hp_eq := (hw_surj a).choose_spec
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by
      constructor
      · by_contra h; push_neg at h
        exact ha.2 (Finset.mem_image.mpr
          ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩, hp_eq⟩)
      · rw [hp_eq]; exact ha_small⟩
  · -- MapsTo backward: p ∈ T → w(p) ∈ S \ Sε.image w
    intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    have ⟨_, hp_far, hp_small⟩ := hp
    rw [Finset.mem_coe, Finset.mem_sdiff]
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp_small⟩, fun h_img ↦ by
      obtain ⟨b, hb, hb_eq⟩ := Finset.mem_image.mp h_img
      have := hw hb_eq; subst this
      exact absurd (Finset.mem_filter.mp hb).2 (by omega)⟩
  · -- LeftInvOn: w(w⁻¹(a)) = a for a ∈ S \ Sε.image w
    intro a _; exact (hw_surj a).choose_spec
  · -- RightInvOn: w⁻¹(w(p)) = p for p ∈ T
    intro p _; exact hw (hw_surj (w p)).choose_spec


/-! **Core counting bound** -/

/-- The mathematical core: the halver network produces at most `ε · depth · k`
    small values (< k) at far positions (≥ k + ⌊δn⌋).

    **Proof approach** (AKS Section 4):
    Each of the `depth` levels of halving introduces at most `ε · k`
    cross-boundary errors via the `IsEpsilonHalver` property applied to the
    sub-interval straddling position `k`. Values correctly classified at all
    levels converge to within `n/2^depth ≤ ⌊δn⌋` of their target position.
    Union bound over depth levels gives total displaced ≤ `depth · ε · k`.

    The key technical challenge is connecting the local halver guarantee
    (on `Fin (2 * halfChunk)`) to the global displacement count (on `Fin n`).
    This requires:
    • `shiftEmbed` acts as the local halver on the sub-interval values
    • The local rank permutation satisfies `IsEpsilonHalver`
    • `exec_comp_monotone` bridges local and global rank orderings -/
private lemma halverNetwork_far_small_bound {n : ℕ} (ε : ℝ) (depth : ℕ)
    (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hdepth : (1 : ℝ) ≤ ε * ↑depth * 2 ^ depth)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (hhalvers : ∀ m, IsEpsilonHalver (halvers m) ε)
    (v : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n) :
    ((univ.filter (fun p : Fin n ↦
        k + ⌊ε * ↑depth * ↑n⌋₊ ≤ p.val ∧
        ((halverNetwork n halvers depth).exec (v : Fin n → Fin n) p).val < k)).card : ℝ)
    ≤ ε * ↑depth * ↑k := by
  sorry


/-! **Main theorems** -/

/-- The initial-segment nearsort bound: after `depth` levels of recursive halving,
    at most `ε · depth · k` elements of each initial segment `[0, k)` are displaced
    beyond the blow-up radius. -/
theorem halverNetwork_initialNearsorted {n : ℕ} (ε : ℝ) (depth d : ℕ)
    (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hdepth : (1 : ℝ) ≤ ε * ↑depth * 2 ^ depth)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (hhalvers : ∀ m, IsEpsilonHalver (halvers m) ε)
    (hhalver_size : ∀ m, (halvers m).size ≤ m * d)
    (v : Equiv.Perm (Fin n)) :
    InitialNearsorted ((halverNetwork n halvers depth).exec v) (ε * ↑depth) := by
  -- Unfold InitialNearsorted: for each k ≤ n, bound |S \ Sδ.image w| ≤ δ·k
  intro k hk
  simp only [Fintype.card_fin] at hk
  -- Simplify rank to val for Fin n
  simp only [rank_fin_val]
  set δ : ℝ := ε * ↑depth
  set w := (halverNetwork n halvers depth).exec (v : Fin n → Fin n)
  set R := ⌊δ * ↑n⌋₊
  -- The network output is injective (hence bijective on Fin n)
  have hw : Function.Injective w := ComparatorNetwork.exec_injective _ v.injective
  -- Step 1: Reformulate |S \ Sδ.image w| as |{far positions with small values}|
  -- Need to show: Fintype.card_fin normalization
  simp only [Fintype.card_fin]
  -- Apply the reformulation
  calc ((univ.filter (fun a : Fin n ↦ a.val < k) \
          (univ.filter (fun a : Fin n ↦ a.val < k + R)).image w).card : ℝ)
      = ((univ.filter (fun p : Fin n ↦ k + R ≤ p.val ∧ (w p).val < k)).card : ℝ) := by
        exact_mod_cast sdiff_image_card_eq_far_count hw
    _ ≤ δ * ↑k := halverNetwork_far_small_bound ε depth hε hε1 hdepth halvers hhalvers v k hk

/-- The dual: final-segment nearsortedness follows from `EpsilonFinalHalved`
    (which is part of `IsEpsilonHalver`). The same per-level argument applies
    with reversed order, using the order dual `(Fin n)ᵒᵈ`. -/
theorem halverNetwork_finalNearsorted {n : ℕ} (ε : ℝ) (depth d : ℕ)
    (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hdepth : (1 : ℝ) ≤ ε * ↑depth * 2 ^ depth)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (hhalvers : ∀ m, IsEpsilonHalver (halvers m) ε)
    (hhalver_size : ∀ m, (halvers m).size ≤ m * d)
    (v : Equiv.Perm (Fin n)) :
    FinalNearsorted ((halverNetwork n halvers depth).exec v) (ε * ↑depth) := by
  sorry
