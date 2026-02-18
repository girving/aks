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

  2. **Depth bound** (`farSmallCount_depth_bound`, sorry): After `depth` levels
     of recursive halving, `farSmallCount ≤ ε · depth · k` at radius `n/2^depth`.
     Uses the AKS displaced-elements argument with union bound over levels.

  3. **Core bound** (`halverNetwork_far_small_bound`, proved): Converts from radius
     `n/2^depth` to the blow-up radius `⌊ε·depth·n⌋₊` via `blowup_covers_displacement`.

  4. **Assembly** (`halverNetwork_initialNearsorted`, proved): Combines reformulation
     and core bound.

  ## Remaining sorry

  `farSmallCount_depth_bound`: the AKS Section 4 displaced-elements argument.
  At each level l, define the error set E_l = elements misclassified by the halver
  (going to the wrong sub-half of their chunk). The ε-halver guarantees |E_l| ≤ ε·k.
  By union bound: |⋃ E_l| ≤ depth·ε·k. Elements never misclassified converge to
  their target; misclassified elements contribute to farSmallCount. The proof
  requires tracking element trajectories through halver levels.

  An earlier attempt used a per-level step on farSmallCount for arbitrary injective
  inputs — this was FALSE (counterexample: n=12, k=5, ε=0.3 with all small values
  concentrated in one chunk). The correct argument requires the displaced-elements
  approach which uses reachability of the input state.

  `halverNetwork_finalNearsorted`: the dual (end-segment) nearsort bound.
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


/-! **Core counting bound — decomposition** -/

/-- Count of "far positions with small values": positions p ≥ k + R
    whose image under w has Fin.val < k. -/
private def farSmallCount {n : ℕ} (w : Fin n → Fin n) (k R : ℕ) : ℕ :=
  (univ.filter (fun p : Fin n ↦ k + R ≤ p.val ∧ (w p).val < k)).card

/-- Larger blow-up radius means fewer far-small positions (monotone in R). -/
private lemma farSmallCount_anti {n : ℕ} (w : Fin n → Fin n) (k : ℕ)
    {R₁ R₂ : ℕ} (hR : R₁ ≤ R₂) :
    farSmallCount w k R₂ ≤ farSmallCount w k R₁ := by
  apply Finset.card_le_card
  intro p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun ⟨h1, h2⟩ ↦ ⟨by omega, h2⟩

/-- Base case: with radius n, no position in Fin n qualifies as "far". -/
private lemma farSmallCount_base {n : ℕ} (w : Fin n → Fin n) (k : ℕ) :
    farSmallCount w k n = 0 := by
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro p _
  simp only [not_and]
  intro h; have := p.isLt; omega

/-- After `depth` levels, the far-small count at radius `n / 2^depth` is
    at most `ε · depth · k`.

    **Proof approach** (AKS Section 4 displaced-elements argument):

    At each level `l`, the halver partitions into chunks of size `n / 2^l`
    and halves each chunk. Define the "error set" at level `l`:
      E_l = {i | i.val < k ∧ element i goes to bottom half of its chunk
                 ∧ i has local rank < min(k_C, halfChunk)}
    where `k_C` = number of values < k in the chunk.

    Step 1: |E_l| ≤ ε · k for each level l.
      Within each chunk c, `EpsilonInitialHalved` with j = min(k_C, halfChunk)
      gives |E_l ∩ chunk c| ≤ ε · min(k_C, halfChunk) ≤ ε · k_C.
      Summing: Σ_c ε · k_C(c) = ε · k.

    Step 2: Elements never in any E_l end up within n/2^depth of their target.
      At each level, "correctly classified" elements have their uncertainty
      interval halved. After depth levels: interval size ≤ n/2^depth.

    Step 3: By the union bound, |⋃ E_l| ≤ Σ |E_l| ≤ depth · ε · k.
      Elements in ⋃ E_l might end up far; elements outside end up close.
      So farSmallCount ≤ |⋃ E_l| ≤ depth · ε · k.

    NOTE: An earlier attempt used a per-level step
    `farSmallCount(halverAtLevel.exec w, k, R') ≤ farSmallCount(w, k, R) + ε·k`
    for arbitrary injective w. This is FALSE: when k_local > halfChunk in some
    chunk, the ε-halver cannot prevent excess false values in the bottom half.
    Counterexample: n=12, l=1, k=5, ε=0.3, all 5 small values in one chunk.
    The correct argument requires w to be a reachable state (output of previous
    halver levels), captured by the trajectory/displaced-elements approach. -/
private lemma farSmallCount_depth_bound {n : ℕ} (ε : ℝ) (depth : ℕ)
    (hε : 0 < ε)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (hhalvers : ∀ m, IsEpsilonHalver (halvers m) ε)
    (v : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n) :
    (farSmallCount ((halverNetwork n halvers depth).exec (v : Fin n → Fin n))
      k (n / 2 ^ depth) : ℝ)
    ≤ ε * ↑depth * ↑k := by
  sorry

/-- The halver network produces at most `ε · depth · k` small values (< k)
    at far positions (≥ k + ⌊δn⌋).

    Proved by combining:
    1. `farSmallCount_depth_bound`: bound at radius `n / 2^depth`
    2. `farSmallCount_anti`: monotonicity in radius
    3. `blowup_covers_displacement`: `n / 2^depth ≤ ⌊ε · depth · n⌋₊` -/
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
  -- The univ.filter expression equals farSmallCount
  change (farSmallCount ((halverNetwork n halvers depth).exec (v : Fin n → Fin n))
    k ⌊ε * ↑depth * ↑n⌋₊ : ℝ) ≤ ε * ↑depth * ↑k
  calc (farSmallCount ((halverNetwork n halvers depth).exec (v : Fin n → Fin n))
        k ⌊ε * ↑depth * ↑n⌋₊ : ℝ)
      ≤ farSmallCount ((halverNetwork n halvers depth).exec (v : Fin n → Fin n))
          k (n / 2 ^ depth) := by
        exact_mod_cast farSmallCount_anti _ k (blowup_covers_displacement hdepth)
    _ ≤ ε * ↑depth * ↑k :=
        farSmallCount_depth_bound ε depth hε halvers hhalvers v k hk


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

/-! **Dual counting bound (end segments)** -/

/-- Count of "far positions with large values": positions p with
    p.val + k + R < n and (w p).val + k ≥ n.
    This is the dual of `farSmallCount` for end segments. -/
private def farLargeCount {n : ℕ} (w : Fin n → Fin n) (k R : ℕ) : ℕ :=
  (univ.filter (fun p : Fin n ↦ p.val + k + R < n ∧ n ≤ (w p).val + k)).card

/-- Larger blow-up radius means fewer far-large positions (monotone in R). -/
private lemma farLargeCount_anti {n : ℕ} (w : Fin n → Fin n) (k : ℕ)
    {R₁ R₂ : ℕ} (hR : R₁ ≤ R₂) :
    farLargeCount w k R₂ ≤ farLargeCount w k R₁ := by
  apply Finset.card_le_card
  intro p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun ⟨h1, h2⟩ ↦ ⟨by omega, h2⟩

/-- When w is injective, |S_end \ Sε_end.image w| equals `farLargeCount`.
    This is the dual reformulation of `sdiff_image_card_eq_far_count` for
    end segments: large values (≥ n-k) not reachable from nearby positions. -/
private lemma sdiff_image_card_eq_far_large_count {n : ℕ}
    {w : Fin n → Fin n} (hw : Function.Injective w)
    {k R : ℕ} :
    (univ.filter (fun a : Fin n ↦ n ≤ a.val + k) \
      (univ.filter (fun a : Fin n ↦ n ≤ a.val + k + R)).image w).card =
    farLargeCount w k R := by
  have hw_surj : Function.Surjective w := Finite.surjective_of_injective hw
  set S := univ.filter (fun a : Fin n ↦ n ≤ a.val + k)
  set Sε := univ.filter (fun a : Fin n ↦ n ≤ a.val + k + R)
  set T := univ.filter (fun p : Fin n ↦ p.val + k + R < n ∧ n ≤ (w p).val + k)
  show (S \ Sε.image w).card = T.card
  apply Finset.card_nbij' (fun a ↦ (hw_surj a).choose) (fun p ↦ w p)
  · -- MapsTo forward: a ∈ S \ Sε.image w → w⁻¹(a) ∈ T
    intro a ha
    rw [Finset.mem_coe, Finset.mem_sdiff] at ha
    have ha_large := (Finset.mem_filter.mp ha.1).2
    have hp_eq := (hw_surj a).choose_spec
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by
      constructor
      · by_contra h; push_neg at h
        exact ha.2 (Finset.mem_image.mpr
          ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩, hp_eq⟩)
      · rw [hp_eq]; exact ha_large⟩
  · -- MapsTo backward: p ∈ T → w(p) ∈ S \ Sε.image w
    intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    have ⟨_, hp_far, hp_large⟩ := hp
    rw [Finset.mem_coe, Finset.mem_sdiff]
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp_large⟩, fun h_img ↦ by
      obtain ⟨b, hb, hb_eq⟩ := Finset.mem_image.mp h_img
      have := hw hb_eq; subst this
      exact absurd (Finset.mem_filter.mp hb).2 (by omega)⟩
  · -- LeftInvOn
    intro a _; exact (hw_surj a).choose_spec
  · -- RightInvOn
    intro p _; exact hw (hw_surj (w p)).choose_spec

/-- After `depth` levels, the far-large count at radius `n / 2^depth` is
    at most `ε · depth · k`. Dual of `farSmallCount_depth_bound`. -/
private lemma farLargeCount_depth_bound {n : ℕ} (ε : ℝ) (depth : ℕ)
    (hε : 0 < ε)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (hhalvers : ∀ m, IsEpsilonHalver (halvers m) ε)
    (v : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n) :
    (farLargeCount ((halverNetwork n halvers depth).exec (v : Fin n → Fin n))
      k (n / 2 ^ depth) : ℝ)
    ≤ ε * ↑depth * ↑k := by
  sorry

/-- Dual of `halverNetwork_far_small_bound` for end segments. -/
private lemma halverNetwork_far_large_bound {n : ℕ} (ε : ℝ) (depth : ℕ)
    (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hdepth : (1 : ℝ) ≤ ε * ↑depth * 2 ^ depth)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (hhalvers : ∀ m, IsEpsilonHalver (halvers m) ε)
    (v : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n) :
    ((univ.filter (fun p : Fin n ↦
        p.val + k + ⌊ε * ↑depth * ↑n⌋₊ < n ∧
        n ≤ ((halverNetwork n halvers depth).exec (v : Fin n → Fin n) p).val + k)).card : ℝ)
    ≤ ε * ↑depth * ↑k := by
  change (farLargeCount ((halverNetwork n halvers depth).exec (v : Fin n → Fin n))
    k ⌊ε * ↑depth * ↑n⌋₊ : ℝ) ≤ ε * ↑depth * ↑k
  calc (farLargeCount ((halverNetwork n halvers depth).exec (v : Fin n → Fin n))
        k ⌊ε * ↑depth * ↑n⌋₊ : ℝ)
      ≤ farLargeCount ((halverNetwork n halvers depth).exec (v : Fin n → Fin n))
          k (n / 2 ^ depth) := by
        exact_mod_cast farLargeCount_anti _ k (blowup_covers_displacement hdepth)
    _ ≤ ε * ↑depth * ↑k :=
        farLargeCount_depth_bound ε depth hε halvers hhalvers v k hk

/-- The dual: final-segment nearsortedness follows from `EpsilonFinalHalved`
    (which is part of `IsEpsilonHalver`). Uses `farLargeCount_depth_bound`
    (the dual of `farSmallCount_depth_bound`). -/
theorem halverNetwork_finalNearsorted {n : ℕ} (ε : ℝ) (depth d : ℕ)
    (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hdepth : (1 : ℝ) ≤ ε * ↑depth * 2 ^ depth)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (hhalvers : ∀ m, IsEpsilonHalver (halvers m) ε)
    (hhalver_size : ∀ m, (halvers m).size ≤ m * d)
    (v : Equiv.Perm (Fin n)) :
    FinalNearsorted ((halverNetwork n halvers depth).exec v) (ε * ↑depth) := by
  -- FinalNearsorted = InitialNearsorted on (Fin n)ᵒᵈ
  unfold FinalNearsorted
  intro k hk
  simp only [Fintype.card_fin] at hk ⊢
  -- rank on (Fin n)ᵒᵈ = n - 1 - val
  simp only [rank_fin_od_val]
  set δ : ℝ := ε * ↑depth
  set w := (halverNetwork n halvers depth).exec (v : Fin n → Fin n)
  set R := ⌊δ * ↑n⌋₊
  have hw : Function.Injective w := ComparatorNetwork.exec_injective _ v.injective
  -- Convert rank condition: n - 1 - a.val < k ↔ n ≤ a.val + k (for a : Fin n, val ≤ n-1)
  -- S = {a | n - 1 - a.val < k} = {a | n ≤ a.val + k}
  -- (Note: n - 1 - a.val < k ↔ n - 1 < k + a.val ↔ n ≤ k + a.val for Nat)
  have hS : (univ.filter (fun a : Fin n ↦ n - 1 - a.val < k)) =
    (univ.filter (fun a : Fin n ↦ n ≤ a.val + k)) := by
    ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h <;> have := a.isLt <;> omega
  have hSε : (univ.filter (fun a : Fin n ↦ n - 1 - a.val < k + R)) =
    (univ.filter (fun a : Fin n ↦ n ≤ a.val + k + R)) := by
    ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h <;> have := a.isLt <;> omega
  rw [hS, hSε]
  -- Now apply the dual reformulation and bound
  calc ((univ.filter (fun a : Fin n ↦ n ≤ a.val + k) \
          (univ.filter (fun a : Fin n ↦ n ≤ a.val + k + R)).image w).card : ℝ)
      = (farLargeCount w k R : ℝ) := by
        exact_mod_cast sdiff_image_card_eq_far_large_count hw
    _ ≤ δ * ↑k :=
        halverNetwork_far_large_bound ε depth hε hε1 hdepth halvers hhalvers v k hk
