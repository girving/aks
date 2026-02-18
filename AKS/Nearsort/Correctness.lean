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

/-  **Proof approach for `farSmallCount_depth_bound`**
    (AKS Section 4 displaced-elements argument):

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


/-! **Trajectory sub-lemmas (AKS Section 4 displaced-elements argument)** -/

section Trajectory

open Classical

/-- A value `a` has "good radius" at level `l` if it's in the same chunk of
    size `n / 2^l` as its target position `a.val`. Formally: the position of
    value `a` in the state after `l` levels is in the same chunk as `a.val`.

    Concretely: `pos(a, l) / (n / 2^l) = a.val / (n / 2^l)` where `pos(a, l)`
    is the position of value `a` after level `l`.

    At level 0, good radius always holds (single chunk = whole array).
    At each subsequent level, good radius can fail if the halver sends `a`
    to the wrong sub-half of its chunk. -/
private def hasGoodRadius {n : ℕ} (w : Fin n → Fin n) (hw : Function.Injective w)
    (a : Fin n) (l : ℕ) : Prop :=
  let chunkSize := n / 2 ^ l
  let pos := (Finite.surjective_of_injective hw a).choose
  pos.val / chunkSize = a.val / chunkSize

/-- The "error set" at level `l`: values `a < k` that have good radius at
    level `l` but lose it after the halver at level `l` acts.
    These are the values that get misclassified at level `l`. -/
private noncomputable def errorSetAtLevel {n : ℕ}
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (v : Equiv.Perm (Fin n)) (k l : ℕ) : Finset (Fin n) :=
  let w_l := (halverNetwork n halvers l).exec (v : Fin n → Fin n)
  let w_l1 := (halverNetwork n halvers (l + 1)).exec (v : Fin n → Fin n)
  let hw_l := ComparatorNetwork.exec_injective _ v.injective
  let hw_l1 := ComparatorNetwork.exec_injective _ v.injective
  univ.filter (fun a : Fin n ↦
    a.val < k ∧
    hasGoodRadius w_l hw_l a l ∧
    ¬hasGoodRadius w_l1 hw_l1 a (l + 1))

/-- **Convergence lemma** (Step 2): If a value `a` with `a.val < k` has good
    radius at level `depth`, and the chunk size `R = n / 2^depth` is positive,
    then its position is < k + R, so it doesn't contribute to `farSmallCount`.

    The proof: if `pos / R = a.val / R` and R > 0, then
    `pos < (a.val / R + 1) * R ≤ a.val + R < k + R`. -/
private lemma good_radius_implies_close {n : ℕ}
    (w : Fin n → Fin n) (hw : Function.Injective w) (a : Fin n)
    (k depth : ℕ) (ha : a.val < k) (hR : 0 < n / 2 ^ depth)
    (hgood : hasGoodRadius w hw a depth) :
    ¬(k + n / 2 ^ depth ≤ (Finite.surjective_of_injective hw a).choose.val ∧
       (w (Finite.surjective_of_injective hw a).choose).val < k) := by
  unfold hasGoodRadius at hgood
  set R := n / 2 ^ depth with hR_def
  set pos := (Finite.surjective_of_injective hw a).choose
  intro ⟨hfar, _⟩
  -- From pos / R = a.val / R: pos = (pos/R)*R + pos%R = (a.val/R)*R + pos%R
  -- So pos < (a.val/R)*R + R = (a.val/R + 1)*R ≤ a.val + R < k + R
  have hmod : pos.val % R < R := Nat.mod_lt pos.val hR
  have hdiv : pos.val = (pos.val / R) * R + pos.val % R := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod pos.val R).symm
  have hle : (a.val / R) * R ≤ a.val := Nat.div_mul_le_self a.val R
  rw [hgood] at hdiv
  omega

/-- The error set restricted to chunk `c`: values `a` in chunk `c` that lose
    good radius at level `l`. -/
private noncomputable def errorSetInChunk {n : ℕ}
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (v : Equiv.Perm (Fin n)) (k l c : ℕ) : Finset (Fin n) :=
  (errorSetAtLevel halvers v k l).filter (fun a ↦ a.val / (n / 2 ^ l) = c)

/-- Values < k in chunk `c` at level `l`. -/
private def valuesInChunk (n k l c : ℕ) : Finset (Fin n) :=
  univ.filter (fun a : Fin n ↦ a.val < k ∧ a.val / (n / 2 ^ l) = c)

/-- **Per-chunk error bound**: Within chunk `c`, at most `ε · k_c` values lose
    good radius, where `k_c` = number of values < k in chunk `c`.
    This is where `EpsilonInitialHalved` is used.

    The halver at level `l` independently acts on each chunk of size `n/2^l`.
    Within chunk `c`, it rearranges values among positions `[c·chunkSize, c·chunkSize + 2·halfChunk)`.
    Values that end up in the wrong sub-half (relative to their target) are bounded
    by `ε · k_c` via `EpsilonInitialHalved` applied to the local permutation. -/
private lemma error_set_chunk_bound {n : ℕ} (ε : ℝ) (hε : 0 < ε)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (hhalvers : ∀ m, IsEpsilonHalver (halvers m) ε)
    (v : Equiv.Perm (Fin n)) (k l c : ℕ) (hk : k ≤ n)
    (hpow : 2 ^ (l + 1) ∣ n) :
    ((errorSetInChunk halvers v k l c).card : ℝ) ≤ ε * (valuesInChunk n k l c).card := by
  sorry

/-- The error set is the disjoint union of per-chunk error sets over chunks
    `c ∈ range (2^l)`. -/
private lemma error_set_eq_biUnion {n : ℕ}
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (v : Equiv.Perm (Fin n)) (k l : ℕ)
    (hpow : 2 ^ (l + 1) ∣ n) :
    errorSetAtLevel halvers v k l =
    (Finset.range (2 ^ l)).biUnion (errorSetInChunk halvers v k l) := by
  ext a
  constructor
  · intro ha
    -- a's chunk index is a.val / (n / 2^l), which is < 2^l
    have hdvd : 2 ^ l ∣ n := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega : l ≤ l + 1)) hpow
    have hc : a.val / (n / 2 ^ l) < 2 ^ l := by
      by_cases hn : n = 0
      · subst hn; exact absurd a.isLt (by simp)
      · apply Nat.div_lt_of_lt_mul
        rw [Nat.div_mul_cancel hdvd]
        exact a.isLt
    exact Finset.mem_biUnion.mpr ⟨a.val / (n / 2 ^ l), Finset.mem_range.mpr hc,
      Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  · intro ha
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp ha
    exact (Finset.mem_filter.mp hc).1

/-- The number of `Fin n` elements with `.val < k` is `k` (when `k ≤ n`). -/
private lemma card_filter_lt_val {n k : ℕ} (hk : k ≤ n) :
    (univ.filter (fun a : Fin n ↦ a.val < k)).card = k := by
  rcases Nat.lt_or_eq_of_le hk with h | h
  · -- k < n: the filter set = Fin.Iio ⟨k, h⟩
    have heq : univ.filter (fun a : Fin n ↦ a.val < k) = Finset.Iio ⟨k, h⟩ := by
      ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio,
        Fin.lt_def]
    rw [heq, Fin.card_Iio]
  · -- k = n: every element qualifies
    subst h
    have : univ.filter (fun a : Fin k ↦ a.val < k) = univ := by
      rw [Finset.filter_true_of_mem]; intro a _; exact a.isLt
    rw [this, Finset.card_univ, Fintype.card_fin]

/-- Summing `k_c` over all chunks gives `k`. -/
private lemma sum_valuesInChunk {n k l : ℕ} (hpow : 2 ^ (l + 1) ∣ n) (hk : k ≤ n) :
    (∑ c ∈ Finset.range (2 ^ l), ((valuesInChunk n k l c).card : ℝ)) = ↑k := by
  have hdvd : 2 ^ l ∣ n := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hpow
  suffices h : (∑ c ∈ Finset.range (2 ^ l), (valuesInChunk n k l c).card) = k by
    exact_mod_cast h
  -- valuesInChunk sets are pairwise disjoint (different chunk indices)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (2 ^ l))) (valuesInChunk n k l) := by
    intro c₁ _ c₂ _ hne
    show Disjoint (valuesInChunk n k l c₁) (valuesInChunk n k l c₂)
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    simp only [valuesInChunk, Finset.mem_filter] at ha1 ha2
    exact hne (ha1.2.2.symm.trans ha2.2.2)
  -- Their union equals {a | a.val < k}
  set S := univ.filter (fun a : Fin n ↦ a.val < k)
  have hunion : (Finset.range (2 ^ l)).biUnion (valuesInChunk n k l) = S := by
    ext a
    constructor
    · intro ha
      obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp ha
      simp only [valuesInChunk, Finset.mem_filter] at hc
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc.2.1⟩
    · intro ha
      have hak := (Finset.mem_filter.mp ha).2
      refine Finset.mem_biUnion.mpr ⟨a.val / (n / 2 ^ l), ?_, ?_⟩
      · exact Finset.mem_range.mpr
          (Nat.div_lt_of_lt_mul (by rw [Nat.div_mul_cancel hdvd]; exact a.isLt))
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hak, rfl⟩
  calc ∑ c ∈ Finset.range (2 ^ l), (valuesInChunk n k l c).card
      = ((Finset.range (2 ^ l)).biUnion (valuesInChunk n k l)).card :=
        (Finset.card_biUnion hdisj).symm
    _ = S.card := by rw [hunion]
    _ = k := card_filter_lt_val hk

private lemma error_set_bound {n : ℕ} (ε : ℝ) (hε : 0 < ε)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (hhalvers : ∀ m, IsEpsilonHalver (halvers m) ε)
    (v : Equiv.Perm (Fin n)) (k l : ℕ) (hk : k ≤ n)
    (hpow : 2 ^ (l + 1) ∣ n) :
    ((errorSetAtLevel halvers v k l).card : ℝ) ≤ ε * ↑k := by
  rw [error_set_eq_biUnion halvers v k l hpow]
  calc (((Finset.range (2 ^ l)).biUnion (errorSetInChunk halvers v k l)).card : ℝ)
      ≤ ∑ c ∈ Finset.range (2 ^ l), ((errorSetInChunk halvers v k l c).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ c ∈ Finset.range (2 ^ l), ε * (valuesInChunk n k l c).card := by
        apply Finset.sum_le_sum
        intro c _
        exact error_set_chunk_bound ε hε halvers hhalvers v k l c hk hpow
    _ = ε * ∑ c ∈ Finset.range (2 ^ l), ((valuesInChunk n k l c).card : ℝ) := by
        rw [Finset.mul_sum]
    _ = ε * ↑k := by rw [sum_valuesInChunk hpow hk]

/-- **Radius inheritance** (induction base): At level 0, every value has
    good radius (single chunk = whole array, chunkSize = n). -/
private lemma good_radius_base {n : ℕ} (w : Fin n → Fin n)
    (hw : Function.Injective w) (a : Fin n) :
    hasGoodRadius w hw a 0 := by
  unfold hasGoodRadius
  simp only [pow_zero, Nat.div_one]
  rw [Nat.div_eq_of_lt (Finite.surjective_of_injective hw a).choose.isLt,
      Nat.div_eq_of_lt a.isLt]

/-- **Error set coverage**: If a value `a < k` does NOT have good radius at
    level `depth`, then it must be in some `errorSetAtLevel` for some `l < depth`.
    This is because good radius holds at level 0, so the first level where it
    fails gives an error set membership.

    Formally: `a.val < k ∧ ¬goodRadius(a, depth) → a ∈ ⋃_{l < depth} E_l`. -/
private lemma not_good_radius_in_error_set {n : ℕ}
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (v : Equiv.Perm (Fin n)) (a : Fin n)
    (k depth : ℕ) (ha : a.val < k)
    (hbad : ¬hasGoodRadius
      ((halverNetwork n halvers depth).exec (v : Fin n → Fin n))
      (ComparatorNetwork.exec_injective _ v.injective) a depth) :
    ∃ l, l < depth ∧ a ∈ errorSetAtLevel halvers v k l := by
  induction depth with
  | zero =>
    -- At depth 0, good_radius_base gives hasGoodRadius, contradicting hbad
    exact absurd (good_radius_base _ _ a) hbad
  | succ d ih =>
    -- Either hasGoodRadius at level d, or not
    by_cases hd : hasGoodRadius
        ((halverNetwork n halvers d).exec (v : Fin n → Fin n))
        (ComparatorNetwork.exec_injective _ v.injective) a d
    · -- Good at level d, bad at level d+1: a ∈ errorSetAtLevel d
      exact ⟨d, Nat.lt_succ_of_le le_rfl,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, hd, hbad⟩⟩
    · -- Bad at level d: by induction hypothesis
      obtain ⟨l, hl, hmem⟩ := ih hd
      exact ⟨l, Nat.lt_succ_of_lt hl, hmem⟩

/-- **Dual convergence lemma** (Step 2, end segments): If a value `a` with
    `a.val ≥ n - k` has good radius at level `depth`, and R > 0, then its
    position is ≥ n - k - R, so it doesn't contribute to `farLargeCount`.

    The proof: `pos / R = a.val / R` and `a.val ≥ n - k` imply
    `pos ≥ ((n-k)/R) * R = (n-k) - (n-k)%R ≥ n - k - R + 1`,
    contradicting `pos + k + R < n`. -/
private lemma good_radius_implies_close_dual {n : ℕ}
    (w : Fin n → Fin n) (hw : Function.Injective w) (a : Fin n)
    (k depth : ℕ) (ha : n ≤ a.val + k) (hR : 0 < n / 2 ^ depth)
    (hgood : hasGoodRadius w hw a depth) :
    ¬((Finite.surjective_of_injective hw a).choose.val + k + n / 2 ^ depth < n ∧
       n ≤ (w (Finite.surjective_of_injective hw a).choose).val + k) := by
  unfold hasGoodRadius at hgood
  set R := n / 2 ^ depth with hR_def
  set pos := (Finite.surjective_of_injective hw a).choose
  intro ⟨hfar, _⟩
  -- pos / R = a.val / R, and a.val ≥ n - k
  -- pos ≥ (pos / R) * R = (a.val / R) * R ≥ ((n-k)/R) * R
  -- ((n-k)/R) * R = (n-k) - (n-k)%R, and (n-k)%R < R, so ((n-k)/R)*R > n-k-R
  have hpos_ge : (pos.val / R) * R ≤ pos.val := Nat.div_mul_le_self pos.val R
  -- From hfar: pos.val + k + R < n, so pos.val < n - k - R
  -- From hgood: pos.val / R = a.val / R
  -- a.val ≥ n - k, so a.val / R ≥ (n - k) / R
  have ha_div : (n - k) / R ≤ a.val / R := Nat.div_le_div_right (by omega)
  rw [hgood] at hpos_ge
  -- pos.val ≥ (a.val / R) * R ≥ ((n-k) / R) * R
  have hge : ((n - k) / R) * R ≤ pos.val := le_trans (Nat.mul_le_mul_right R ha_div) hpos_ge
  -- ((n-k) / R) * R ≥ (n - k) - (R - 1) = n - k - R + 1
  have hmod : (n - k) % R < R := Nat.mod_lt (n - k) hR
  have hdivmod : (n - k) = ((n - k) / R) * R + (n - k) % R := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod (n - k) R).symm
  -- So ((n-k)/R)*R = (n-k) - (n-k)%R, and pos ≥ this, giving pos + k + R ≥ n + 1
  omega

/-- **Dual error set**: values `a` with `a.val ≥ n - k` that have good radius
    at level `l` but lose it at level `l + 1`. -/
private noncomputable def errorSetAtLevelDual {n : ℕ}
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (v : Equiv.Perm (Fin n)) (k l : ℕ) : Finset (Fin n) :=
  let w_l := (halverNetwork n halvers l).exec (v : Fin n → Fin n)
  let w_l1 := (halverNetwork n halvers (l + 1)).exec (v : Fin n → Fin n)
  let hw_l := ComparatorNetwork.exec_injective _ v.injective
  let hw_l1 := ComparatorNetwork.exec_injective _ v.injective
  univ.filter (fun a : Fin n ↦
    n ≤ a.val + k ∧
    hasGoodRadius w_l hw_l a l ∧
    ¬hasGoodRadius w_l1 hw_l1 a (l + 1))

/-- Dual error set restricted to chunk `c`. -/
private noncomputable def errorSetInChunkDual {n : ℕ}
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (v : Equiv.Perm (Fin n)) (k l c : ℕ) : Finset (Fin n) :=
  (errorSetAtLevelDual halvers v k l).filter (fun a ↦ a.val / (n / 2 ^ l) = c)

/-- Dual values in chunk: values `a` with `n ≤ a.val + k` in chunk `c`. -/
private def valuesInChunkDual (n k l c : ℕ) : Finset (Fin n) :=
  univ.filter (fun a : Fin n ↦ n ≤ a.val + k ∧ a.val / (n / 2 ^ l) = c)

/-- **Per-chunk error bound (dual)**: Within chunk `c`, at most `ε · k_c` values
    lose good radius. Uses `EpsilonFinalHalved`. -/
private lemma error_set_chunk_bound_dual {n : ℕ} (ε : ℝ) (hε : 0 < ε)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (hhalvers : ∀ m, IsEpsilonHalver (halvers m) ε)
    (v : Equiv.Perm (Fin n)) (k l c : ℕ) (hk : k ≤ n)
    (hpow : 2 ^ (l + 1) ∣ n) :
    ((errorSetInChunkDual halvers v k l c).card : ℝ) ≤
      ε * (valuesInChunkDual n k l c).card := by
  sorry

private lemma error_set_eq_biUnion_dual {n : ℕ}
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (v : Equiv.Perm (Fin n)) (k l : ℕ)
    (hpow : 2 ^ (l + 1) ∣ n) :
    errorSetAtLevelDual halvers v k l =
    (Finset.range (2 ^ l)).biUnion (errorSetInChunkDual halvers v k l) := by
  ext a
  constructor
  · intro ha
    have hdvd : 2 ^ l ∣ n := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hpow
    have hc : a.val / (n / 2 ^ l) < 2 ^ l := by
      by_cases hn : n = 0
      · subst hn; exact absurd a.isLt (by simp)
      · exact Nat.div_lt_of_lt_mul (by rw [Nat.div_mul_cancel hdvd]; exact a.isLt)
    exact Finset.mem_biUnion.mpr ⟨a.val / (n / 2 ^ l), Finset.mem_range.mpr hc,
      Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  · intro ha
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp ha
    exact (Finset.mem_filter.mp hc).1

/-- The number of `Fin n` elements with `n ≤ a.val + k` is `k` (when `k ≤ n`). -/
private lemma card_filter_ge_val {n k : ℕ} (hk : k ≤ n) :
    (univ.filter (fun a : Fin n ↦ n ≤ a.val + k)).card = k := by
  -- card({a | n ≤ a + k}) + card({a | a < n - k}) = n (partition of Fin n)
  -- card({a | a < n - k}) = n - k (by card_filter_lt_val)
  -- So card({a | n ≤ a + k}) = n - (n - k) = k
  have hcompl : (univ.filter (fun a : Fin n ↦ ¬(n ≤ a.val + k))).card = n - k := by
    have heq : univ.filter (fun a : Fin n ↦ ¬(n ≤ a.val + k)) =
        univ.filter (fun a : Fin n ↦ a.val < n - k) := by
      ext ⟨a, ha⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    rw [heq, card_filter_lt_val (Nat.sub_le n k)]
  have htotal : (univ : Finset (Fin n)).card = n := Finset.card_fin n
  have hpart := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun a ↦ n ≤ a.val + k)
  rw [htotal] at hpart; omega

private lemma sum_valuesInChunkDual {n k l : ℕ} (hpow : 2 ^ (l + 1) ∣ n) (hk : k ≤ n) :
    (∑ c ∈ Finset.range (2 ^ l), ((valuesInChunkDual n k l c).card : ℝ)) = ↑k := by
  have hdvd : 2 ^ l ∣ n := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hpow
  suffices h : (∑ c ∈ Finset.range (2 ^ l), (valuesInChunkDual n k l c).card) = k by
    exact_mod_cast h
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (2 ^ l))) (valuesInChunkDual n k l) := by
    intro c₁ _ c₂ _ hne
    show Disjoint (valuesInChunkDual n k l c₁) (valuesInChunkDual n k l c₂)
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    simp only [valuesInChunkDual, Finset.mem_filter] at ha1 ha2
    exact hne (ha1.2.2.symm.trans ha2.2.2)
  set S := univ.filter (fun a : Fin n ↦ n ≤ a.val + k)
  have hunion : (Finset.range (2 ^ l)).biUnion (valuesInChunkDual n k l) = S := by
    ext a
    constructor
    · intro ha
      obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp ha
      simp only [valuesInChunkDual, Finset.mem_filter] at hc
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc.2.1⟩
    · intro ha
      have hak := (Finset.mem_filter.mp ha).2
      refine Finset.mem_biUnion.mpr ⟨a.val / (n / 2 ^ l), ?_, ?_⟩
      · exact Finset.mem_range.mpr
          (Nat.div_lt_of_lt_mul (by rw [Nat.div_mul_cancel hdvd]; exact a.isLt))
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hak, rfl⟩
  calc ∑ c ∈ Finset.range (2 ^ l), (valuesInChunkDual n k l c).card
      = ((Finset.range (2 ^ l)).biUnion (valuesInChunkDual n k l)).card :=
        (Finset.card_biUnion hdisj).symm
    _ = S.card := by rw [hunion]
    _ = k := card_filter_ge_val hk

/-- **Per-level error bound (dual)**: At each level `l`, the dual error set
    has at most `ε · k` elements. -/
private lemma error_set_bound_dual {n : ℕ} (ε : ℝ) (hε : 0 < ε)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (hhalvers : ∀ m, IsEpsilonHalver (halvers m) ε)
    (v : Equiv.Perm (Fin n)) (k l : ℕ) (hk : k ≤ n)
    (hpow : 2 ^ (l + 1) ∣ n) :
    ((errorSetAtLevelDual halvers v k l).card : ℝ) ≤ ε * ↑k := by
  rw [error_set_eq_biUnion_dual halvers v k l hpow]
  calc (((Finset.range (2 ^ l)).biUnion (errorSetInChunkDual halvers v k l)).card : ℝ)
      ≤ ∑ c ∈ Finset.range (2 ^ l), ((errorSetInChunkDual halvers v k l c).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ c ∈ Finset.range (2 ^ l), ε * (valuesInChunkDual n k l c).card := by
        apply Finset.sum_le_sum
        intro c _
        exact error_set_chunk_bound_dual ε hε halvers hhalvers v k l c hk hpow
    _ = ε * ∑ c ∈ Finset.range (2 ^ l), ((valuesInChunkDual n k l c).card : ℝ) := by
        rw [Finset.mul_sum]
    _ = ε * ↑k := by rw [sum_valuesInChunkDual hpow hk]

/-- **Dual error set coverage**: If `a.val ≥ n - k` and ¬goodRadius at depth,
    then `a ∈ errorSetAtLevelDual` for some `l < depth`. -/
private lemma not_good_radius_in_error_set_dual {n : ℕ}
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (v : Equiv.Perm (Fin n)) (a : Fin n)
    (k depth : ℕ) (ha : n ≤ a.val + k)
    (hbad : ¬hasGoodRadius
      ((halverNetwork n halvers depth).exec (v : Fin n → Fin n))
      (ComparatorNetwork.exec_injective _ v.injective) a depth) :
    ∃ l, l < depth ∧ a ∈ errorSetAtLevelDual halvers v k l := by
  induction depth with
  | zero => exact absurd (good_radius_base _ _ a) hbad
  | succ d ih =>
    by_cases hd : hasGoodRadius
        ((halverNetwork n halvers d).exec (v : Fin n → Fin n))
        (ComparatorNetwork.exec_injective _ v.injective) a d
    · exact ⟨d, Nat.lt_succ_of_le le_rfl,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, hd, hbad⟩⟩
    · obtain ⟨l, hl, hmem⟩ := ih hd
      exact ⟨l, Nat.lt_succ_of_lt hl, hmem⟩

end Trajectory

/-- After `depth` levels, the far-small count at radius `n / 2^depth` is
    at most `ε · depth · k`.

    Proved via trajectory argument:
    1. Values with good radius at depth don't contribute (convergence lemma)
    2. Values without good radius are in some error set (coverage)
    3. Each error set has size ≤ ε·k (per-level bound)
    4. Union bound: total ≤ depth·ε·k -/
private lemma farSmallCount_depth_bound {n : ℕ} (ε : ℝ) (depth : ℕ)
    (hε : 0 < ε)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (hhalvers : ∀ m, IsEpsilonHalver (halvers m) ε)
    (hpow : 2 ^ depth ∣ n)
    (v : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n) :
    (farSmallCount ((halverNetwork n halvers depth).exec (v : Fin n → Fin n))
      k (n / 2 ^ depth) : ℝ)
    ≤ ε * ↑depth * ↑k := by
  classical
  -- Handle n = 0: Fin 0 is empty, everything is 0
  by_cases hn : n = 0
  · subst hn; simp [farSmallCount]; positivity
  -- Set up notation
  set R := n / 2 ^ depth with hR_def
  set w := (halverNetwork n halvers depth).exec (v : Fin n → Fin n) with hw_def
  have hw_inj : Function.Injective w := ComparatorNetwork.exec_injective _ v.injective
  -- R > 0 since 2^depth | n and n > 0
  have hR_pos : 0 < R := by
    rw [hR_def]; exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpow)
      (Nat.pos_of_ne_zero (by positivity))
  -- Define the far-small filter set
  set F := univ.filter (fun p : Fin n ↦ k + R ≤ p.val ∧ (w p).val < k)
  -- Map F through w to get values; by injectivity |w(F)| = |F|
  -- w(F) ⊆ {a : Fin n | a.val < k}
  -- Each a in w(F) is NOT good-radius → in some error set
  -- So w(F) ⊆ (range depth).biUnion (errorSetAtLevel halvers v k)
  -- Step 1: Map F to values via w. |F| = |F.image w| by injectivity.
  have hF_card : F.card = (F.image w).card :=
    (Finset.card_image_of_injective F hw_inj).symm
  -- Step 2: Each value a = w p in F.image w has a.val < k and is in some error set.
  have hF_sub : F.image w ⊆ (Finset.range depth).biUnion (errorSetAtLevel halvers v k) := by
    intro a ha
    obtain ⟨p, hp, hpw⟩ := Finset.mem_image.mp ha
    rw [Finset.mem_filter] at hp
    have hp_far : k + R ≤ p.val := hp.2.1
    have ha_small : a.val < k := by rw [← hpw]; exact hp.2.2
    -- a = w p, so the preimage of a under w is p
    -- We need: ¬hasGoodRadius w hw_inj a depth
    -- good_radius_implies_close says: if hasGoodRadius, then ¬(k + R ≤ pos ∧ (w pos).val < k)
    -- But pos = (surj a).choose, which is p (since w p = a and w is injective)
    have hbad : ¬hasGoodRadius w hw_inj a depth := by
      intro hgood
      apply good_radius_implies_close w hw_inj a k depth ha_small hR_pos hgood
      -- Need: k + R ≤ (surj a).choose.val ∧ (w (surj a).choose).val < k
      have hsurj_eq : (Finite.surjective_of_injective hw_inj a).choose = p := by
        have := (Finite.surjective_of_injective hw_inj a).choose_spec
        -- this : w (surj a).choose = a, and we know w p = a (from hpw)
        exact hw_inj (this.trans hpw.symm)
      constructor
      · rw [hsurj_eq]; exact hp_far
      · rw [hsurj_eq, hpw]; exact ha_small
    obtain ⟨l, hl, hmem⟩ := not_good_radius_in_error_set halvers v a k depth ha_small hbad
    exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_range.mpr hl, hmem⟩
  -- Step 3: Union bound
  calc (F.card : ℝ)
      = ((F.image w).card : ℝ) := by rw [hF_card]
    _ ≤ ((Finset.range depth).biUnion (errorSetAtLevel halvers v k)).card := by
        exact_mod_cast Finset.card_le_card hF_sub
    _ ≤ ∑ l ∈ Finset.range depth, ((errorSetAtLevel halvers v k l).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _l ∈ Finset.range depth, (ε * ↑k) := by
        apply Finset.sum_le_sum
        intro l hl
        have hl' : l < depth := Finset.mem_range.mp hl
        have hpow_l : 2 ^ (l + 1) ∣ n := by
          exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hpow
        exact error_set_bound ε hε halvers hhalvers v k l hk hpow_l
    _ = ε * ↑depth * ↑k := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

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
    (hpow : 2 ^ depth ∣ n)
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
        farSmallCount_depth_bound ε depth hε halvers hhalvers hpow v k hk


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
    (hpow : 2 ^ depth ∣ n)
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
    _ ≤ δ * ↑k := halverNetwork_far_small_bound ε depth hε hε1 hdepth halvers hhalvers hpow v k hk

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
    (hpow : 2 ^ depth ∣ n)
    (v : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n) :
    (farLargeCount ((halverNetwork n halvers depth).exec (v : Fin n → Fin n))
      k (n / 2 ^ depth) : ℝ)
    ≤ ε * ↑depth * ↑k := by
  classical
  by_cases hn : n = 0
  · subst hn; simp [farLargeCount]; positivity
  set R := n / 2 ^ depth with hR_def
  set w := (halverNetwork n halvers depth).exec (v : Fin n → Fin n) with hw_def
  have hw_inj : Function.Injective w := ComparatorNetwork.exec_injective _ v.injective
  have hR_pos : 0 < R := by
    rw [hR_def]; exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpow)
      (Nat.pos_of_ne_zero (by positivity))
  set F := univ.filter (fun p : Fin n ↦ p.val + k + R < n ∧ n ≤ (w p).val + k)
  -- Step 1: |F| = |F.image w| by injectivity
  have hF_card : F.card = (F.image w).card :=
    (Finset.card_image_of_injective F hw_inj).symm
  -- Step 2: Each a = w p in F.image w has a.val ≥ n - k and is in some dual error set
  have hF_sub : F.image w ⊆ (Finset.range depth).biUnion (errorSetAtLevelDual halvers v k) := by
    intro a ha
    obtain ⟨p, hp, hpw⟩ := Finset.mem_image.mp ha
    rw [Finset.mem_filter] at hp
    have hp_far : p.val + k + R < n := hp.2.1
    have ha_large : n ≤ a.val + k := by rw [← hpw]; exact hp.2.2
    have hbad : ¬hasGoodRadius w hw_inj a depth := by
      intro hgood
      apply good_radius_implies_close_dual w hw_inj a k depth ha_large hR_pos hgood
      have hsurj_eq : (Finite.surjective_of_injective hw_inj a).choose = p := by
        have := (Finite.surjective_of_injective hw_inj a).choose_spec
        exact hw_inj (this.trans hpw.symm)
      constructor
      · rw [hsurj_eq]; exact hp_far
      · rw [hsurj_eq, hpw]; exact ha_large
    obtain ⟨l, hl, hmem⟩ := not_good_radius_in_error_set_dual halvers v a k depth ha_large hbad
    exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_range.mpr hl, hmem⟩
  -- Step 3: Union bound
  calc (F.card : ℝ)
      = ((F.image w).card : ℝ) := by rw [hF_card]
    _ ≤ ((Finset.range depth).biUnion (errorSetAtLevelDual halvers v k)).card := by
        exact_mod_cast Finset.card_le_card hF_sub
    _ ≤ ∑ l ∈ Finset.range depth, ((errorSetAtLevelDual halvers v k l).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _l ∈ Finset.range depth, (ε * ↑k) := by
        apply Finset.sum_le_sum
        intro l hl
        have hl' : l < depth := Finset.mem_range.mp hl
        have hpow_l : 2 ^ (l + 1) ∣ n :=
          Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hpow
        exact error_set_bound_dual ε hε halvers hhalvers v k l hk hpow_l
    _ = ε * ↑depth * ↑k := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- Dual of `halverNetwork_far_small_bound` for end segments. -/
private lemma halverNetwork_far_large_bound {n : ℕ} (ε : ℝ) (depth : ℕ)
    (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hdepth : (1 : ℝ) ≤ ε * ↑depth * 2 ^ depth)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (hhalvers : ∀ m, IsEpsilonHalver (halvers m) ε)
    (hpow : 2 ^ depth ∣ n)
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
        farLargeCount_depth_bound ε depth hε halvers hhalvers hpow v k hk

/-- The dual: final-segment nearsortedness follows from `EpsilonFinalHalved`
    (which is part of `IsEpsilonHalver`). Uses `farLargeCount_depth_bound`
    (the dual of `farSmallCount_depth_bound`). -/
theorem halverNetwork_finalNearsorted {n : ℕ} (ε : ℝ) (depth d : ℕ)
    (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hdepth : (1 : ℝ) ≤ ε * ↑depth * 2 ^ depth)
    (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (hhalvers : ∀ m, IsEpsilonHalver (halvers m) ε)
    (hhalver_size : ∀ m, (halvers m).size ≤ m * d)
    (hpow : 2 ^ depth ∣ n)
    (v : Equiv.Perm (Fin n)) :
    FinalNearsorted ((halverNetwork n halvers depth).exec v) (ε * ↑depth) := by
  -- FinalNearsorted = InitialNearsorted on (Fin n)ᵒᵈ
  unfold FinalNearsorted
  intro k hk
  -- Unfold the let-bindings from InitialNearsorted and simplify Fintype.card
  dsimp only []
  simp only [Fintype.card_orderDual, Fintype.card_fin] at hk ⊢
  set δ : ℝ := ε * ↑depth
  set w := (halverNetwork n halvers depth).exec (v : Fin n → Fin n)
  set R := ⌊δ * ↑n⌋₊
  have hw : Function.Injective w := ComparatorNetwork.exec_injective _ v.injective
  -- Convert rank-based filters on (Fin n)ᵒᵈ to val-based filters on Fin n
  -- rank a < k' in (Fin n)ᵒᵈ ↔ n - 1 - a.val < k' ↔ n ≤ a.val + k'
  have hconv : ∀ k' : ℕ,
      (univ.filter (fun a : (Fin n)ᵒᵈ ↦ rank a < k')) =
      (univ.filter (fun a : Fin n ↦ n ≤ a.val + k')) := by
    intro k'
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, rank_fin_od]
    have := (OrderDual.ofDual a).isLt
    omega
  rw [hconv k, hconv (k + R)]
  -- Now apply the dual reformulation and bound
  -- After hconv, the Sε filter uses a.val + (k + R); convert to a.val + k + R
  have hassoc : (univ.filter (fun a : Fin n ↦ n ≤ a.val + (k + R))) =
      (univ.filter (fun a : Fin n ↦ n ≤ a.val + k + R)) := by
    congr 1; ext a; constructor <;> intro h <;> omega
  rw [hassoc]
  calc ((univ.filter (fun a : Fin n ↦ n ≤ a.val + k) \
          (univ.filter (fun a : Fin n ↦ n ≤ a.val + k + R)).image w).card : ℝ)
      = (farLargeCount w k R : ℝ) := by exact_mod_cast sdiff_image_card_eq_far_large_count hw
    _ ≤ δ * ↑k :=
        halverNetwork_far_large_bound ε depth hε hε1 hdepth halvers hhalvers hpow v k hk
