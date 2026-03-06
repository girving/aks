module
/-
  # General Halver for Arbitrary Sizes

  Builds a halver network for any target size `m ≥ 1` via:
  1. Pick `n = max(3, √(Q₀·m) + 1)` so that `mgg n` has `n² ≥ m` vertices
  2. Apply iterated graph squaring to shrink spectral gap below `ε`
  3. Use the König quotient halver (`konigQuotientHalver`) to project to `m` wires

  The MGG graph `mgg n` is 8-regular on `n²` vertices with spectral gap
  ≤ `5√2/8 < 89/100`. The side length `n` is chosen so that `n²/m ≥ Q₀`,
  which (via `sufficient_epsCond`) ensures the algebraic condition `hε_cond`
  holds.

  Key results:
  - `mggHalverNet`: halver at `2 * m` wires for any `m ≥ 1`
  - `mggHalverNet_isEpsilonHalver`: the halver property (proved)
  - `mggHalverNet_depth_le`: m-independent depth bound (proved)
  - `halvers`: concrete entry point, fully proved
-/

public import AKS.Halver.Quotient
public import AKS.Halver.Empty
public import AKS.MGG.Spectral
public import AKS.Graph.Square

@[expose] public section


/-! **Number of Squarings** -/

/-- Iteratively square a rational number `p` times: `iterSq c p = c^(2^p)`.
    Used to compute `β^(2^p)` for finding the number of squarings needed. -/
def iterSq (c : ℚ) : ℕ → ℚ
  | 0 => c
  | p + 1 => iterSq c p * iterSq c p

lemma iterSq_eq_pow (c : ℚ) (p : ℕ) : iterSq c p = c ^ (2 ^ p) := by
  induction p with
  | zero => simp [iterSq]
  | succ p ih => simp [iterSq, ih, pow_succ]; ring

/-- For any `0 ≤ c < 1` and `ε > 0`, there exists `p` with `c^(2^p) ≤ ε`. -/
lemma iterSq_eventually_le' (c ε : ℚ) (hc0 : 0 ≤ c) (hc1 : c < 1) (hε : 0 < ε) :
    ∃ p, iterSq c p ≤ ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hc1
  exact ⟨n, by rw [iterSq_eq_pow]; exact le_of_lt (lt_of_le_of_lt
    (pow_le_pow_of_le_one hc0 hc1.le (le_of_lt Nat.lt_two_pow_self)) hn)⟩


/-! **MGG Spectral Gap Bound (Rational)** -/

/-- Rational upper bound for the MGG spectral gap `5√2/8 ≈ 0.8839`.
    We use `89/100 = 0.89` which satisfies `(5√2/8)² = 50/64 < 7921/10000 = (89/100)²`. -/
def mggBeta : ℚ := 89 / 100

/-- `mggBeta` is nonneg. -/
lemma mggBeta_nn : (0 : ℚ) ≤ mggBeta := by unfold mggBeta; norm_num

/-- `mggBeta` is less than 1. -/
lemma mggBeta_lt_one : mggBeta < 1 := by unfold mggBeta; norm_num

/-- The MGG spectral gap is bounded by `mggBeta`: `spectralGap (mgg n) ≤ 89/100`.
    Proof: `spectralGap (mgg n) ≤ 5√2/8` by `spectralGap_mgg`, and `5√2/8 ≤ 89/100`
    because `(5√2/8)² = 50/64 ≤ 7921/10000 = (89/100)²` (both sides nonneg). -/
theorem mgg_gap_le_mggBeta (n : ℕ) (hn : 3 ≤ n) :
    spectralGap (mgg n) ≤ ↑mggBeta := by
  have h1 := spectralGap_mgg n hn
  have h2 : 5 * Real.sqrt 2 / 8 ≤ (mggBeta : ℝ) := by
    rw [show (mggBeta : ℝ) = 89 / 100 from by unfold mggBeta; push_cast; ring]
    rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 8) (by norm_num : (0:ℝ) < 100)]
    -- Goal: 5 * √2 * 100 ≤ 89 * 8, i.e., 500 * √2 ≤ 712
    -- Square both sides (both nonneg): 500² * 2 = 500000 ≤ 506944 = 712²
    have h_lhs_nn : 0 ≤ 5 * Real.sqrt 2 * 100 := by positivity
    rw [show 89 * (8 : ℝ) = 712 from by norm_num]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 from by norm_num),
               sq_nonneg (5 * Real.sqrt 2 * 100 - 712)]
  exact h1.trans h2


/-! **Number of Squarings (MGG)** -/

/-- Number of MGG graph squarings needed for spectral gap `≤ ε`.
    The smallest `p` such that `(89/100)^(2^p) ≤ ε`. -/
def mggNumSquarings (ε : ℚ) (hε : 0 < ε) : ℕ :=
  Nat.find (iterSq_eventually_le' mggBeta ε mggBeta_nn mggBeta_lt_one hε)

/-- `mggNumSquarings` satisfies its spec. -/
lemma mggNumSquarings_spec (ε : ℚ) (hε : 0 < ε) :
    iterSq mggBeta (mggNumSquarings ε hε) ≤ ε :=
  Nat.find_spec (iterSq_eventually_le' mggBeta ε mggBeta_nn mggBeta_lt_one hε)


/-! **Algebraic Condition Infrastructure** -/

/-- The algebraic discriminant `A = ε² - β²(1-ε)²` from the `hε_cond` condition.
    When `A > 0` and `q` is large enough, `(q+1)²A > (2q+1)ε` holds. -/
def epsCondA (ε β : ℚ) : ℚ := ε ^ 2 - β ^ 2 * (1 - ε) ^ 2

/-- `A > 0` when `0 < ε`, `0 ≤ β ≤ ε`, `β < 1`. -/
lemma epsCondA_pos (ε β : ℚ) (hε : 0 < ε) (hβ : 0 ≤ β) (hβε : β ≤ ε) (hβ1 : β < 1) :
    0 < epsCondA ε β := by
  unfold epsCondA
  have key : ε ^ 2 - β ^ 2 * (1 - ε) ^ 2 =
    (ε - β * (1 - ε)) * (ε + β * (1 - ε)) := by ring
  rw [key]; apply mul_pos
  · by_cases h : ε ≤ 1
    · have : (1 - ε) * (ε - β) ≥ 0 := mul_nonneg (by linarith) (by linarith)
      nlinarith [mul_pos hε hε]
    · push_neg at h; have : β * (ε - 1) ≥ 0 := mul_nonneg hβ (by linarith); linarith
  · by_cases h : ε ≤ 1
    · have : β * (1 - ε) ≥ 0 := mul_nonneg hβ (by linarith); linarith
    · push_neg at h; nlinarith

/-- Bridge lemma: if `Q₀ * A > 3ε` then the full `hε_cond` holds for all `q ≥ Q₀`.
    This avoids proving `hε_cond` directly for each `q`; we just need `N/m ≥ Q₀`. -/
theorem sufficient_epsCond (ε A : ℝ) (hε : 0 < ε) (Q₀ : ℕ) (hQ₀ : 1 ≤ Q₀)
    (hQ₀A : (Q₀ : ℝ) * A > 3 * ε)
    (q : ℕ) (hq : Q₀ ≤ q) :
    (↑q + 1) ^ 2 * A > (2 * ↑q + 1) * ε := by
  have hQ₀_pos : (0 : ℝ) < Q₀ := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_pos hQ₀
  have hA : 0 < A := by
    by_contra h; push_neg at h
    have : (Q₀ : ℝ) * A ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hQ₀_pos.le h; linarith
  have hQ₀_le : (Q₀ : ℝ) ≤ q := by exact_mod_cast hq
  have hq_ge1 : (1 : ℝ) ≤ (q : ℝ) := le_trans (by exact_mod_cast hQ₀) hQ₀_le
  have h1 : (↑q + 1) ^ 2 * A ≥ (↑q : ℝ) ^ 2 * A := by nlinarith [sq_nonneg (q : ℝ)]
  have h2 : (↑q : ℝ) ^ 2 * A ≥ ↑Q₀ * ↑q * A := by
    have h2a : (↑q : ℝ) * ((↑q : ℝ) - ↑Q₀) ≥ 0 := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have h3 : ↑Q₀ * (↑q : ℝ) * A > 3 * ↑q * ε := by
    have hq_pos : (↑q : ℝ) > 0 := by linarith
    nlinarith [mul_pos hq_pos hA]
  have h4 : 3 * (↑q : ℝ) * ε ≥ (2 * ↑q + 1) * ε := by
    have hq_sub : (↑q : ℝ) - 1 ≥ 0 := by linarith
    nlinarith [mul_nonneg hq_sub hε.le]
  linarith


/-! **Q₀ Computation** -/

/-- Existence of Q₀: for any `A > 0`, there exists `Q₀`
    such that `Q₀ * A > 3ε`. -/
lemma mggQ0_exists' (ε A : ℚ) (hA : 0 < A) :
    ∃ Q₀ : ℕ, (Q₀ : ℚ) * A > 3 * ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (3 * ε / A)
  refine ⟨n, ?_⟩; rwa [gt_iff_lt, ← div_lt_iff₀ hA]

/-- Helper for computing `mggQ0`: the `A` value for given `ε`. -/
def mggCondA (ε : ℚ) (hε : 0 < ε) : ℚ :=
  epsCondA ε (iterSq mggBeta (mggNumSquarings ε hε))

/-- The `A` value is positive. -/
lemma mggCondA_pos (ε : ℚ) (hε : 0 < ε) : 0 < mggCondA ε hε := by
  unfold mggCondA
  have hβ_nn : 0 ≤ iterSq mggBeta (mggNumSquarings ε hε) := by
    rw [iterSq_eq_pow]; exact pow_nonneg mggBeta_nn _
  have hβε := mggNumSquarings_spec ε hε
  have hβ1 : iterSq mggBeta (mggNumSquarings ε hε) < 1 := by
    rw [iterSq_eq_pow]; exact pow_lt_one₀ mggBeta_nn mggBeta_lt_one (by positivity)
  exact epsCondA_pos ε _ hε hβ_nn hβε hβ1

/-- The Q₀ value for the MGG construction: the smallest `Q₀` such that `Q₀ * A > 3ε`.
    Uses `Nat.find` to keep the definition computable. -/
def mggQ0 (ε : ℚ) (hε : 0 < ε) : ℕ :=
  max 1 (Nat.find (mggQ0_exists' ε (mggCondA ε hε) (mggCondA_pos ε hε)))

/-- `mggQ0 ≥ 1`. -/
lemma mggQ0_pos (ε : ℚ) (hε : 0 < ε) : 1 ≤ mggQ0 ε hε := le_max_left _ _

/-- `mggQ0` satisfies the sufficient condition: `Q₀ * A > 3ε`. -/
lemma mggQ0_spec (ε : ℚ) (hε : 0 < ε) :
    (mggQ0 ε hε : ℚ) * mggCondA ε hε > 3 * ε := by
  unfold mggQ0
  have hfind := Nat.find_spec (mggQ0_exists' ε (mggCondA ε hε) (mggCondA_pos ε hε))
  have hA_pos := mggCondA_pos ε hε
  set k := Nat.find (mggQ0_exists' ε (mggCondA ε hε) (mggCondA_pos ε hε))
  calc (↑(max 1 k) : ℚ) * mggCondA ε hε
      ≥ ↑k * mggCondA ε hε := by
        apply mul_le_mul_of_nonneg_right _ hA_pos.le
        exact_mod_cast le_max_right 1 k
    _ > 3 * ε := hfind


/-! **Side Length** -/

/-- Side length of the MGG graph for target size `m`:
    `n = max 3 (√(Q₀ * m) + 1)`, ensuring `n ≥ 3` (for `spectralGap_mgg`)
    and `n² ≥ Q₀ * m + 1 > m` (for quotient halver). -/
def mggSideLen (Q0 m : ℕ) : ℕ := max 3 (Nat.sqrt (Q0 * m) + 1)

/-- `mggSideLen ≥ 3`. -/
lemma mggSideLen_ge_three (Q0 m : ℕ) : 3 ≤ mggSideLen Q0 m := le_max_left _ _

/-- `m ≤ n²` where `n = mggSideLen Q0 m`, when `Q0 ≥ 1`. -/
lemma mggSideLen_sq_ge (Q0 m : ℕ) (hQ0 : 1 ≤ Q0) :
    m ≤ mggSideLen Q0 m * mggSideLen Q0 m := by
  unfold mggSideLen
  have h1 : Q0 * m < (Nat.sqrt (Q0 * m) + 1) ^ 2 := Nat.lt_succ_sqrt' (Q0 * m)
  have h2 : m ≤ Q0 * m := Nat.le_mul_of_pos_left m (by omega)
  have h3 : m < (Nat.sqrt (Q0 * m) + 1) ^ 2 := lt_of_le_of_lt h2 h1
  have h4 : m ≤ (Nat.sqrt (Q0 * m) + 1) * (Nat.sqrt (Q0 * m) + 1) := by rw [← sq]; omega
  calc m ≤ (Nat.sqrt (Q0 * m) + 1) * (Nat.sqrt (Q0 * m) + 1) := h4
    _ ≤ max 3 (Nat.sqrt (Q0 * m) + 1) * max 3 (Nat.sqrt (Q0 * m) + 1) :=
      Nat.mul_le_mul (le_max_right _ _) (le_max_right _ _)

/-- `Q0 ≤ n²/m` where `n = mggSideLen Q0 m`, when `m > 0`. -/
lemma mggSideLen_div_ge (Q0 m : ℕ) (hm : 0 < m) :
    Q0 ≤ mggSideLen Q0 m * mggSideLen Q0 m / m := by
  rw [Nat.le_div_iff_mul_le hm]
  unfold mggSideLen
  have h1 : Q0 * m < (Nat.sqrt (Q0 * m) + 1) ^ 2 := Nat.lt_succ_sqrt' (Q0 * m)
  calc Q0 * m
      ≤ (Nat.sqrt (Q0 * m) + 1) * (Nat.sqrt (Q0 * m) + 1) := by rw [← sq]; omega
    _ ≤ max 3 (Nat.sqrt (Q0 * m) + 1) * max 3 (Nat.sqrt (Q0 * m) + 1) :=
      Nat.mul_le_mul (le_max_right _ _) (le_max_right _ _)


/-! **Depth Factor** -/

/-- Depth factor: upper bound on `n²/m + 1` that is independent of `m`.
    We use `7 * Q0 + 10` which covers all cases including `m = 1`.
    For `n = max(3, √(Q0*m) + 1)`, we have `n ≤ √(Q0*m) + 3` (since `max(3,s+1) ≤ s+3`),
    so `n² ≤ (√(Q0*m) + 3)² ≤ Q0*m + 6*Q0*m + 9 = 7*Q0*m + 9`, giving
    `n²/m ≤ 7*Q0 + 9` and `n²/m + 1 ≤ 7*Q0 + 10`. -/
def mggDepthFactor (Q0 : ℕ) : ℕ := 7 * Q0 + 10

/-- `n²/m + 1 ≤ mggDepthFactor Q0` when `m > 0`. -/
lemma mggSideLen_div_le (Q0 m : ℕ) (hm : 0 < m) :
    mggSideLen Q0 m * mggSideLen Q0 m / m + 1 ≤ mggDepthFactor Q0 := by
  unfold mggSideLen mggDepthFactor
  set s := Nat.sqrt (Q0 * m)
  -- max(3, s+1) ≤ s + 3
  have hmax_le : max 3 (s + 1) ≤ s + 3 := by omega
  -- s² ≤ Q0 * m (from Nat.sqrt_le)
  have hs2 : s * s ≤ Q0 * m := Nat.sqrt_le (Q0 * m)
  -- s ≤ Q0 * m (from Nat.sqrt_le_self)
  have hs_le : s ≤ Q0 * m := Nat.sqrt_le_self (Q0 * m)
  -- (s+3)² = s² + 6s + 9 ≤ Q0*m + 6*Q0*m + 9 = 7*Q0*m + 9
  have h_sq : (s + 3) * (s + 3) ≤ 7 * Q0 * m + 9 := by nlinarith
  -- n² ≤ 7*Q0*m + 9
  have hn2_le : max 3 (s + 1) * max 3 (s + 1) ≤ 7 * Q0 * m + 9 :=
    le_trans (Nat.mul_le_mul hmax_le hmax_le) h_sq
  -- n²/m ≤ (7*Q0*m + 9)/m ≤ 7*Q0 + 9
  have hdiv1 : max 3 (s + 1) * max 3 (s + 1) / m ≤ (7 * Q0 * m + 9) / m :=
    Nat.div_le_div_right hn2_le
  have hdiv2 : (7 * Q0 * m + 9) / m ≤ 7 * Q0 + 9 := by
    rw [show 7 * Q0 * m + 9 = 9 + m * (7 * Q0) from by ring]
    rw [Nat.add_mul_div_left 9 (7 * Q0) hm]
    have : 9 / m ≤ 9 := Nat.div_le_self 9 m; omega
  omega


/-! **Halver Construction** -/

/-- Halver network for target size `m ≥ 1`, using the MGG graph.
    Squares `mgg n` `p` times, then applies `konigQuotientHalver`. -/
def mggHalverNet (p Q0 m : ℕ) (hm : 0 < m) :
    ComparatorNetwork (2 * m) :=
  let n := mggSideLen Q0 m
  let G := (mgg n).iterSquare p
  have hd_pos : 0 < iterSquareDeg 8 p := iterSquareDeg_pos (by norm_num) p
  konigQuotientHalver G m hm hd_pos


/-! **Halver Property** -/

/-- The MGG halver is an ε-halver. Chains:
    `spectralGap_mgg` → `mgg_gap_le_mggBeta` → `spectralGap_iterSquare` →
    `sufficient_epsCond` (with Q0, using `mggSideLen_div_ge`) →
    `konigQuotientHalver_isEpsilonHalver`. -/
theorem mggHalverNet_isEpsilonHalver (p Q0 m : ℕ) (hm : 0 < m) (hQ0 : 1 ≤ Q0)
    {ε : ℚ} (hε_pos : 0 < ε)
    (hQ0A : (Q0 : ℚ) * epsCondA ε (iterSq mggBeta p) > 3 * ε) :
    IsEpsilonHalver (mggHalverNet p Q0 m hm) (↑ε) := by
  unfold mggHalverNet
  set n := mggSideLen Q0 m
  have hn3 := mggSideLen_ge_three Q0 m
  have hmN := mggSideLen_sq_ge Q0 m hQ0
  have hd_pos : 0 < iterSquareDeg 8 p := iterSquareDeg_pos (by norm_num) p
  -- Spectral gap bound after squaring
  have hgap_mgg : spectralGap (mgg n) ≤ ↑mggBeta := mgg_gap_le_mggBeta n hn3
  have hgap_sq : spectralGap ((mgg n).iterSquare p) ≤ (↑mggBeta : ℝ) ^ (2^p) := by
    rw [spectralGap_iterSquare]
    exact pow_le_pow_left₀ (spectralGap_nonneg _) hgap_mgg (2^p)
  -- Convert iterSq to pow
  set β := iterSq mggBeta p
  have hβ_eq : (↑β : ℝ) = (↑mggBeta : ℝ) ^ (2^p) := by
    show (↑(iterSq mggBeta p) : ℝ) = _; rw [iterSq_eq_pow]; push_cast; rfl
  have hgap : spectralGap ((mgg n).iterSquare p) ≤ (↑β : ℝ) := by rw [hβ_eq]; exact hgap_sq
  have hβ_nn_q : (0 : ℚ) ≤ β := by
    show 0 ≤ iterSq mggBeta p; rw [iterSq_eq_pow]; exact pow_nonneg mggBeta_nn _
  have hβ_nn : (0 : ℝ) ≤ ↑β := by exact_mod_cast hβ_nn_q
  have hβ1 : (↑β : ℝ) < 1 := by
    exact_mod_cast (show β < 1 from by
      show iterSq mggBeta p < 1; rw [iterSq_eq_pow]
      exact pow_lt_one₀ mggBeta_nn mggBeta_lt_one (by positivity))
  -- Q0 ≤ n²/m
  have hQ0_le := mggSideLen_div_ge Q0 m hm
  -- Cast the ℚ condition to ℝ
  have hε_nn : (0 : ℝ) ≤ ↑ε := by exact_mod_cast hε_pos.le
  have hε_pos_r : (0 : ℝ) < ↑ε := by exact_mod_cast hε_pos
  have hQ0A_r : (Q0 : ℝ) * ((↑ε : ℝ) ^ 2 - (↑β : ℝ) ^ 2 * (1 - ↑ε) ^ 2) > 3 * ↑ε := by
    have h := Rat.cast_lt (K := ℝ).mpr hQ0A
    simp only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] at h
    unfold epsCondA at h; push_cast at h; linarith
  -- Apply sufficient_epsCond
  have hε_cond := sufficient_epsCond (↑ε)
    ((↑ε : ℝ) ^ 2 - (↑β : ℝ) ^ 2 * (1 - ↑ε) ^ 2)
    hε_pos_r Q0 hQ0 hQ0A_r
    (n * n / m) (by exact_mod_cast hQ0_le)
  exact konigQuotientHalver_isEpsilonHalver _ hm hmN hd_pos (↑ε) (↑β) hgap hβ_nn hβ1 hε_nn hε_cond

/-! **Depth Bound** -/

/-- Depth bound for the MGG halver: depth ≤ `iterSquareDeg 8 p * mggDepthFactor Q0`.
    The König quotient halver has depth ≤ `d * (N/m + 1)`, and
    `N/m + 1 ≤ mggDepthFactor Q0`. -/
theorem mggHalverNet_depth_le (p Q0 m : ℕ) (hm : 0 < m) :
    (mggHalverNet p Q0 m hm).depth ≤
      iterSquareDeg 8 p * mggDepthFactor Q0 := by
  unfold mggHalverNet
  have hd_pos : 0 < iterSquareDeg 8 p := iterSquareDeg_pos (by norm_num) p
  calc (konigQuotientHalver _ m hm hd_pos).depth
      ≤ iterSquareDeg 8 p * (mggSideLen Q0 m * mggSideLen Q0 m / m + 1) :=
        konigQuotientHalver_depth_le _ m hm hd_pos
    _ ≤ iterSquareDeg 8 p * mggDepthFactor Q0 := by
        apply Nat.mul_le_mul_left
        exact mggSideLen_div_le Q0 m hm


/-! **Concrete Halver Family** -/

/-- m-independent depth bound for halvers at error `ε`.
    Uses MGG base expander (degree 8). -/
def halverDepth (ε : ℚ) (hε : 0 < ε) : ℕ :=
  iterSquareDeg 8 (mggNumSquarings ε hε) * mggDepthFactor (mggQ0 ε hε)

/-- Concrete halver family using the MGG expander (8-regular on `n²` vertices).
    Takes `ε > 0` and computes the number of squarings and Q₀ internally.

    The halver property is fully proved via:
    1. `mggNumSquarings` finds `p` with `(89/100)^(2^p) ≤ ε`
    2. `mggQ0` finds Q₀ so `Q₀ * A > 3ε`
    3. `mggSideLen` picks `n` with `n² ≥ m` and `n²/m ≥ Q₀`
    4. `sufficient_epsCond` bridges to `hε_cond`
    5. `konigQuotientHalver_isEpsilonHalver` gives the halver property -/
def halvers (ε : ℚ) (hε : 0 < ε) : HalverFamily ε where
  depth := halverDepth ε hε
  net m :=
    if hm : 0 < m then
      mggHalverNet (mggNumSquarings ε hε) (mggQ0 ε hε) m hm
    else (⟨[]⟩ : ComparatorNetwork 0).cast (by omega)
  isHalver m := by
    by_cases hm : 0 < m
    · rw [dif_pos hm]
      exact mggHalverNet_isEpsilonHalver _ _ m hm (mggQ0_pos ε hε)
        hε (mggQ0_spec ε hε)
    · rw [dif_neg hm]
      exact (ComparatorNetwork.cast_isEpsilonHalver _ _ _).mpr
        (emptyNet_isEpsilonHalver ↑ε)
  depth_le m := by
    by_cases hm : 0 < m
    · rw [dif_pos hm]
      exact mggHalverNet_depth_le _ _ m hm
    · rw [dif_neg hm]; simp [ComparatorNetwork.cast_depth, emptyNet_depth]

/-! **Helper lemmas for `halverDepth_antitone`** -/

private theorem iterSq_ge_base {c : ℚ} (hc : 1 ≤ c) (p : ℕ) : c ≤ iterSq c p := by
  induction p with
  | zero => simp [iterSq]
  | succ p ih =>
    simp only [iterSq]; exact le_trans ih (le_mul_of_one_le_right (by linarith) (le_trans hc ih))

private theorem iterSq_mul (a b : ℚ) (p : ℕ) : iterSq a p * iterSq b p = iterSq (a * b) p := by
  induction p with
  | zero => simp [iterSq]
  | succ p ih =>
    simp only [iterSq]
    rw [show iterSq a p * iterSq a p * (iterSq b p * iterSq b p) =
      (iterSq a p * iterSq b p) * (iterSq a p * iterSq b p) from by ring, ih]

private theorem iterSquareDeg_cast (d p : ℕ) : (iterSquareDeg d p : ℚ) = iterSq (d : ℚ) p := by
  induction p with
  | zero => simp [iterSquareDeg, iterSq]
  | succ p ih => simp only [iterSquareDeg, iterSq, Nat.cast_mul, ih]

private theorem iterSquareDeg_mono_p {d : ℕ} (hd : 1 ≤ d) {p₁ p₂ : ℕ} (hp : p₁ ≤ p₂) :
    iterSquareDeg d p₁ ≤ iterSquareDeg d p₂ := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hp
  induction k with
  | zero => simp
  | succ k ih =>
    calc iterSquareDeg d p₁ ≤ iterSquareDeg d (p₁ + k) := ih (by omega)
      _ ≤ iterSquareDeg d (p₁ + k) * iterSquareDeg d (p₁ + k) :=
        Nat.le_mul_of_pos_right _ (iterSquareDeg_pos (by omega) _)

/-- `mggNumSquarings` is antitone: larger ε → fewer squarings needed. -/
theorem mggNumSquarings_antitone {ε₁ ε₂ : ℚ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (h : ε₁ ≤ ε₂) :
    mggNumSquarings ε₂ hε₂ ≤ mggNumSquarings ε₁ hε₁ := by
  unfold mggNumSquarings
  exact Nat.find_min' _ ((mggNumSquarings_spec ε₁ hε₁).trans h)

/-- Cross-bound: `ε₂ * A(ε₁,β) ≤ ε₁ * A(ε₂,β)` when `ε₁ ≤ ε₂` and `β < 1`. -/
private theorem epsCondA_cross {ε₁ ε₂ β : ℚ} (hε₁ : 0 < ε₁) (h : ε₁ ≤ ε₂)
    (hβ : 0 ≤ β) (hβ1 : β < 1) :
    ε₂ * epsCondA ε₁ β ≤ ε₁ * epsCondA ε₂ β := by
  unfold epsCondA
  have key : ε₁ * (ε₂ ^ 2 - β ^ 2 * (1 - ε₂) ^ 2) - ε₂ * (ε₁ ^ 2 - β ^ 2 * (1 - ε₁) ^ 2) =
    (ε₂ - ε₁) * (ε₁ * ε₂ * (1 - β ^ 2) + β ^ 2) := by ring
  have h1 : 0 ≤ 1 - β ^ 2 := by nlinarith [sq_nonneg (1 - β)]
  nlinarith [sq_nonneg β, mul_nonneg (mul_nonneg hε₁.le (le_trans hε₁.le h)) h1]

/-- Lower bound: `A ≥ ε · β²` when `β < 1` and `β ≤ ε`. -/
private theorem epsCondA_ge_eps_mul_sq {ε β : ℚ} (hε : 0 < ε) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hβε : β ≤ ε) : ε * β ^ 2 ≤ epsCondA ε β := by
  unfold epsCondA
  suffices h : β ^ 2 * (1 - ε + ε ^ 2) ≤ ε ^ 2 by linarith
  by_cases hε1 : ε ≤ 1
  · have hβ2 : β ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg (ε - β)]
    calc β ^ 2 * (1 - ε + ε ^ 2) ≤ ε ^ 2 * 1 :=
          mul_le_mul hβ2 (by nlinarith) (by nlinarith [sq_nonneg (1 - ε)]) (by positivity)
      _ = ε ^ 2 := mul_one _
  · push_neg at hε1
    have h1 : β ^ 2 * (1 - ε) ≤ 0 := by nlinarith [sq_nonneg β]
    have h2 : β ^ 2 * ε ^ 2 ≤ ε ^ 2 := by
      nlinarith [sq_nonneg (1 - β), sq_nonneg ε, sq_nonneg (ε * (1 - β))]
    nlinarith

/-- Upper bound on `mggQ0`: `Q₀ · A ≤ 3ε + A` (from predecessor minimality of `Nat.find`). -/
private theorem mggQ0_mul_le (ε : ℚ) (hε : 0 < ε) :
    (mggQ0 ε hε : ℚ) * mggCondA ε hε ≤ 3 * ε + mggCondA ε hε := by
  set A := mggCondA ε hε with hA_def
  set hex := mggQ0_exists' ε A (mggCondA_pos ε hε)
  set F := Nat.find hex with hF_def
  have hA_pos := mggCondA_pos ε hε
  have hF_ge : 1 ≤ F := by
    by_contra h; push_neg at h
    have hF0 : F = 0 := by omega
    have h1 := Nat.find_spec hex
    rw [hF_def] at hF0; simp [hF0] at h1; linarith
  have hpred : ¬((F - 1 : ℕ) : ℚ) * A > 3 * ε :=
    Nat.find_min hex (by omega)
  push_neg at hpred
  have hmgg : mggQ0 ε hε = F := by show max 1 F = F; exact max_eq_right hF_ge
  rw [hmgg]
  have hF_eq : (F : ℚ) = ↑(F - 1 : ℕ) + 1 := by rw [Nat.cast_sub hF_ge]; ring
  rw [hF_eq]; nlinarith

/-- `21 ≤ 17·(d-1)·β²` where `d = iterSq 8 p`, `β² = iterSq(7921/10000, p)`.
    The key exponential bound ensuring `mggDepthFactor Q₀ ≤ 17·d`. -/
private theorem depth_factor_bound (p : ℕ) :
    (21 : ℚ) ≤ 17 * (iterSq 8 p - 1) * iterSq (7921 / 10000) p := by
  induction p with
  | zero => simp [iterSq]; norm_num
  | succ p ih =>
    simp only [iterSq]
    set d := iterSq (8 : ℚ) p
    set c := iterSq (7921 / 10000 : ℚ) p
    have hd : (8 : ℚ) ≤ d := iterSq_ge_base (by norm_num) p
    have hc_pos : (0 : ℚ) < c := by show 0 < iterSq _ p; rw [iterSq_eq_pow]; positivity
    have hdc : (63368 / 10000 : ℚ) ≤ d * c := by
      have h1 : iterSq (8 * (7921 / 10000) : ℚ) p = d * c := (iterSq_mul 8 (7921/10000) p).symm
      have h2 : (8 * (7921 / 10000) : ℚ) = 63368 / 10000 := by norm_num
      rw [h2] at h1; rw [← h1]; exact iterSq_ge_base (by norm_num) p
    have h_dc1 : (1 : ℚ) ≤ (d + 1) * c := by nlinarith
    have key : 17 * (d * d - 1) * (c * c) = 17 * (d - 1) * c * ((d + 1) * c) := by ring
    nlinarith

/-- `mggDepthFactor (mggQ0 ε hε) ≤ 17 · iterSquareDeg 8 (mggNumSquarings ε hε)`.
    Chains: `Q₀·A ≤ 3ε+A` → `A ≥ ε·β²` → `21 ≤ 17·(d-1)·β²` → divide by `A > 0`. -/
private theorem mggQ0_depth_bound (ε : ℚ) (hε : 0 < ε) :
    mggDepthFactor (mggQ0 ε hε) ≤ 17 * iterSquareDeg 8 (mggNumSquarings ε hε) := by
  set p := mggNumSquarings ε hε
  set A := mggCondA ε hε
  set Q := mggQ0 ε hε
  set d := iterSquareDeg 8 p
  set β := iterSq mggBeta p
  have hA_pos := mggCondA_pos ε hε
  have hβ_nn : 0 ≤ β := by
    show 0 ≤ iterSq mggBeta p; rw [iterSq_eq_pow]; exact pow_nonneg mggBeta_nn _
  have hβ1 : β < 1 := by
    show iterSq mggBeta p < 1; rw [iterSq_eq_pow]
    exact pow_lt_one₀ mggBeta_nn mggBeta_lt_one (by positivity)
  have hβε : β ≤ ε := mggNumSquarings_spec ε hε
  have hA_lb : ε * β ^ 2 ≤ A := epsCondA_ge_eps_mul_sq hε hβ_nn hβ1 hβε
  have hQ_ub := mggQ0_mul_le ε hε
  -- (7Q+10) * A ≤ 21ε + 17A
  have hQA : (7 * Q + 10 : ℚ) * A ≤ 21 * ε + 17 * A := by
    show (7 * (mggQ0 ε hε : ℚ) + 10) * A ≤ _; nlinarith
  -- β² = iterSq(7921/10000, p)
  have hβ2_eq : β * β = iterSq (7921 / 10000 : ℚ) p := by
    show iterSq mggBeta p * iterSq mggBeta p = _
    rw [iterSq_mul]; congr 1; unfold mggBeta; norm_num
  -- (d : ℚ) = iterSq 8 p
  have hd_eq : (d : ℚ) = iterSq 8 p := iterSquareDeg_cast 8 p
  -- 21 ≤ 17*(d-1)*β²
  have h_dfb := depth_factor_bound p
  -- Chain: 21ε ≤ 17*(d-1)*ε*β² ≤ (17d-17)*A
  have hd_pos : (0 : ℚ) < d := by exact_mod_cast iterSquareDeg_pos (by norm_num : 0 < 8) p
  have h_21ε : 21 * ε ≤ (17 * (d : ℚ) - 17) * A := by
    have h1 : (21 : ℚ) ≤ 17 * ((d : ℚ) - 1) * (β * β) := by rw [hβ2_eq, hd_eq]; exact h_dfb
    have h2 : 21 * ε ≤ 17 * ((d : ℚ) - 1) * (ε * β ^ 2) := by nlinarith
    have hfac : (0 : ℚ) ≤ 17 * ((d : ℚ) - 1) := by nlinarith
    calc 21 * ε ≤ 17 * ((d : ℚ) - 1) * (ε * β ^ 2) := h2
      _ ≤ 17 * ((d : ℚ) - 1) * A := by nlinarith
      _ = (17 * (d : ℚ) - 17) * A := by ring
  -- (7Q+10) * A ≤ 17*d*A
  have hQdA : (7 * Q + 10 : ℚ) * A ≤ 17 * (d : ℚ) * A := by nlinarith
  -- Divide by A > 0
  have h_final : (7 * Q + 10 : ℚ) ≤ 17 * (d : ℚ) := le_of_mul_le_mul_right hQdA hA_pos
  show 7 * Q + 10 ≤ 17 * d; exact_mod_cast h_final

/-- Halver depth is antitone in ε: larger error tolerance → fewer squarings → less depth.

    **Case `p₁ = p₂`** (same squarings): same degree `d`, and `Q₂ ≤ Q₁` via `epsCondA_cross`
    (larger ε needs smaller Q₀ for the algebraic condition), so `d·F(Q₂) ≤ d·F(Q₁)`.

    **Case `p₂ < p₁`** (fewer squarings): `F(Q₂) ≤ 17·d₂` (from `depth_factor_bound`),
    so `halverDepth ε₂ ≤ 17·d₂² ≤ 17·d₁ ≤ halverDepth ε₁`. -/
theorem halverDepth_antitone {ε₁ ε₂ : ℚ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (h : ε₁ ≤ ε₂) :
    halverDepth ε₂ hε₂ ≤ halverDepth ε₁ hε₁ := by
  have hp : mggNumSquarings ε₂ hε₂ ≤ mggNumSquarings ε₁ hε₁ :=
    mggNumSquarings_antitone hε₁ hε₂ h
  unfold halverDepth
  by_cases heq : mggNumSquarings ε₁ hε₁ = mggNumSquarings ε₂ hε₂
  · -- Case 1: same squarings → same d, show Q₂ ≤ Q₁
    rw [← heq]; apply Nat.mul_le_mul_left
    unfold mggDepthFactor
    suffices mggQ0 ε₂ hε₂ ≤ mggQ0 ε₁ hε₁ by omega
    -- mggQ0 ε₁ satisfies the ε₂ predicate (by epsCondA_cross), so find₂ ≤ mggQ0 ε₁
    unfold mggQ0
    apply max_le (le_max_left 1 _)
    apply Nat.find_min'
    -- Goal: (max 1 (Nat.find ...)) * mggCondA ε₂ hε₂ > 3 * ε₂
    -- i.e., mggQ0 ε₁ hε₁ * A₂ > 3ε₂
    set β := iterSq mggBeta (mggNumSquarings ε₁ hε₁)
    have hβ_nn : 0 ≤ β := by
      show 0 ≤ iterSq mggBeta _; rw [iterSq_eq_pow]; exact pow_nonneg mggBeta_nn _
    have hβ1 : β < 1 := by
      show iterSq mggBeta _ < 1; rw [iterSq_eq_pow]
      exact pow_lt_one₀ mggBeta_nn mggBeta_lt_one (by positivity)
    -- Both A values use the same β since p₁ = p₂
    have hA₁ : mggCondA ε₁ hε₁ = epsCondA ε₁ β := rfl
    have hA₂ : mggCondA ε₂ hε₂ = epsCondA ε₂ β := by
      show epsCondA ε₂ (iterSq mggBeta (mggNumSquarings ε₂ hε₂)) = epsCondA ε₂ β
      rw [← heq]
    have hspec := mggQ0_spec ε₁ hε₁  -- Q₁ * A₁ > 3ε₁
    rw [hA₁] at hspec; rw [hA₂]
    have hcross := epsCondA_cross hε₁ h hβ_nn hβ1
    -- Q₁ * A₂ * ε₁ ≥ Q₁ * A₁ * ε₂ > 3ε₁ * ε₂ > 0, so Q₁ * A₂ > 3ε₂
    -- The goal has `max 1 (Nat.find ...)` which is mggQ0 ε₁ hε₁
    change (mggQ0 ε₁ hε₁ : ℚ) * epsCondA ε₂ β > 3 * ε₂
    nlinarith [mul_pos (show (0 : ℚ) < mggQ0 ε₁ hε₁ from by exact_mod_cast mggQ0_pos ε₁ hε₁)
      (epsCondA_pos ε₁ β hε₁ hβ_nn (mggNumSquarings_spec ε₁ hε₁) hβ1)]
  · -- Case 2: p₂ < p₁ → use mggQ0_depth_bound
    have hlt : mggNumSquarings ε₂ hε₂ + 1 ≤ mggNumSquarings ε₁ hε₁ := by omega
    have hdfb := mggQ0_depth_bound ε₂ hε₂
    calc iterSquareDeg 8 (mggNumSquarings ε₂ hε₂) * mggDepthFactor (mggQ0 ε₂ hε₂)
        ≤ iterSquareDeg 8 (mggNumSquarings ε₂ hε₂) * (17 * iterSquareDeg 8 (mggNumSquarings ε₂ hε₂)) :=
          Nat.mul_le_mul_left _ hdfb
      _ = 17 * iterSquareDeg 8 (mggNumSquarings ε₂ hε₂ + 1) := by
          simp [iterSquareDeg]; ring
      _ ≤ 17 * iterSquareDeg 8 (mggNumSquarings ε₁ hε₁) :=
          Nat.mul_le_mul_left _ (iterSquareDeg_mono_p (by norm_num) hlt)
      _ ≤ iterSquareDeg 8 (mggNumSquarings ε₁ hε₁) * mggDepthFactor (mggQ0 ε₁ hε₁) := by
          unfold mggDepthFactor; nlinarith [mggQ0_pos ε₁ hε₁]

end
