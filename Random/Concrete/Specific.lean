module
/-
  # Concrete Spectral Gap Conditions for `Random65536.graph`

  Specializes the RVW fixed-point iteration to the concrete base expander
  `Random65536.graph` with spectral gap β = 17/32 and contraction bound
  c = 7/8. These lemmas are used by `Seiferas.lean` to instantiate
  `seiferasSepFamily_isSepFamily`.
-/

public import Random.Concrete.Random65536
public import AKS.ZigZag.RVWBound

@[expose] public section


/-- The spectral gap β = 17/32 from `Random65536.gap` (17/(2·16) = 17/32). -/
lemma random65536_β_le : spectralGap Random65536.graph ≤ 17 / 32 :=
  Random65536.gap.trans (by norm_num)

/-- β = 17/32 ≤ 1. -/
lemma random65536_β_le_one : (17 / 32 : ℝ) ≤ 1 := by norm_num

/-- Base case: β² = (17/32)² = 289/1024 ≤ 7/8 = 896/1024. -/
lemma random65536_hbase : (17 / 32 : ℝ) ^ 2 ≤ 7 / 8 := by norm_num

/-- c = 7/8 ≤ 1. -/
lemma random65536_c_le_one : (7 / 8 : ℝ) ≤ 1 := by norm_num

/-- Iteration: `rvwBound(c², β) ≤ c` with c = 7/8, β = 17/32.
    Proved via the polynomial condition `(1-β²)c³ + β² ≤ c²`. -/
lemma random65536_hiter :
    rvwBound ((7 / 8 : ℝ) ^ 2) (17 / 32) ≤ 7 / 8 :=
  rvwBound_le_of_poly (by norm_num) (by norm_num) (by positivity) (by norm_num) (by norm_num)
    (by norm_num)

/-- (7/8)^64 ≤ 1/1000, proved via 6-step squaring chain.
    Each step squares the previous bound and rounds up to a manageable fraction. -/
lemma random65536_c_pow64_le : (7 / 8 : ℝ) ^ 64 ≤ 1 / 1000 := by
  calc (7 / 8 : ℝ) ^ 64
      = ((7 / 8 : ℝ) ^ 2) ^ 32 := by rw [← pow_mul]
    _ ≤ (766 / 1000 : ℝ) ^ 32 :=
        pow_le_pow_left₀ (by positivity) (by norm_num) 32
    _ = ((766 / 1000 : ℝ) ^ 2) ^ 16 := by rw [← pow_mul]
    _ ≤ (587 / 1000 : ℝ) ^ 16 :=
        pow_le_pow_left₀ (by positivity) (by norm_num) 16
    _ = ((587 / 1000 : ℝ) ^ 2) ^ 8 := by rw [← pow_mul]
    _ ≤ (345 / 1000 : ℝ) ^ 8 :=
        pow_le_pow_left₀ (by positivity) (by norm_num) 8
    _ = ((345 / 1000 : ℝ) ^ 2) ^ 4 := by rw [← pow_mul]
    _ ≤ (120 / 1000 : ℝ) ^ 4 :=
        pow_le_pow_left₀ (by positivity) (by norm_num) 4
    _ = ((120 / 1000 : ℝ) ^ 2) ^ 2 := by rw [← pow_mul]
    _ ≤ (15 / 1000 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by norm_num) 2
    _ ≤ 1 / 1000 := by norm_num

end
