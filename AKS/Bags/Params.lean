module
/-
  # Seiferas Parameters and Capacity

  Parameter structure for the Seiferas (2009) sorting network construction,
  concrete parameter values, capacity/fringe definitions, and `numStages`.

  Key definitions:
  - `Params`: parameter constraints (γ, ε, ν, A)
  - `seiferasParams`: concrete satisfying values
  - `capacity`: parametric bag capacity `2^k · ν^t · A^l`
  - `effectiveGamma`: effective separator fraction per bag
  - `fringe`: fringe size at a given level
  - `numStages`: smallest `t` achieving convergence at level `k - 2`
  - `Params.stagesFactor`: constant bounding `numStages / k`
-/

public import AKS.Sort.Defs

@[expose] public section


/-! **Seiferas Parameters** -/

/-- Seiferas (2009) parameters (Section 5).

    The parameter constraints encode the conditions from Seiferas p.6:
    - `h2εA`: convergence of geometric series `∑(2εA)^{2i}`
    - `hC3`: capacity bound for Clause 3 (`bagCard ≤ capacity`)
    - `hC4_gt1`: stranger decay for j ≥ 2
    - `hC4_eq1`: master constraint for j = 1

    Concrete satisfying values: `A = 10, γ = 1/100, ε = 1/100, ν = 13/20`. -/
structure Params where
  /-- Separator fraction -/
  γ : ℚ
  /-- Separator error -/
  ε : ℚ
  /-- Capacity decay per stage -/
  ν : ℚ
  /-- Capacity growth per level -/
  A : ℚ
  hγ_pos : 0 < γ
  hγ_half : γ ≤ 1 / 2
  hε_pos : 0 < ε
  hε_lt : ε < 1
  hA : 1 < A
  hν_pos : 0 < ν
  hν_lt : ν < 1
  /-- Convergence: `(2εA)² < 1` -/
  h2εA : (2 * ε * A) ^ 2 < 1
  /-- Clause 3 capacity bound -/
  hC3 : ν ≥ 4 * γ * A + 5 / (2 * A)
  /-- j ≥ 2 stranger decay: `2Aε + 1/A ≤ ν` -/
  hC4_gt1 : 2 * A * ε + 1 / A ≤ ν
  /-- j = 1 master constraint.
      The first four terms match Seiferas (2009) §5. The two extra terms
      (`γ / A` and `1 / (8A³-2A)`) are not in the paper: `γ / A` absorbs
      D-strangers (IH on parent bag at distance 1) and `1 / (8A³-2A)`
      absorbs a ½ parity correction from the conservation split at the
      parent level (geometric series over inactive sub-bag capacities). -/
  hC4_eq1 : 2 * γ * ε * A
           + ε * γ / A + ε / (2 * A)
           + 2 * γ * ε * A / (1 - (2 * ε * A) ^ 2)
           + 1 / (8 * A ^ 3 - 2 * A)
           + γ / A
           + 1 / (8 * A ^ 3 - 2 * A)
           ≤ γ * ν
  /-- Capacity bound: ensures `6A/(4+2γ) ≤ 2^k` for `k ≥ 10`.
      The constant 1024 = 2^10. -/
  hC_bound : 6 * A / (4 + 2 * γ) ≤ 1024
  /-- Ancestor capacity bound: `γ · A² ≥ 1`.
      Used to show ancestor bags are empty once convergence holds at the
      finish level. Not imposed in the paper — Seiferas uses `1/λ < A²`
      (strict), and the paper's parameters `λ = 1/99, A = 10` satisfy
      `1/λ = 99 < 100 = A²`. Our `γ = 1/100` gives equality; the strict
      inequality from `hconv` propagates through the capacity chain.
      This constraint may be removable if the ancestor argument can use
      only `hconv` directly. -/
  hA2_le : 1 ≤ γ * A ^ 2

/-- Concrete satisfying values from Seiferas (2009), p.6:
    `γ = 1/100, ε = 1/100, ν = 13/20, A = 10`. -/
def seiferasParams : Params where
  γ := 1 / 100
  ε := 1 / 100
  ν := 13 / 20
  A := 10
  hγ_pos := by decide +kernel
  hγ_half := by decide +kernel
  hε_pos := by decide +kernel
  hε_lt := by decide +kernel
  hA := by decide +kernel
  hν_pos := by decide +kernel
  hν_lt := by decide +kernel
  h2εA := by decide +kernel
  hC3 := by decide +kernel
  hC4_gt1 := by decide +kernel
  hC4_eq1 := by decide +kernel
  hC_bound := by decide +kernel
  hA2_le := by decide +kernel

/-! **Capacity** -/

/-- Parametric capacity of a bag (Seiferas 2009, Section 5).
    `capacity p k t l = 2^k · ν^t · A^l`. -/
def capacity (p : Params) (k t l : ℕ) : ℚ :=
  ↑(2 ^ k) * p.ν ^ t * p.A ^ l

/-- `capacity` is strictly positive. -/
theorem capacity_pos (p : Params) (k t l : ℕ) : 0 < capacity p k t l := by
  unfold capacity
  apply mul_pos (mul_pos _ _) _
  · exact_mod_cast Nat.pos_of_ne_zero (by positivity : 2 ^ k ≠ 0)
  · exact pow_pos p.hν_pos t
  · exact pow_pos (by linarith [p.hA]) l

/-! **Effective Gamma** -/

/-- Effective separator fraction for a bag with `C` wires and capacity `cap`.
    When `C > 0`, `γₑ = γ * cap / C ≥ γ` (since `C ≤ cap` by `bagCard_le_capacity`).
    The product `γₑ * C = γ * cap` exactly, resolving the capacity/bagCard boundary mismatch
    in separator filtering (Seiferas 2009, p.7). -/
def effectiveGamma (γ cap : ℚ) (C : ℕ) : ℚ :=
  if C = 0 then γ else γ * cap / ↑C

theorem effectiveGamma_pos {γ cap : ℚ} (hγ : 0 < γ) (hcap : 0 < cap) (C : ℕ) :
    0 < effectiveGamma γ cap C := by
  unfold effectiveGamma; split
  · exact hγ
  · next h => exact div_pos (mul_pos hγ hcap) (Nat.cast_pos.mpr (by omega))

/-- Key property: `γₑ * C = γ * cap` when `C > 0`. -/
theorem effectiveGamma_mul (γ cap : ℚ) {C : ℕ} (hC : C ≠ 0) :
    effectiveGamma γ cap C * ↑C = γ * cap := by
  unfold effectiveGamma; rw [if_neg hC]; field_simp

/-! **Fringe** -/

/-- Fringe size at a given level (Seiferas 2009, Section 3).
    Independent of horizontal bag index `x`.
    - Root (`level = 0`): `f = 0` — no fringe
    - Leaf (`k ≤ level + 1`): `f = s / 2` — everything to parent
    - Interior: `f = ⌊γ · cap⌋₊` where `cap = capacity p k t level` -/
def fringe (p : Params) (k t level : ℕ) (s : ℕ) : ℕ :=
  if level = 0 then 0
  else if k ≤ level + 1 then s / 2
  else ⌊p.γ * capacity p k t level⌋₊

/-! **Convergence and numStages** -/

/-- Convergence: capacity at level `k - 2` eventually drops below `1/γ`. Since `ν < 1`,
    capacity `= 2^k · ν^t · A^(k-2)` decays geometrically to 0. -/
theorem convergence_exists (p : Params) (k : ℕ) :
    ∃ t, p.γ * capacity p k t (k - 2) < 1 := by
  unfold capacity
  have hA_pos : (0:ℚ) < p.A := by linarith [p.hA]
  have h2k : (0:ℚ) < (2 ^ k : ℕ) := Nat.cast_pos.mpr (by positivity)
  set c := p.γ * (↑(2 ^ k) * p.A ^ (k - 2))
  have hc_pos : (0:ℚ) < c := mul_pos p.hγ_pos (mul_pos h2k (pow_pos hA_pos _))
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hc_pos) p.hν_lt
  refine ⟨n, ?_⟩
  show p.γ * (↑(2 ^ k) * p.ν ^ n * p.A ^ (k - 2)) < 1
  rw [show p.γ * (↑(2 ^ k) * p.ν ^ n * p.A ^ (k - 2)) = c * p.ν ^ n from by ring]
  calc c * p.ν ^ n < c * c⁻¹ := mul_lt_mul_of_pos_left hn hc_pos
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hc_pos)

/-- The number of separator stages to run before finishing.

    The smallest `t` such that `γ · capacity(t, k-2) < 1`, i.e.,
    convergence at the convergence level. Since `ν < 1`, capacity decays
    geometrically and convergence is guaranteed (no fuel needed). -/
def numStages (p : Params) (k : ℕ) : ℕ :=
  Nat.find (convergence_exists p k)

/-! **Capacity base condition** -/

/-- `hC_bound` + `10 ≤ k` gives `6A/(4+2γ) ≤ 2^k`. -/
theorem Params.hbase (p : Params) {k : ℕ} (hk : 10 ≤ k) :
    6 * p.A / (4 + 2 * p.γ) ≤ ↑(2 ^ k) :=
  p.hC_bound.trans (by
    have : (1024 : ℚ) = ↑(2 ^ 10 : ℕ) := by norm_num
    rw [this]
    exact_mod_cast Nat.pow_le_pow_right (by omega) hk)

/-! **numStages properties** -/

/-- Convergence at the convergence level `k - 2`. -/
theorem numStages_hconv_cl (p : Params) (k : ℕ) :
    p.γ * capacity p k (numStages p k) (k - 2) < 1 :=
  Nat.find_spec (convergence_exists p k)

/-- Convergence at the finish level `k - 3` (follows from convergence at `k - 2`
    since capacity is monotone in level). -/
theorem numStages_hconv (p : Params) (k : ℕ) :
    p.γ * capacity p k (numStages p k) (k - 3) < 1 := by
  have h := numStages_hconv_cl p k
  have hle : k - 3 ≤ k - 2 := by omega
  have hcap_le : capacity p k (numStages p k) (k - 3) ≤
      capacity p k (numStages p k) (k - 2) := by
    unfold capacity
    have h2k : (0:ℚ) ≤ (2:ℚ) ^ k * p.ν ^ numStages p k := by
      exact mul_nonneg (by positivity) (pow_nonneg p.hν_pos.le _)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ p.hA.le hle) h2k
  calc p.γ * capacity p k (numStages p k) (k - 3)
      ≤ p.γ * capacity p k (numStages p k) (k - 2) :=
        mul_le_mul_of_nonneg_left hcap_le p.hγ_pos.le
    _ < 1 := h

/-- Pre-convergence: for `t < numStages`, capacity at the convergence level
    hasn't yet dropped below `1/γ`. -/
theorem numStages_pre (p : Params) (k : ℕ) (t : ℕ) (ht : t < numStages p k) :
    1 ≤ p.γ * capacity p k t (k - 2) :=
  not_lt.mp (Nat.find_min (convergence_exists p k) ht)

/-- For `t ≤ numStages`, capacity at `numStages` ≤ capacity at `t`.
    Since `ν < 1`, capacity decreases with stage number. -/
theorem numStages_cap_mono (p : Params) (k t l : ℕ)
    (ht : t ≤ numStages p k) :
    capacity p k (numStages p k) l ≤ capacity p k t l := by
  unfold capacity
  have hν_le := pow_le_pow_of_le_one p.hν_pos.le p.hν_lt.le ht
  have hAl : (0:ℚ) ≤ p.A ^ l := pow_nonneg (by linarith [p.hA]) _
  linarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hν_le hAl)
              (show (0:ℚ) ≤ (2:ℚ) ^ k by positivity),
            show (2:ℚ)^k * p.ν ^ numStages p k * p.A^l =
              (2:ℚ)^k * (p.ν ^ numStages p k * p.A^l) from by ring,
            show (2:ℚ)^k * p.ν^t * p.A^l = (2:ℚ)^k * (p.ν^t * p.A^l) from by ring]

/-- `numStages ≥ 1` for `k ≥ 10`: initial capacity is too large for convergence at `t = 0`. -/
theorem numStages_pos (p : Params) (k : ℕ) (hk : 10 ≤ k) : 0 < numStages p k := by
  by_contra h; simp only [not_lt, Nat.le_zero] at h
  have hconv : p.γ * capacity p k 0 (k - 2) < 1 := by
    have := numStages_hconv_cl p k; rwa [h] at this
  unfold capacity at hconv; simp only [pow_zero, mul_one] at hconv
  rw [show k - 2 = 2 + (k - 4) from by omega, pow_add] at hconv
  have h1 := p.hA2_le
  have h3 : (1:ℚ) ≤ p.A ^ (k - 4) := one_le_pow₀ (by linarith [p.hA] : (1:ℚ) ≤ p.A)
  have h2k : (1:ℚ) ≤ (2:ℚ) ^ k := one_le_pow₀ (by norm_num : (1:ℚ) ≤ 2)
  linarith [show p.γ * ((2:ℚ) ^ k * (p.A ^ 2 * p.A ^ (k - 4))) =
    (p.γ * p.A ^ 2) * ((2:ℚ) ^ k * p.A ^ (k - 4)) from by ring,
    one_le_mul_of_one_le_of_one_le h1 (one_le_mul_of_one_le_of_one_le h2k h3)]

/-! **Stages-per-level factor** -/

/-- There exists `c` such that `ν^c · (2 * A) < 1`. Since `ν < 1` and `A > 0`,
    `ν^c → 0`, so eventually `ν^c < 1/(2A)`. -/
theorem Params.exists_stagesFactor (p : Params) :
    ∃ c : ℕ, p.ν ^ c * (2 * p.A) < 1 := by
  have hA_pos : (0:ℚ) < 2 * p.A := by linarith [p.hA]
  obtain ⟨c, hc⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hA_pos) p.hν_lt
  refine ⟨c, ?_⟩
  rw [inv_eq_one_div] at hc
  calc p.ν ^ c * (2 * p.A) < 1 / (2 * p.A) * (2 * p.A) :=
      mul_lt_mul_of_pos_right hc hA_pos
    _ = 1 := div_mul_cancel₀ 1 (ne_of_gt hA_pos)

/-- The smallest `c` such that `ν^c · 2A < 1`. Controls the ratio
    `numStages / k`: we have `numStages p k ≤ stagesFactor * k`. -/
def Params.stagesFactor (p : Params) : ℕ :=
  Nat.find p.exists_stagesFactor

theorem Params.stagesFactor_spec (p : Params) :
    p.ν ^ p.stagesFactor * (2 * p.A) < 1 :=
  Nat.find_spec p.exists_stagesFactor

end
