module
/-
  # ℚ/ℝ Floor Bridge

  Lemmas bridging `⌊·⌋₊` between `ℚ` and `ℝ`.
-/

public import Mathlib.Data.Real.Archimedean

@[expose] public section

lemma floor_rat_real_eq (q : ℚ) (hq : 0 ≤ q) : ⌊(q : ℝ)⌋₊ = ⌊q⌋₊ := by
  have h1 : (⌊q⌋₊ : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.floor_le hq
  have h2 : (q : ℝ) < (⌊q⌋₊ : ℝ) + 1 := by exact_mod_cast Nat.lt_floor_add_one q
  exact (Nat.floor_eq_iff (by exact_mod_cast hq : (0 : ℝ) ≤ ↑q)).mpr ⟨h1, h2⟩

lemma floor_rat_real_mul_nat (γ : ℚ) (n : ℕ) (hγ : 0 ≤ γ) :
    ⌊(γ : ℝ) * ↑n⌋₊ = ⌊(γ : ℚ) * ↑n⌋₊ := by
  rw [show (γ : ℝ) * ↑n = ↑((γ : ℚ) * ↑n) from by push_cast; ring]
  exact floor_rat_real_eq _ (mul_nonneg hγ (Nat.cast_nonneg _))

end
