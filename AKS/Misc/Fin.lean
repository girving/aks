/-
  # Fin Arithmetic Helpers

  Reusable `Fin` encode/decode lemmas for product-type indexing.
  Used by graph constructions in `Graph/Regular.lean` and `ZigZag.lean` that represent
  `Fin n × Fin d` as `Fin (n * d)` via `j * d + i` encoding.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring

/-- Encoding a pair `(j, i) : Fin n × Fin d` as `j * d + i` stays in bounds. -/
theorem Fin.pair_lt {n d : ℕ} (j : Fin n) (i : Fin d) :
    j.val * d + i.val < n * d :=
  calc j.val * d + i.val
      < j.val * d + d := Nat.add_lt_add_left i.isLt _
    _ = (j.val + 1) * d := by ring
    _ ≤ n * d := Nat.mul_le_mul_right d (Nat.succ_le_of_lt j.isLt)

/-- Decode-encode: dividing `x * d + y` by `d` gives `x`. -/
theorem fin_encode_fst {n d : ℕ} (x : Fin n) (y : Fin d)
    (h : (x.val * d + y.val) / d < n) :
    (⟨(x.val * d + y.val) / d, h⟩ : Fin n) = x := by
  apply Fin.ext
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; exact absurd y.isLt (by omega))
  show (x.val * d + y.val) / d = x.val
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt y.isLt]; omega

/-- Decode-encode: `x * d + y` mod `d` gives `y`. -/
theorem fin_encode_snd {n d : ℕ} (x : Fin n) (y : Fin d)
    (h : (x.val * d + y.val) % d < d) :
    (⟨(x.val * d + y.val) % d, h⟩ : Fin d) = y := by
  apply Fin.ext
  show (x.val * d + y.val) % d = y.val
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; exact absurd y.isLt (by omega))
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt y.isLt]

/-- Encode-decode: `(ij / d) * d + ij % d = ij`. -/
theorem fin_div_add_mod {n d : ℕ} (ij : Fin (n * d))
    (h : (ij.val / d) * d + ij.val % d < n * d) :
    (⟨(ij.val / d) * d + ij.val % d, h⟩ : Fin (n * d)) = ij := by
  apply Fin.ext
  show (ij.val / d) * d + ij.val % d = ij.val
  rw [Nat.mul_comm]; exact Nat.div_add_mod ij.val d


/-! **Order** -/

/-- Strict inequality from `≤` and `≠` for `Fin`. -/
lemma Fin.lt_of_le_of_ne {n : ℕ} {a b : Fin n} (h1 : a ≤ b) (h2 : a ≠ b) : a < b := by
  by_contra h
  push_neg at h
  exact h2 (Fin.le_antisymm h1 h)


/-! **Rank** -/

/-- The rank of an element: the number of strictly smaller elements.
    For `Fin n`, this equals the element's value. -/
def rank {α : Type*} [Fintype α] [LinearOrder α] (a : α) : ℕ :=
  (Finset.univ.filter (· < a)).card

/-- The rank of a `Fin n` element equals its value. -/
lemma rank_fin_val {n : ℕ} (i : Fin n) : rank i = i.val := by
  unfold rank
  have : Finset.univ.filter (· < i) = Finset.Iio i := by
    ext x; simp [Finset.mem_Iio]
  rw [this, Fin.card_Iio]

/-- The rank of a `Fin n` element in the order dual equals `n - 1 - i.val`. -/
lemma rank_fin_od_val {n : ℕ} (i : Fin n) :
    rank (α := (Fin n)ᵒᵈ) (OrderDual.toDual i) = n - 1 - i.val := by
  unfold rank
  -- In (Fin n)ᵒᵈ, b <_od a means a <_orig b, i.e., i < b
  have hcard : (Finset.univ.filter (· < OrderDual.toDual i) : Finset (Fin n)ᵒᵈ).card =
    (Finset.univ.filter (fun b : Fin n ↦ i < b)).card := by
    apply Finset.card_nbij' (fun a ↦ OrderDual.ofDual a) (fun b ↦ OrderDual.toDual b)
    · intro a ha
      rw [Finset.mem_coe, Finset.mem_filter] at ha ⊢
      exact ⟨Finset.mem_univ _, ha.2⟩
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨Finset.mem_univ _, hb.2⟩
    · intro _ _; rfl
    · intro _ _; rfl
  rw [hcard]
  have : Finset.univ.filter (fun b : Fin n ↦ i < b) = Finset.Ioi i := by
    ext x; simp [Finset.mem_Ioi]
  rw [this, Fin.card_Ioi]

/-- `rank` on `(Fin n)ᵒᵈ` in terms of `.val`. Matches goals after unfolding
    `FinalNearsorted` where the variable is already of type `(Fin n)ᵒᵈ`. -/
@[simp] lemma rank_fin_od {n : ℕ} (a : (Fin n)ᵒᵈ) :
    rank a = n - 1 - a.val :=
  rank_fin_od_val (OrderDual.ofDual a)
