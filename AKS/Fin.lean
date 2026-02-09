/-
  # Fin Arithmetic Helpers

  Reusable `Fin` encode/decode lemmas for product-type indexing.
  Used by graph constructions in `ZigZag.lean` that represent
  `Fin n × Fin d` as `Fin (n * d)` via `j * d + i` encoding.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

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
