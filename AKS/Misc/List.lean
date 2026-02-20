/-
  # List helpers

  Reusable lemmas for `List.range'` decomposition.
-/

/-- Split `List.range' 0 (n+1)` into `List.range' 0 n ++ [n]`. -/
theorem range'_zero_succ (n : Nat) :
    List.range' 0 (n + 1) = List.range' 0 n ++ [n] := by
  rw [← List.range'_append (m := n) (n := 1)]
  simp [List.range'_one]
