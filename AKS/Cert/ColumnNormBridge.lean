/-
  # Column Norm Bridge: Imperative → Pure Equality

  Proves that `checkColumnNormBound` (imperative, fast) computes exactly the
  same result as `checkColumnNormBoundPure` (pure recursive, provable).

  The key insight: both compute `epsMax` (max off-diagonal |P[i,j]|) and
  `minDiag` (min diagonal P[j,j]) then feed them to `checkPerRow`. The
  imperative version uses pre-decoded arrays and for-loops; the pure version
  uses recursive functions. Under the involution hypothesis (which is checked
  by `checkCertificateSlow`), both compute exactly the same values.

  Imports `CertCheck` (definitions), `AKS/Misc/ForLoop` (loop characterization),
  and `Mathlib.Tactic` for `set`, `ring`, etc.
-/

import CertCheck
import AKS.Misc.ForLoop
import Mathlib.Tactic.Set

universe u
variable {β : Type u}

/-! **Generic loop helpers** -/

/-- Array-builder fold preserves size. -/
theorem fold_set_size (g : Nat → Int) (n m : Nat) (hm : m ≤ n) :
    (Nat.fold m (fun v _ arr => arr.set! v (g v)) (Array.replicate n (0:Int))).size = n := by
  induction m with
  | zero => simp [Nat.fold_zero, Array.size_replicate]
  | succ k ih =>
    rw [Nat.fold_succ, Array.set!, Array.size_setIfInBounds]
    exact ih (by omega)

/-- Array-builder fold: `getElem?` characterization. -/
theorem fold_set_getElem? (g : Nat → Int) (n m : Nat) (hm : m ≤ n) (v : Nat) :
    (Nat.fold m (fun i _ arr => arr.set! i (g i)) (Array.replicate n (0:Int)))[v]? =
    if v < n then some (if v < m then g v else 0) else none := by
  induction m with
  | zero =>
    simp [Nat.fold_zero]
    by_cases hv : v < n
    · rw [if_pos hv, Array.getElem?_replicate, if_pos hv]
    · rw [if_neg hv, Array.getElem?_replicate, if_neg hv]
  | succ k ih =>
    rw [Nat.fold_succ, Array.set!, Array.getElem?_setIfInBounds]
    by_cases hkv : k = v
    · subst hkv
      rw [if_pos rfl, if_pos (by rw [fold_set_size g n k (by omega)]; omega), if_pos (by omega)]
      simp
    · rw [if_neg hkv, ih (by omega)]
      by_cases hv : v < n
      · rw [if_pos hv, if_pos hv]; congr 1
        by_cases hvk : v < k
        · rw [if_pos hvk, if_pos (by omega)]
        · rw [if_neg hvk, if_neg (by omega)]
      · rw [if_neg hv, if_neg hv]

/-- `getD` from `getElem? = some`. -/
private theorem getD_of_getElem?_some {arr : Array Int} {i : Nat} {v : Int}
    (h : arr[i]? = some v) : arr.getD i 0 = v := by
  show (if _ : i < arr.size then arr[i] else 0) = v
  split
  case isTrue hi =>
    have : arr[i]? = some arr[i] := by simp [hi]
    rw [this] at h; exact Option.some.inj h
  case isFalse hni =>
    have : arr[i]? = none := by simp [hni]
    rw [this] at h; cases h

/-- `getD` of array-builder fold at set indices. -/
theorem fold_set_getD (g : Nat → Int) (n m : Nat) (hm : m ≤ n) (k : Nat) (hk : k < m) :
    (Nat.fold m (fun i _ arr => arr.set! i (g i)) (Array.replicate n (0:Int))).getD k 0 = g k :=
  getD_of_getElem?_some (by rw [fold_set_getElem? g n m hm]; rw [if_pos (by omega), if_pos hk])

/-- `sumTo g n = Nat.fold n (fun p _ acc => acc + g p) 0`. -/
theorem sumTo_eq_fold (g : Nat → Int) (n : Nat) :
    sumTo g n = Nat.fold n (fun p _ acc => acc + g p) 0 := by
  induction n with
  | zero => simp [sumTo, Nat.fold_zero]
  | succ n ih => simp only [sumTo, Nat.fold_succ]; rw [ih]

/-- Congruence for fold-based sums. -/
theorem fold_sum_congr {d : Nat} (g₁ g₂ : Nat → Int)
    (h : ∀ p, p < d → g₁ p = g₂ p) :
    Nat.fold d (fun p _ acc => acc + g₁ p) (0 : Int) =
    Nat.fold d (fun p _ acc => acc + g₂ p) (0 : Int) := by
  suffices ∀ init : Int, Nat.fold d (fun p _ acc => acc + g₁ p) init =
    Nat.fold d (fun p _ acc => acc + g₂ p) init from this 0
  intro init
  induction d generalizing init with
  | zero => simp [Nat.fold_zero]
  | succ k ih =>
    simp only [Nat.fold_succ]
    rw [ih (fun p hp => h p (by omega))]
    congr 1
    exact h k (by omega)

/-- Tail of `sumTo` is zero when the function vanishes. -/
theorem sumTo_tail_zero (g : Nat → Int) (m n : Nat) (hm : m ≤ n)
    (h : ∀ l, m ≤ l → l < n → g l = 0) :
    sumTo g n = sumTo g m := by
  induction n with
  | zero =>
    have := Nat.le_zero.mp hm
    subst this; rfl
  | succ k ih =>
    by_cases hmk : m ≤ k
    · simp only [sumTo]
      rw [h k hmk (by omega)]
      simp only [Int.add_zero]
      exact ih hmk (fun l hl1 hl2 => h l hl1 (by omega))
    · have heq : m = k + 1 := by omega
      subst heq; rfl


/-! **`mulAdjWith` specification** -/

/-- `mulAdjWith` unfolds to nested `Nat.fold` (outer: array builder, inner: sum). -/
theorem mulAdjWith_eq_fold (f : Nat → Nat) (z : Array Int) (n d : Nat) :
    mulAdjWith f z n d = Nat.fold n (fun v _ arr =>
      arr.set! v (Nat.fold d (fun p _ acc => acc + z[f (v * d + p)]!) 0))
      (Array.replicate n (0 : Int)) := by
  unfold mulAdjWith
  simp only [Id.run, bind, pure, Std.Range.forIn_eq_forIn_range', Std.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, forIn_range'_eq_fold, Nat.zero_add]

theorem mulAdjWith_size (f : Nat → Nat) (z : Array Int) (n d : Nat) :
    (mulAdjWith f z n d).size = n := by
  rw [mulAdjWith_eq_fold]; exact fold_set_size _ n n (Nat.le_refl n)

/-- `(mulAdjWith f z n d)[v]? = some (∑_{p<d} z[f(v*d+p)]!)` for `v < n`. -/
theorem mulAdjWith_getElem? (f : Nat → Nat) (z : Array Int) (n d v : Nat) :
    (mulAdjWith f z n d)[v]? =
    if v < n then some (Nat.fold d (fun p _ acc => acc + z[f (v * d + p)]!) 0) else none := by
  rw [mulAdjWith_eq_fold, fold_set_getElem? _ n n (Nat.le_refl n)]
  split <;> simp [*]

/-- `getD` version of `mulAdjWith` spec. -/
theorem mulAdjWith_getD (f : Nat → Nat) (z : Array Int) (n d v : Nat) (hv : v < n) :
    (mulAdjWith f z n d).getD v 0 =
    Nat.fold d (fun p _ acc => acc + z[f (v * d + p)]!) 0 :=
  getD_of_getElem?_some (by rw [mulAdjWith_getElem?, if_pos hv])


/-! **`psdColumnStep` sub-expression specifications** -/

/-- `zCol` (the column extraction loop in `psdColumnStep`) produces
    `certEntryInt certBytes k j` for `k ≤ j` and `0` for `k > j`. -/
private theorem zCol_spec (certBytes : ByteArray) (n j : Nat) (hj : j < n) (v : Nat) :
    (Nat.fold (j + 1) (fun i _ arr =>
      arr.set! i (decodeBase85Int certBytes (j * (j + 1) / 2 + i)))
      (Array.replicate n (0 : Int)))[v]? =
    if v < n then some (certEntryInt certBytes v j) else none := by
  rw [fold_set_getElem? _ n (j + 1) (by omega)]
  split
  case isTrue hv =>
    congr 1
    simp only [certEntryInt]
    by_cases hvj : v ≤ j
    · rw [if_pos hvj, if_pos (by omega)]
    · rw [if_neg hvj, if_neg (by omega)]
  case isFalse => rfl

/-- `getD` version of `zCol_spec`. -/
private theorem zCol_getD (certBytes : ByteArray) (n j k : Nat) (hj : j < n) (hk : k < n) :
    (Nat.fold (j + 1) (fun i _ arr =>
      arr.set! i (decodeBase85Int certBytes (j * (j + 1) / 2 + i)))
      (Array.replicate n (0 : Int))).getD k 0 =
    certEntryInt certBytes k j :=
  getD_of_getElem?_some (by rw [zCol_spec certBytes n j hj]; rw [if_pos hk])

/-- `colSum` (the column sum loop) equals `colSumZ certBytes n j`. -/
private theorem colSum_spec (certBytes : ByteArray) (n j : Nat) (hj : j < n) :
    Nat.fold (j + 1) (fun k _ acc => acc +
      (Nat.fold (j + 1) (fun i _ arr =>
        arr.set! i (decodeBase85Int certBytes (j * (j + 1) / 2 + i)))
        (Array.replicate n (0 : Int))).getD k 0) 0 =
    colSumZ certBytes n j := by
  rw [fold_sum_congr _ (fun k ↦ certEntryInt certBytes k j)
    (fun k hk ↦ zCol_getD certBytes n j k hj (by omega))]
  rw [← sumTo_eq_fold]
  simp only [colSumZ]
  exact (sumTo_tail_zero _ (j + 1) n (by omega)
    (fun l hl1 _ ↦ by simp [certEntryInt, show ¬(l ≤ j) from by omega])).symm


/-! **`mulAdjPre` ↔ `adjMulPure` bridge** -/

/-- `decodeNeighbors` entry at index `k` (via `getD`) equals the raw decode. -/
theorem decodeNeighbors_getD (rotBytes : ByteArray) (n d k : Nat) (hk : k < n * d) :
    (decodeNeighbors rotBytes n d).getD k 0 = decodeBase85Nat rotBytes (2 * k) := by
  unfold decodeNeighbors
  show (if _ : k < (Array.ofFn _).size then _ else _) = _
  split
  case isTrue h => exact Array.getElem_ofFn h
  case isFalse h => exact absurd (Array.size_ofFn ▸ hk) h

/-- Under involution bounds, `mulAdjPre neighbors z n d` entry at `v` equals
    `adjMulPure rotBytes zfun n d v`, where `zfun i = z.getD i 0` and
    `neighbors = decodeNeighbors rotBytes n d`. -/
theorem mulAdjPre_getD_eq_adjMulPure
    (rotBytes : ByteArray) (z : Array Int) (n d v : Nat)
    (hv : v < n) (hz : z.size = n) (hd : 0 < d)
    (hinv : ∀ k, k < n * d → decodeBase85Nat rotBytes (2 * k) < n) :
    (mulAdjPre (decodeNeighbors rotBytes n d) z n d).getD v 0 =
    adjMulPure rotBytes (fun i ↦ z.getD i 0) n d v := by
  show (mulAdjWith (fun k => (decodeNeighbors rotBytes n d)[k]!) z n d).getD v 0 = _
  rw [mulAdjWith_getD _ z n d v hv]
  unfold adjMulPure; rw [sumTo_eq_fold]
  apply fold_sum_congr; intro p hp
  -- Goal: z[(decodeNeighbors rotBytes n d)[v*d+p]!]! =
  --       z.getD (decodeBase85Nat rotBytes (2*(v*d+p)) % n) 0
  -- z[w]! = z.getD w 0 by rfl, so suffices to show the index is equal
  have hvdp : v * d + p < n * d :=
    calc v * d + p < v * d + d := Nat.add_lt_add_left hp _
    _ = (v + 1) * d := (Nat.succ_mul v d).symm
    _ ≤ n * d := Nat.mul_le_mul_right d (by omega)
  have hneq : (decodeNeighbors rotBytes n d).getD (v * d + p) 0 =
    decodeBase85Nat rotBytes (2 * (v * d + p)) := decodeNeighbors_getD rotBytes n d _ hvdp
  have hmod : decodeBase85Nat rotBytes (2 * (v * d + p)) % n =
    decodeBase85Nat rotBytes (2 * (v * d + p)) := Nat.mod_eq_of_lt (hinv _ hvdp)
  show z.getD ((decodeNeighbors rotBytes n d).getD (v * d + p) 0) 0 =
    z.getD (decodeBase85Nat rotBytes (2 * (v * d + p)) % n) 0
  rw [hneq, hmod]

/-! **Congruence helpers** -/

/-- `adjMulPure` depends only on `z` restricted to `{0, ..., n-1}`. -/
theorem adjMulPure_congr (rotBytes : ByteArray) (z₁ z₂ : Nat → Int) (n d v : Nat)
    (hn : 0 < n) (h : ∀ i, i < n → z₁ i = z₂ i) :
    adjMulPure rotBytes z₁ n d v = adjMulPure rotBytes z₂ n d v := by
  unfold adjMulPure
  congr 1; ext p
  exact h _ (Nat.mod_lt _ hn)

/-- `sumTo` congruence: if `g₁` and `g₂` agree on `{0, ..., n-1}`, their sums agree. -/
theorem sumTo_congr (g₁ g₂ : Nat → Int) (n : Nat)
    (h : ∀ i, i < n → g₁ i = g₂ i) :
    sumTo g₁ n = sumTo g₂ n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumTo]
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]

/-- Size of `mulAdjPre`. -/
theorem mulAdjPre_size (neighbors : Array Nat) (z : Array Int) (n d : Nat) :
    (mulAdjPre neighbors z n d).size = n := mulAdjWith_size _ z n d

/-! **`psdColumnStep` pij characterization** -/

/-- The `pij` value computed inside `psdColumnStep` for row `i`, column `j` equals
    `pEntryPure rotBytes certBytes n d c₁ c₂ c₃ i j` (under involution). -/
private theorem psdColumnStep_pij_eq
    (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (j i : Nat) (hj : j < n) (hi : i < n) (hd : 0 < d)
    (hinv : ∀ k, k < n * d → decodeBase85Nat rotBytes (2 * k) < n) :
    let neighbors := decodeNeighbors rotBytes n d
    let zCol := Nat.fold (j + 1) (fun k _ arr =>
      arr.set! k (decodeBase85Int certBytes (j * (j + 1) / 2 + k)))
      (Array.replicate n (0 : Int))
    let bz := mulAdjPre neighbors zCol n d
    let b2z := mulAdjPre neighbors bz n d
    let colSum := Nat.fold (j + 1) (fun k _ acc => acc + zCol.getD k 0) 0
    c₁ * zCol[i]! - c₂ * b2z[i]! + c₃ * colSum =
    pEntryPure rotBytes certBytes n d c₁ c₂ c₃ i j := by
  intro neighbors zCol bz b2z colSum_imp
  -- Step 1: zCol[i]! = certEntryInt certBytes i j
  have hzCol_i : (zCol : Array Int).getD i 0 = certEntryInt certBytes i j :=
    zCol_getD certBytes n j i hj hi
  -- Step 2: colSum_imp = colSumZ certBytes n j = sumTo ... n
  have hcolSum : colSum_imp = sumTo (fun l ↦ certEntryInt certBytes l j) n := by
    -- colSum_imp unfolds to Nat.fold (j+1) (... zCol.getD k 0 ...) 0
    -- which is definitionally equal to the explicit form in colSum_spec
    change _ = colSumZ certBytes n j
    exact colSum_spec certBytes n j hj
  -- Step 3: bz.getD v 0 = adjMulPure rotBytes (certEntryInt certBytes · j) n d v for v < n
  have hbz : ∀ v, v < n → bz.getD v 0 =
      adjMulPure rotBytes (fun k ↦ certEntryInt certBytes k j) n d v := by
    intro v hv
    rw [mulAdjPre_getD_eq_adjMulPure rotBytes zCol n d v hv
      (by rw [fold_set_size]; omega) hd hinv]
    exact adjMulPure_congr rotBytes _ _ n d v (by omega)
      (fun k hk ↦ zCol_getD certBytes n j k hj hk)
  -- Step 4: b2z.getD i 0 = adjMulPure rotBytes (adjMulPure rotBytes zj n d ·) n d i
  have hb2z_i : b2z.getD i 0 = adjMulPure rotBytes
      (fun v ↦ adjMulPure rotBytes (fun k ↦ certEntryInt certBytes k j) n d v) n d i := by
    rw [mulAdjPre_getD_eq_adjMulPure rotBytes bz n d i hi
      (mulAdjPre_size _ _ _ _) hd hinv]
    exact adjMulPure_congr rotBytes _ _ n d i (by omega) hbz
  -- Assemble: pEntryPure unfolds to c₁ * zj i - c₂ * b2zj_i + c₃ * colSum
  -- where each piece matches what we proved above
  unfold pEntryPure
  -- Now goal is: c₁ * zCol[i]! - c₂ * b2z[i]! + c₃ * colSum_imp =
  --   c₁ * certEntryInt ... - c₂ * adjMulPure ... + c₃ * sumTo ...
  -- zCol[i]! = zCol.getD i 0 (by rfl for Int arrays)
  -- Similarly for b2z[i]!
  change c₁ * zCol.getD i 0 - c₂ * b2z.getD i 0 + c₃ * colSum_imp =
    c₁ * certEntryInt certBytes i j -
    c₂ * adjMulPure rotBytes (fun v ↦ adjMulPure rotBytes (fun k ↦ certEntryInt certBytes k j) n d v) n d i +
    c₃ * sumTo (fun l ↦ certEntryInt certBytes l j) n
  rw [hzCol_i, hb2z_i, hcolSum]


/-! **Per-entry function and bridge to `pEntryPure`** -/

/-- The per-entry value computed inside `psdColumnStep` for row `i`, column `j`. -/
private def psdG (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (j i : Nat) : Int :=
  let neighbors := decodeNeighbors rotBytes n d
  let colStart := j * (j + 1) / 2
  let zCol := Id.run do
    let mut arr := Array.replicate n (0 : Int)
    for k in [:j+1] do arr := arr.set! k (decodeBase85Int certBytes (colStart + k))
    return arr
  let bz := mulAdjPre neighbors zCol n d
  let b2z := mulAdjPre neighbors bz n d
  let colSum := Id.run do
    let mut s : Int := 0
    for k in [:j+1] do s := s + zCol[k]!
    return s
  c₁ * zCol[i]! - c₂ * b2z[i]! + c₃ * colSum

/-- `psdG` equals `pEntryPure` under involution hypothesis. -/
private theorem psdG_eq_pEntryPure
    (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (j i : Nat) (hj : j < n) (hi : i < n) (hd : 0 < d)
    (hinv : ∀ k, k < n * d → decodeBase85Nat rotBytes (2 * k) < n) :
    psdG rotBytes certBytes n d c₁ c₂ c₃ j i =
    pEntryPure rotBytes certBytes n d c₁ c₂ c₃ i j := by
  simp only [psdG, Id.run, bind, pure, Std.Range.forIn_eq_forIn_range', Std.Range.size,
    Nat.div_one, Nat.sub_zero, Nat.add_sub_cancel, forIn_range'_eq_fold, Nat.zero_add]
  exact psdColumnStep_pij_eq rotBytes certBytes n d c₁ c₂ c₃ j i hj hi hd hinv


/-! **Tracker step functions** -/

/-- Tracker step on `Int × Bool × Int`. All branches explicitly reconstruct
    the tuple for compatibility with `MProd` correspondence proofs. -/
private def trackerStepP (g : Nat → Int) (j : Nat) (i : Nat)
    (s : Int × Bool × Int) : Int × Bool × Int :=
  if (i == j) = true then
    if s.2.1 = true then (s.1, false, g i)
    else if g i < s.2.2 then (s.1, s.2.1, g i)
    else (s.1, s.2.1, s.2.2)
  else if i < j then
    if (if g i ≥ 0 then g i else -g i) > s.1 then
      (if g i ≥ 0 then g i else -g i, s.2.1, s.2.2)
    else (s.1, s.2.1, s.2.2)
  else (s.1, s.2.1, s.2.2)

/-- Tracker step on `MProd` matching the compiled do-block body. -/
private def trackerStepM (g : Nat → Int) (j : Nat) (i : Nat)
    (r : MProd Int (MProd Bool Int)) : MProd Int (MProd Bool Int) :=
  if (i == j) = true then
    if r.snd.fst = true then ⟨r.fst, false, g i⟩
    else if g i < r.snd.snd then ⟨r.fst, r.snd.fst, g i⟩
    else ⟨r.fst, r.snd.fst, r.snd.snd⟩
  else if i < j then
    if (if g i ≥ 0 then g i else -g i) > r.fst then
      ⟨if g i ≥ 0 then g i else -g i, r.snd.fst, r.snd.snd⟩
    else ⟨r.fst, r.snd.fst, r.snd.snd⟩
  else ⟨r.fst, r.snd.fst, r.snd.snd⟩


/-! **MProd–Prod correspondence** -/

private def MProdProdCorr {α β γ : Type} (rm : MProd α (MProd β γ)) (rp : α × β × γ) : Prop :=
  rm.fst = rp.1 ∧ rm.snd.fst = rp.2.1 ∧ rm.snd.snd = rp.2.2

private theorem fold_preserves_corr {α β γ : Type}
    {step_m : Nat → MProd α (MProd β γ) → MProd α (MProd β γ)}
    {step_p : Nat → α × β × γ → α × β × γ}
    (hstep : ∀ i rm rp, MProdProdCorr rm rp → MProdProdCorr (step_m i rm) (step_p i rp))
    {init_m : MProd α (MProd β γ)} {init_p : α × β × γ}
    (hinit : MProdProdCorr init_m init_p) (n : Nat) :
    MProdProdCorr (Nat.fold n (fun i _ s => step_m i s) init_m)
                  (Nat.fold n (fun i _ s => step_p i s) init_p) := by
  induction n with
  | zero => exact hinit
  | succ n ih => simp only [Nat.fold_succ]; exact hstep n _ _ ih

private theorem trackerStep_corr (g : Nat → Int) (j i : Nat)
    (rm : MProd Int (MProd Bool Int)) (rp : Int × Bool × Int)
    (h : MProdProdCorr rm rp) :
    MProdProdCorr (trackerStepM g j i rm) (trackerStepP g j i rp) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold trackerStepM trackerStepP MProdProdCorr
  rw [h1, h2, h3]
  split <;> split <;> (try split) <;> (try split) <;> exact ⟨rfl, rfl, rfl⟩


/-! **Do-block = `Nat.fold` bridge** -/

private theorem ite_yield' (c : Prop) [Decidable c] (a b : β) :
    (if c then ForInStep.yield a else ForInStep.yield b) =
    ForInStep.yield (if c then a else b) := by split <;> rfl

private theorem tracker_body_M (g : Nat → Int) (j : Nat) (i : Nat)
    (r : MProd Int (MProd Bool Int)) :
    (if (i == j) = true then
      if r.snd.fst = true then ForInStep.yield ⟨r.fst, false, g i⟩
      else
        if g i < r.snd.snd then ForInStep.yield ⟨r.fst, r.snd.fst, g i⟩
        else ForInStep.yield ⟨r.fst, r.snd.fst, r.snd.snd⟩
    else
      if i < j then
        if (if g i ≥ 0 then g i else -g i) > r.fst then
          ForInStep.yield ⟨if g i ≥ 0 then g i else -g i, r.snd.fst, r.snd.snd⟩
        else ForInStep.yield ⟨r.fst, r.snd.fst, r.snd.snd⟩
      else ForInStep.yield ⟨r.fst, r.snd.fst, r.snd.snd⟩) =
    ForInStep.yield (trackerStepM g j i r) := by
  unfold trackerStepM
  split
  · split
    · rfl
    · simp only [ite_yield']
  · split
    · simp only [ite_yield']
    · rfl

private theorem tracker_3var_eq_fold (g : Nat → Int) (j n : Nat) (e₀ d₀ : Int) (f₀ : Bool) :
    (Id.run do
      let mut epsMax := e₀
      let mut first := f₀
      let mut minDiag := d₀
      for i in [:n] do
        let pij := g i
        if i == j then
          if first then minDiag := pij; first := false
          else if pij < minDiag then minDiag := pij
        else if i < j then
          let absPij := if pij >= 0 then pij else -pij
          if absPij > epsMax then epsMax := absPij
      return (epsMax, first, minDiag)) =
    Nat.fold n (fun i _ s => trackerStepP g j i s) (e₀, f₀, d₀) := by
  simp only [Id.run, bind, pure, Std.Range.forIn_eq_forIn_range', Std.Range.size, Nat.div_one,
    Nat.sub_zero, Nat.add_sub_cancel]
  have hbody_ext : (fun i (r : MProd Int (MProd Bool Int)) =>
      if (i == j) = true then
        if r.snd.fst = true then ForInStep.yield ⟨r.fst, false, g i⟩
        else
          if g i < r.snd.snd then ForInStep.yield ⟨r.fst, r.snd.fst, g i⟩
          else ForInStep.yield ⟨r.fst, r.snd.fst, r.snd.snd⟩
      else
        if i < j then
          if (if g i ≥ 0 then g i else -g i) > r.fst then
            ForInStep.yield ⟨if g i ≥ 0 then g i else -g i, r.snd.fst, r.snd.snd⟩
          else ForInStep.yield ⟨r.fst, r.snd.fst, r.snd.snd⟩
        else ForInStep.yield ⟨r.fst, r.snd.fst, r.snd.snd⟩) =
      (fun i r => ForInStep.yield (trackerStepM g j i r)) :=
    funext fun i => funext fun r => tracker_body_M g j i r
  rw [hbody_ext, forIn_range'_eq_fold (trackerStepM g j)]
  simp only [Nat.zero_add]
  have corr := fold_preserves_corr
    (trackerStep_corr g j) (⟨rfl, rfl, rfl⟩ : MProdProdCorr ⟨e₀, f₀, d₀⟩ (e₀, f₀, d₀)) n
  obtain ⟨c1, c2, c3⟩ := corr
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> assumption


/-! **Fold characterization** -/

private def foldMax (g : Nat → Int) : Nat → Int
  | 0 => 0
  | k + 1 => max (foldMax g k) (intAbs (g k))

private theorem step_offdiag (g : Nat → Int) (j i : Nat) (e d : Int) (f : Bool)
    (hi : i < j) :
    trackerStepP g j i (e, f, d) = (max e (intAbs (g i)), f, d) := by
  unfold trackerStepP
  have hbeq : (i == j) = false := beq_false_of_ne (by omega)
  simp only [hbeq, Bool.false_eq_true, ite_false, hi, ite_true]
  show (if intAbs (g i) > e then (intAbs (g i), f, d) else (e, f, d)) = _
  by_cases h : intAbs (g i) > e
  · rw [if_pos h]; congr 1; omega
  · rw [if_neg h]; congr 1; omega

private theorem step_diag (g : Nat → Int) (j : Nat) (e d : Int) (f : Bool) :
    trackerStepP g j j (e, f, d) =
    (e, false, if f then g j else min d (g j)) := by
  unfold trackerStepP
  simp only [beq_self_eq_true, ite_true]
  by_cases hf : f = true
  · simp [hf]
  · have hf' : f = false := by cases f <;> simp_all
    simp only [hf', Bool.false_eq_true, ite_false]
    by_cases hlt : g j < d
    · simp only [hlt, ite_true, show min d (g j) = g j from by omega]
    · simp only [hlt, ite_false, show min d (g j) = d from by omega]

private theorem step_skip (g : Nat → Int) (j i : Nat) (s : Int × Bool × Int)
    (hi : i > j) : trackerStepP g j i s = s := by
  unfold trackerStepP
  have hbeq : (i == j) = false := beq_false_of_ne (by omega)
  have hnlt : ¬(i < j) := by omega
  simp only [hbeq, Bool.false_eq_true, ite_false, hnlt, Prod.eta]

private theorem trackerFold_phase1 (g : Nat → Int) (j : Nat) (e₀ d₀ : Int) (f₀ : Bool)
    (k : Nat) (hk : k ≤ j) :
    Nat.fold k (fun i _ s => trackerStepP g j i s) (e₀, f₀, d₀) =
    (Nat.fold k (fun i _ e => max e (intAbs (g i))) e₀, f₀, d₀) := by
  induction k with
  | zero => simp [Nat.fold_zero]
  | succ m ih =>
    rw [Nat.fold_succ, Nat.fold_succ, ih (by omega)]
    exact step_offdiag g j m _ d₀ f₀ (by omega)

private theorem running_max_eq (g : Nat → Int) (e₀ : Int) (he : 0 ≤ e₀) (k : Nat) :
    Nat.fold k (fun i _ e => max e (intAbs (g i))) e₀ =
    max e₀ (foldMax g k) := by
  induction k with
  | zero => simp [Nat.fold_zero, foldMax]; omega
  | succ m ih => rw [Nat.fold_succ, ih, foldMax]; omega

private theorem trackerFold_trim (g : Nat → Int) (j : Nat) (e₀ d₀ : Int) (f₀ : Bool)
    (n : Nat) (hn : n ≥ j + 1) :
    Nat.fold n (fun i _ s => trackerStepP g j i s) (e₀, f₀, d₀) =
    Nat.fold (j + 1) (fun i _ s => trackerStepP g j i s) (e₀, f₀, d₀) := by
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hkj : k ≥ j + 1
    · rw [Nat.fold_succ, ih hkj, step_skip g j k _ (by omega)]
    · have hkeq : k = j := by omega
      subst hkeq; rfl

private theorem trackerFold_spec (g : Nat → Int) (j n : Nat) (e₀ d₀ : Int) (f₀ : Bool)
    (hj : j < n) (he : 0 ≤ e₀) :
    let r := Nat.fold n (fun i _ s => trackerStepP g j i s) (e₀, f₀, d₀)
    r.1 = max e₀ (foldMax g j) ∧ r.2.1 = false ∧
    r.2.2 = (if f₀ then g j else min d₀ (g j)) := by
  rw [trackerFold_trim g j e₀ d₀ f₀ n (by omega), Nat.fold_succ,
    trackerFold_phase1 g j e₀ d₀ f₀ j (Nat.le_refl j), step_diag g j _ d₀ f₀,
    running_max_eq g e₀ he j]
  exact ⟨rfl, rfl, rfl⟩


/-! **`foldMax` ↔ `epsMaxCol` connection** -/

private theorem foldMax_congr (g₁ g₂ : Nat → Int) (k : Nat)
    (h : ∀ i, i < k → g₁ i = g₂ i) : foldMax g₁ k = foldMax g₂ k := by
  induction k with
  | zero => rfl
  | succ m ih =>
    simp only [foldMax, ih (fun i hi => h i (by omega)), h m (by omega)]

private theorem foldMax_eq_epsMaxCol (rotBytes certBytes : ByteArray) (n d : Nat)
    (c₁ c₂ c₃ : Int) (j k : Nat) :
    foldMax (fun i => pEntryPure rotBytes certBytes n d c₁ c₂ c₃ i j) k =
    epsMaxCol rotBytes certBytes n d c₁ c₂ c₃ j (colSumZ certBytes n j) k := by
  induction k with
  | zero => simp [foldMax, epsMaxCol]
  | succ m ih =>
    simp only [foldMax, epsMaxCol, colSumZ, ih]; unfold pEntryPure; rfl


/-! **`psdColumnStep` ↔ fold bridge** -/

/-- Prod version of `psdColumnStep` for bridging to fold characterization. -/
private def psdColumnStepProd (doMulAdj : Array Int → Array Int)
    (certBytes : ByteArray) (n : Nat) (c₁ c₂ c₃ : Int)
    (state : PSDChunkResult) (j : Nat) : Int × Bool × Int :=
  let colStart := j * (j + 1) / 2
  let zCol := Id.run do
    let mut arr := Array.replicate n (0 : Int)
    for k in [:j+1] do arr := arr.set! k (decodeBase85Int certBytes (colStart + k))
    return arr
  let bz := doMulAdj zCol
  let b2z := doMulAdj bz
  let colSum := Id.run do
    let mut s : Int := 0
    for k in [:j+1] do s := s + zCol[k]!
    return s
  Id.run do
    let mut epsMax := state.epsMax
    let mut first := state.first
    let mut minDiag := state.minDiag
    for i in [:n] do
      let pij := c₁ * zCol[i]! - c₂ * b2z[i]! + c₃ * colSum
      if i == j then
        if first then minDiag := pij; first := false
        else if pij < minDiag then minDiag := pij
      else if i < j then
        let absPij := if pij >= 0 then pij else -pij
        if absPij > epsMax then epsMax := absPij
    return (epsMax, first, minDiag)

/-- `psdColumnStepProd` equals `Nat.fold` with `trackerStepP` using `psdG`. -/
private theorem psdColumnStepProd_eq_fold
    (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (state : PSDChunkResult) (j : Nat) :
    psdColumnStepProd (mulAdjPre (decodeNeighbors rotBytes n d) · n d)
      certBytes n c₁ c₂ c₃ state j =
    Nat.fold n (fun i _ s => trackerStepP
      (psdG rotBytes certBytes n d c₁ c₂ c₃ j) j i s)
      (state.epsMax, state.first, state.minDiag) := by
  unfold psdColumnStepProd
  exact tracker_3var_eq_fold _ j n state.epsMax state.minDiag state.first


/-! **Tracker loop characterization** -/

/-- The tracker loop inside `psdColumnStep` for column `j` (with `j < n`)
    updates the state as follows:
    - `epsMax` becomes `max(old.epsMax, epsMaxCol ... j (colSumZ ...) j)`
    - `minDiag` becomes `old.minDiag` min'd with `pEntryPure j j` (or set if first)
    - `first` becomes `false` -/
private theorem psdColumnStep_result
    (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (state : PSDChunkResult) (j : Nat) (hj : j < n) (hd : 0 < d)
    (hinv : ∀ k, k < n * d → decodeBase85Nat rotBytes (2 * k) < n)
    (he : 0 ≤ state.epsMax) :
    (psdColumnStep (mulAdjPre (decodeNeighbors rotBytes n d) · n d)
      certBytes n c₁ c₂ c₃ state j).epsMax = max state.epsMax
      (epsMaxCol rotBytes certBytes n d c₁ c₂ c₃ j (colSumZ certBytes n j) j) ∧
    (psdColumnStep (mulAdjPre (decodeNeighbors rotBytes n d) · n d)
      certBytes n c₁ c₂ c₃ state j).minDiag =
      (if state.first then pEntryPure rotBytes certBytes n d c₁ c₂ c₃ j j
       else min state.minDiag (pEntryPure rotBytes certBytes n d c₁ c₂ c₃ j j)) ∧
    (psdColumnStep (mulAdjPre (decodeNeighbors rotBytes n d) · n d)
      certBytes n c₁ c₂ c₃ state j).first = false := by
  -- Bridge PSDChunkResult → Prod (definitional equalities)
  show (psdColumnStepProd (mulAdjPre (decodeNeighbors rotBytes n d) · n d)
      certBytes n c₁ c₂ c₃ state j).1 = _ ∧
    (psdColumnStepProd (mulAdjPre (decodeNeighbors rotBytes n d) · n d)
      certBytes n c₁ c₂ c₃ state j).2.2 = _ ∧
    (psdColumnStepProd (mulAdjPre (decodeNeighbors rotBytes n d) · n d)
      certBytes n c₁ c₂ c₃ state j).2.1 = _
  rw [psdColumnStepProd_eq_fold]
  -- Apply fold characterization
  have hspec := trackerFold_spec (psdG rotBytes certBytes n d c₁ c₂ c₃ j) j n
    state.epsMax state.minDiag state.first hj he
  obtain ⟨heps, hfirst, hmin⟩ := hspec
  refine ⟨?_, ?_, hfirst⟩
  · -- epsMax: foldMax (psdG ...) j = epsMaxCol ... j
    rw [heps]; congr 1
    rw [foldMax_congr _ (fun i => pEntryPure rotBytes certBytes n d c₁ c₂ c₃ i j) j
      (fun i hi => psdG_eq_pEntryPure rotBytes certBytes n d c₁ c₂ c₃ j i hj (by omega) hd hinv)]
    exact foldMax_eq_epsMaxCol rotBytes certBytes n d c₁ c₂ c₃ j j
  · -- minDiag: psdG j j = pEntryPure j j
    rw [hmin, psdG_eq_pEntryPure rotBytes certBytes n d c₁ c₂ c₃ j j hj hj hd hinv]

/-! **Sequential fold produces `epsMaxVal`/`minDiagVal`** -/

private theorem epsMaxVal_nonneg (rotBytes certBytes : ByteArray) (n d : Nat)
    (c₁ c₂ c₃ : Int) (m : Nat) :
    0 ≤ epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ m := by
  induction m with
  | zero => simp [epsMaxVal]
  | succ k ih =>
    simp only [epsMaxVal]
    exact Int.le_trans ih (Int.le_max_left _ _)

private theorem minDiagVal_succ (rotBytes certBytes : ByteArray) (n d : Nat)
    (c₁ c₂ c₃ : Int) (m : Nat) (hm : 1 ≤ m) :
    minDiagVal rotBytes certBytes n d c₁ c₂ c₃ (m + 1) =
    min (minDiagVal rotBytes certBytes n d c₁ c₂ c₃ m)
        (pEntryPure rotBytes certBytes n d c₁ c₂ c₃ m m) := by
  cases m with
  | zero => omega
  | succ k => simp [minDiagVal]

/-- Folding `psdColumnStep` over columns `[0, ..., m-1]` (starting from the
    initial empty state) produces `epsMaxVal m` and `minDiagVal m`. -/
private theorem seqFold_eq_pure
    (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (hd : 0 < d) (hn : 0 < n)
    (hinv : ∀ k, k < n * d → decodeBase85Nat rotBytes (2 * k) < n) (m : Nat)
    (hm : m ≤ n) :
    let step := psdColumnStep (mulAdjPre (decodeNeighbors rotBytes n d) · n d)
      certBytes n c₁ c₂ c₃
    let init : PSDChunkResult := { epsMax := 0, minDiag := 0, first := true }
    let result := (List.range m).foldl step init
    result.epsMax = epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ m ∧
    (m = 0 ∨ result.minDiag = minDiagVal rotBytes certBytes n d c₁ c₂ c₃ m) ∧
    result.first = (m == 0) := by
  induction m with
  | zero => exact ⟨rfl, Or.inl rfl, rfl⟩
  | succ k ih =>
    have hk : k ≤ n := by omega
    have hkn : k < n := by omega
    obtain ⟨ih_eps, ih_min, ih_first⟩ := ih hk
    -- Decompose: foldl over range (k+1) = step (foldl over range k) k
    set prev := (List.range k).foldl
      (psdColumnStep (mulAdjPre (decodeNeighbors rotBytes n d) · n d)
        certBytes n c₁ c₂ c₃)
      { epsMax := 0, minDiag := 0, first := true } with hprev_def
    have hfold : (List.range (k + 1)).foldl
        (psdColumnStep (mulAdjPre (decodeNeighbors rotBytes n d) · n d)
          certBytes n c₁ c₂ c₃)
        { epsMax := 0, minDiag := 0, first := true } =
      psdColumnStep (mulAdjPre (decodeNeighbors rotBytes n d) · n d)
        certBytes n c₁ c₂ c₃ prev k := by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    -- Apply psdColumnStep_result
    have he : 0 ≤ prev.epsMax := ih_eps ▸ epsMaxVal_nonneg rotBytes certBytes n d c₁ c₂ c₃ k
    have hpsd := psdColumnStep_result rotBytes certBytes n d c₁ c₂ c₃ prev k hkn hd hinv he
    obtain ⟨hpsd_eps, hpsd_min, hpsd_first⟩ := hpsd
    set result := (List.range (k + 1)).foldl
      (psdColumnStep (mulAdjPre (decodeNeighbors rotBytes n d) · n d)
        certBytes n c₁ c₂ c₃)
      { epsMax := 0, minDiag := 0, first := true } with hresult_def
    have hresult_step := hresult_def.trans hfold
    -- epsMax
    have heps : result.epsMax = epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ (k + 1) := by
      rw [hresult_step, hpsd_eps, ih_eps, epsMaxVal]
    -- first
    have hfirst : result.first = (k + 1 == 0) := by
      rw [hresult_step, hpsd_first]; rfl
    -- minDiag
    have hmin : result.minDiag = minDiagVal rotBytes certBytes n d c₁ c₂ c₃ (k + 1) := by
      rw [hresult_step, hpsd_min]
      cases k with
      | zero =>
        -- prev.first = true, so minDiag = pEntryPure 0 0 = minDiagVal 1
        have : prev.first = true := ih_first
        rw [this, if_pos rfl, minDiagVal]
      | succ k' =>
        -- prev.first = false (since k'+1 ≠ 0)
        have : prev.first = false := by rw [ih_first]; rfl
        rw [this, if_neg (Bool.noConfusion)]
        have hprev_min : prev.minDiag = minDiagVal rotBytes certBytes n d c₁ c₂ c₃ (k' + 1) :=
          ih_min.resolve_left (by omega)
        rw [hprev_min]
        exact (minDiagVal_succ rotBytes certBytes n d c₁ c₂ c₃ (k' + 1) (by omega)).symm
    exact ⟨heps, Or.inr hmin, hfirst⟩

/-! **Partition + merge infrastructure** -/

/-- `epsMaxVal` is monotone. -/
private theorem epsMaxVal_mono (rotBytes certBytes : ByteArray) (n d : Nat)
    (c₁ c₂ c₃ : Int) (j : Nat) :
    epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ j ≤
    epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ (j + 1) := by
  simp only [epsMaxVal]; exact Int.le_max_left _ _

/-- `epsMaxVal` is monotone in its bound argument. -/
private theorem epsMaxVal_le_of_le (rotBytes certBytes : ByteArray) (n d : Nat)
    (c₁ c₂ c₃ : Int) {a b : Nat} (hab : a ≤ b) :
    epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ a ≤
    epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ b := by
  induction hab with
  | refl => exact Int.le_refl _
  | step _ ih => exact Int.le_trans ih (epsMaxVal_mono _ _ _ _ _ _ _ _)

/-- `epsMaxCol j ≤ epsMaxVal n` for `j < n`. -/
private theorem epsMaxCol_le_epsMaxVal (rotBytes certBytes : ByteArray) (n d : Nat)
    (c₁ c₂ c₃ : Int) (j : Nat) (hj : j < n) :
    epsMaxCol rotBytes certBytes n d c₁ c₂ c₃ j (colSumZ certBytes n j) j ≤
    epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ n := by
  have h1 : epsMaxCol rotBytes certBytes n d c₁ c₂ c₃ j (colSumZ certBytes n j) j ≤
      epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ (j + 1) := by
    unfold epsMaxVal; exact Int.le_max_right _ _
  exact Int.le_trans h1 (epsMaxVal_le_of_le _ _ _ _ _ _ _ (by omega))

/-- `minDiagVal` is antitone (decreasing). -/
private theorem minDiagVal_mono (rotBytes certBytes : ByteArray) (n d : Nat)
    (c₁ c₂ c₃ : Int) (j : Nat) (hj : 1 ≤ j) :
    minDiagVal rotBytes certBytes n d c₁ c₂ c₃ (j + 1) ≤
    minDiagVal rotBytes certBytes n d c₁ c₂ c₃ j := by
  rw [minDiagVal_succ _ _ _ _ _ _ _ j hj]; exact Int.min_le_left _ _

/-- `minDiagVal` is antitone (decreasing) in its bound argument for bounds ≥ 1. -/
private theorem minDiagVal_antitone (rotBytes certBytes : ByteArray) (n d : Nat)
    (c₁ c₂ c₃ : Int) {a b : Nat} (ha : 1 ≤ a) (hab : a ≤ b) :
    minDiagVal rotBytes certBytes n d c₁ c₂ c₃ b ≤
    minDiagVal rotBytes certBytes n d c₁ c₂ c₃ a := by
  induction hab with
  | refl => exact Int.le_refl _
  | @step m h ih => exact Int.le_trans (minDiagVal_mono _ _ _ _ _ _ _ m (Nat.le_trans ha h)) ih

/-- `minDiagVal n ≤ pEntryPure j j` for `j < n` and `n ≥ 1`. -/
private theorem minDiagVal_le_pEntryPure (rotBytes certBytes : ByteArray) (n d : Nat)
    (c₁ c₂ c₃ : Int) (j : Nat) (hj : j < n) :
    minDiagVal rotBytes certBytes n d c₁ c₂ c₃ n ≤
    pEntryPure rotBytes certBytes n d c₁ c₂ c₃ j j := by
  have h1 : minDiagVal rotBytes certBytes n d c₁ c₂ c₃ (j + 1) ≤
      pEntryPure rotBytes certBytes n d c₁ c₂ c₃ j j := by
    cases j with
    | zero => simp [minDiagVal]
    | succ j' => rw [minDiagVal_succ _ _ _ _ _ _ _ (j' + 1) (by omega)]; exact Int.min_le_right _ _
  exact Int.le_trans (minDiagVal_antitone _ _ _ _ _ _ _ (by omega) (by omega)) h1


/-! **List ForIn bridge** -/

private theorem list_forIn_yield_eq_foldl {α β : Type} (l : List α) (init : β) (f : β → α → β) :
    (forIn (m := Id) l init (fun x s => ForInStep.yield (f s x))) = l.foldl f init := by
  induction l generalizing init with
  | nil => simp only [forIn, ForIn.forIn, List.forIn'_nil, List.foldl, pure]
  | cons x xs ih =>
    simp only [forIn, ForIn.forIn, List.forIn'_cons, List.foldl, bind]
    exact ih (f init x)

private theorem checkPSDColumns_eq_listFoldl (neighbors : Array Nat)
    (certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int) (cols : Array Nat) :
    checkPSDColumns neighbors certBytes n d c₁ c₂ c₃ cols =
    cols.toList.foldl (psdColumnStep (mulAdjPre neighbors · n d) certBytes n c₁ c₂ c₃)
      { epsMax := 0, minDiag := 0, first := true } := by
  unfold checkPSDColumns; simp only [Id.run, bind, pure]
  rw [show forIn cols _ _ = forIn cols.toList _ _ from (Array.forIn_toList).symm]
  exact list_forIn_yield_eq_foldl cols.toList _ _


/-! **Fold invariants for `psdColumnStep`** -/

private abbrev stepFn (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int) :=
  psdColumnStep (mulAdjPre (decodeNeighbors rotBytes n d) · n d) certBytes n c₁ c₂ c₃

/-- `psdColumnStep_result` restated with `stepFn` in the conclusion for `rw` matching. -/
private theorem stepFn_result (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (state : PSDChunkResult) (j : Nat) (hj : j < n) (hd : 0 < d)
    (hinv : ∀ k, k < n * d → decodeBase85Nat rotBytes (2 * k) < n)
    (he : 0 ≤ state.epsMax) :
    (stepFn rotBytes certBytes n d c₁ c₂ c₃ state j).epsMax = max state.epsMax
      (epsMaxCol rotBytes certBytes n d c₁ c₂ c₃ j (colSumZ certBytes n j) j) ∧
    (stepFn rotBytes certBytes n d c₁ c₂ c₃ state j).minDiag =
      (if state.first then pEntryPure rotBytes certBytes n d c₁ c₂ c₃ j j
       else min state.minDiag (pEntryPure rotBytes certBytes n d c₁ c₂ c₃ j j)) ∧
    (stepFn rotBytes certBytes n d c₁ c₂ c₃ state j).first = false :=
  psdColumnStep_result rotBytes certBytes n d c₁ c₂ c₃ state j hj hd hinv he

/-- epsMax monotonicity: `foldl step` only increases epsMax. -/
private theorem foldl_step_epsMax_mono
    (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int) (hd : 0 < d)
    (hinv : ∀ k, k < n * d → decodeBase85Nat rotBytes (2 * k) < n)
    (L : List Nat) (state : PSDChunkResult) (hL : ∀ j ∈ L, j < n) (he : 0 ≤ state.epsMax) :
    state.epsMax ≤ (L.foldl (stepFn rotBytes certBytes n d c₁ c₂ c₃) state).epsMax := by
  induction L generalizing state with
  | nil => simp [List.foldl]
  | cons j rest ih =>
    simp only [List.foldl]
    have hj := hL j (.head rest)
    have hpsd := stepFn_result rotBytes certBytes n d c₁ c₂ c₃ state j hj hd hinv he
    have he' : 0 ≤ (stepFn rotBytes certBytes n d c₁ c₂ c₃ state j).epsMax := by
      rw [hpsd.1]; exact Int.le_trans he (Int.le_max_left _ _)
    calc state.epsMax
        ≤ max state.epsMax _ := Int.le_max_left _ _
      _ = (stepFn rotBytes certBytes n d c₁ c₂ c₃ state j).epsMax := hpsd.1.symm
      _ ≤ _ := ih _ (fun j hj => hL j (List.mem_cons_of_mem _ hj)) he'

/-- minDiag monotonicity: once `first = false`, `foldl step` only decreases minDiag. -/
private theorem foldl_step_minDiag_mono
    (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int) (hd : 0 < d)
    (hinv : ∀ k, k < n * d → decodeBase85Nat rotBytes (2 * k) < n)
    (L : List Nat) (state : PSDChunkResult) (hL : ∀ j ∈ L, j < n)
    (he : 0 ≤ state.epsMax) (hf : state.first = false) :
    (L.foldl (stepFn rotBytes certBytes n d c₁ c₂ c₃) state).minDiag ≤ state.minDiag := by
  induction L generalizing state with
  | nil => simp [List.foldl]
  | cons j rest ih =>
    simp only [List.foldl]
    have hj := hL j (.head rest)
    have hpsd := stepFn_result rotBytes certBytes n d c₁ c₂ c₃ state j hj hd hinv he
    have he' : 0 ≤ (stepFn rotBytes certBytes n d c₁ c₂ c₃ state j).epsMax := by
      rw [hpsd.1]; exact Int.le_trans he (Int.le_max_left _ _)
    have hf' : (stepFn rotBytes certBytes n d c₁ c₂ c₃ state j).first = false := hpsd.2.2
    have h1 := ih _ (fun j hj => hL j (List.mem_cons_of_mem _ hj)) he' hf'
    have h2 : (stepFn rotBytes certBytes n d c₁ c₂ c₃ state j).minDiag ≤ state.minDiag := by
      rw [hpsd.2.1, if_neg (by rw [hf]; decide)]; exact Int.min_le_left _ _
    exact Int.le_trans h1 h2

/-- epsMax upper bound: fold over valid columns ≤ epsMaxVal n. -/
private theorem foldl_step_epsMax_le
    (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int) (hd : 0 < d)
    (hinv : ∀ k, k < n * d → decodeBase85Nat rotBytes (2 * k) < n)
    (L : List Nat) (state : PSDChunkResult) (hL : ∀ j ∈ L, j < n)
    (he : 0 ≤ state.epsMax) (hle : state.epsMax ≤ epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ n) :
    (L.foldl (stepFn rotBytes certBytes n d c₁ c₂ c₃) state).epsMax ≤
      epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ n := by
  induction L generalizing state with
  | nil => simpa [List.foldl]
  | cons j rest ih =>
    simp only [List.foldl]
    have hj := hL j (.head rest)
    have hpsd := stepFn_result rotBytes certBytes n d c₁ c₂ c₃ state j hj hd hinv he
    have he' : 0 ≤ (stepFn rotBytes certBytes n d c₁ c₂ c₃ state j).epsMax := by
      rw [hpsd.1]; exact Int.le_trans he (Int.le_max_left _ _)
    have hle' : (stepFn rotBytes certBytes n d c₁ c₂ c₃ state j).epsMax ≤
        epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ n := by
      rw [hpsd.1]; exact Int.max_le.mpr ⟨hle, epsMaxCol_le_epsMaxVal _ _ _ _ _ _ _ j hj⟩
    exact ih _ (fun j hj => hL j (List.mem_cons_of_mem _ hj)) he' hle'

/-- epsMax lower bound: for `j ∈ L`, fold result ≥ `epsMaxCol j`. -/
private theorem foldl_step_epsMax_ge
    (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int) (hd : 0 < d)
    (hinv : ∀ k, k < n * d → decodeBase85Nat rotBytes (2 * k) < n)
    (L : List Nat) (state : PSDChunkResult) (hL : ∀ j ∈ L, j < n) (he : 0 ≤ state.epsMax)
    {j : Nat} (hj : j ∈ L) :
    epsMaxCol rotBytes certBytes n d c₁ c₂ c₃ j (colSumZ certBytes n j) j ≤
    (L.foldl (stepFn rotBytes certBytes n d c₁ c₂ c₃) state).epsMax := by
  induction L generalizing state with
  | nil => nomatch hj
  | cons x rest ih =>
    simp only [List.foldl]
    have hx := hL x (.head rest)
    have hpsd := stepFn_result rotBytes certBytes n d c₁ c₂ c₃ state x hx hd hinv he
    have he' : 0 ≤ (stepFn rotBytes certBytes n d c₁ c₂ c₃ state x).epsMax := by
      rw [hpsd.1]; exact Int.le_trans he (Int.le_max_left _ _)
    cases List.mem_cons.mp hj with
    | inl hjx =>
      subst hjx
      calc epsMaxCol _ _ _ _ _ _ _ j (colSumZ _ _ j) j
          ≤ max state.epsMax _ := Int.le_max_right _ _
        _ = (stepFn rotBytes certBytes n d c₁ c₂ c₃ state j).epsMax := hpsd.1.symm
        _ ≤ _ := foldl_step_epsMax_mono _ _ _ _ _ _ _ hd hinv rest _
            (fun j hj => hL j (List.mem_cons_of_mem _ hj)) he'
    | inr hjr => exact ih _ (fun j hj => hL j (List.mem_cons_of_mem _ hj)) he' hjr

/-- After nonempty fold, `first = false`. -/
private theorem foldl_step_not_first
    (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int) (hd : 0 < d)
    (hinv : ∀ k, k < n * d → decodeBase85Nat rotBytes (2 * k) < n)
    (L : List Nat) (state : PSDChunkResult) (hL : ∀ j ∈ L, j < n) (he : 0 ≤ state.epsMax)
    (hne : L ≠ []) :
    (L.foldl (stepFn rotBytes certBytes n d c₁ c₂ c₃) state).first = false := by
  cases L with
  | nil => exact absurd rfl hne
  | cons x rest =>
    simp only [List.foldl]
    have hx := hL x (.head rest)
    have hpsd := stepFn_result rotBytes certBytes n d c₁ c₂ c₃ state x hx hd hinv he
    have he' : 0 ≤ (stepFn rotBytes certBytes n d c₁ c₂ c₃ state x).epsMax := by
      rw [hpsd.1]; exact Int.le_trans he (Int.le_max_left _ _)
    cases rest with
    | nil => simp [List.foldl]; exact hpsd.2.2
    | cons y ys =>
      exact foldl_step_not_first _ _ _ _ _ _ _ hd hinv (y :: ys) _
        (fun j hj => hL j (List.mem_cons_of_mem x hj))
        he' (List.cons_ne_nil _ _)

/-- minDiag lower bound: fold over valid columns ≥ minDiagVal n (for nonempty L). -/
private theorem foldl_step_minDiag_ge
    (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int) (hd : 0 < d)
    (hinv : ∀ k, k < n * d → decodeBase85Nat rotBytes (2 * k) < n)
    (L : List Nat) (state : PSDChunkResult) (hL : ∀ j ∈ L, j < n) (he : 0 ≤ state.epsMax)
    (hn : 0 < n) (hne : L ≠ [])
    (hge : state.first = true ∨ minDiagVal rotBytes certBytes n d c₁ c₂ c₃ n ≤ state.minDiag) :
    minDiagVal rotBytes certBytes n d c₁ c₂ c₃ n ≤
    (L.foldl (stepFn rotBytes certBytes n d c₁ c₂ c₃) state).minDiag := by
  induction L generalizing state with
  | nil => exact absurd rfl hne
  | cons x rest ih =>
    simp only [List.foldl]
    have hx := hL x (.head rest)
    have hpsd := stepFn_result rotBytes certBytes n d c₁ c₂ c₃ state x hx hd hinv he
    have he' : 0 ≤ (stepFn rotBytes certBytes n d c₁ c₂ c₃ state x).epsMax := by
      rw [hpsd.1]; exact Int.le_trans he (Int.le_max_left _ _)
    have hmin_ge : minDiagVal rotBytes certBytes n d c₁ c₂ c₃ n ≤
        (stepFn rotBytes certBytes n d c₁ c₂ c₃ state x).minDiag := by
      rw [hpsd.2.1]
      cases hge with
      | inl hfirst =>
        rw [if_pos (by rw [hfirst])]
        exact minDiagVal_le_pEntryPure _ _ _ _ _ _ _ x hx
      | inr hge' =>
        cases hfb : state.first with
        | true => rw [if_pos rfl]; exact minDiagVal_le_pEntryPure _ _ _ _ _ _ _ x hx
        | false =>
          rw [if_neg (by decide)]
          exact Int.le_min.mpr ⟨hge', minDiagVal_le_pEntryPure _ _ _ _ _ _ _ x hx⟩
    cases rest with
    | nil => simp [List.foldl]; exact hmin_ge
    | cons y ys =>
      exact ih _ (fun j hj => hL j (List.mem_cons_of_mem _ hj)) he'
        (List.cons_ne_nil _ _) (Or.inr hmin_ge)

/-- minDiag upper bound: for `j ∈ L`, fold result ≤ `pEntryPure j j` (nonempty L). -/
private theorem foldl_step_minDiag_le
    (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int) (hd : 0 < d)
    (hinv : ∀ k, k < n * d → decodeBase85Nat rotBytes (2 * k) < n)
    (L : List Nat) (state : PSDChunkResult) (hL : ∀ j ∈ L, j < n) (he : 0 ≤ state.epsMax)
    {j : Nat} (hj : j ∈ L) :
    (L.foldl (stepFn rotBytes certBytes n d c₁ c₂ c₃) state).minDiag ≤
    pEntryPure rotBytes certBytes n d c₁ c₂ c₃ j j := by
  induction L generalizing state with
  | nil => nomatch hj
  | cons x rest ih =>
    simp only [List.foldl]
    have hx := hL x (.head rest)
    have hpsd := stepFn_result rotBytes certBytes n d c₁ c₂ c₃ state x hx hd hinv he
    have he' : 0 ≤ (stepFn rotBytes certBytes n d c₁ c₂ c₃ state x).epsMax := by
      rw [hpsd.1]; exact Int.le_trans he (Int.le_max_left _ _)
    cases List.mem_cons.mp hj with
    | inl hjx =>
      subst hjx
      have hstep_le : (stepFn rotBytes certBytes n d c₁ c₂ c₃ state j).minDiag ≤
          pEntryPure rotBytes certBytes n d c₁ c₂ c₃ j j := by
        rw [hpsd.2.1]
        cases state.first <;> simp [Int.min_le_right]
      cases rest with
      | nil => simpa [List.foldl]
      | cons y ys =>
        exact Int.le_trans (foldl_step_minDiag_mono _ _ _ _ _ _ _ hd hinv _ _
          (fun j hj => hL j (List.mem_cons_of_mem _ hj)) he' hpsd.2.2) hstep_le
    | inr hjr => exact ih _ (fun j hj => hL j (List.mem_cons_of_mem _ hj)) he' hjr


/-! **Merge lemmas** -/

private theorem merge_first_true (b : PSDChunkResult) :
    PSDChunkResult.merge { epsMax := 0, minDiag := 0, first := true } b = b := by
  simp [PSDChunkResult.merge]

private theorem merge_first_gen (a b : PSDChunkResult) (ha : a.first = true) :
    PSDChunkResult.merge a b = b := by
  simp [PSDChunkResult.merge, ha]

private theorem merge_not_first (a b : PSDChunkResult) (ha : a.first = false) :
    (PSDChunkResult.merge a b).first = false := by
  simp [PSDChunkResult.merge, ha]; split <;> simp_all

private theorem merge_first_right (a b : PSDChunkResult) (ha : a.first = false)
    (hb : b.first = true) : PSDChunkResult.merge a b = a := by
  simp [PSDChunkResult.merge, ha, hb]

private theorem merge_right_not_first (a b : PSDChunkResult) (hb : b.first = false) :
    (PSDChunkResult.merge a b).first = false := by
  cases ha : a.first
  · exact merge_not_first a b ha
  · rw [merge_first_gen a b ha]; exact hb

/-! **List-level merge fold helpers** -/

private theorem foldl_merge_preserves_not_first (L : List PSDChunkResult) (acc : PSDChunkResult)
    (hacc : acc.first = false) :
    (L.foldl PSDChunkResult.merge acc).first = false := by
  induction L generalizing acc with
  | nil => exact hacc
  | cons x rest ih => simp only [List.foldl]; exact ih _ (merge_not_first acc x hacc)

private theorem foldl_merge_has_not_first (L : List PSDChunkResult) (acc : PSDChunkResult)
    {x : PSDChunkResult} (hx : x ∈ L) (hxf : x.first = false) :
    (L.foldl PSDChunkResult.merge acc).first = false := by
  induction L generalizing acc with
  | nil => nomatch hx
  | cons y rest ih =>
    simp only [List.foldl]
    cases List.mem_cons.mp hx with
    | inl h =>
      subst h
      exact foldl_merge_preserves_not_first rest _ (merge_right_not_first acc x hxf)
    | inr hyr => exact ih _ hyr

private theorem foldl_merge_epsMax_le (L : List PSDChunkResult) (acc : PSDChunkResult)
    (bound : Int) (hacc : acc.epsMax ≤ bound)
    (hL : ∀ x ∈ L, x.epsMax ≤ bound) :
    (L.foldl PSDChunkResult.merge acc).epsMax ≤ bound := by
  induction L generalizing acc with
  | nil => simpa [List.foldl]
  | cons x rest ih =>
    simp only [List.foldl]
    apply ih
    · have hx := hL x (.head rest)
      simp only [PSDChunkResult.merge]
      split
      · exact hx
      · split
        · exact hacc
        · split <;> omega
    · exact fun y hy => hL y (List.mem_cons_of_mem _ hy)

private theorem foldl_merge_epsMax_ge_acc (L : List PSDChunkResult) (acc : PSDChunkResult)
    (hacc : acc.first = false) :
    acc.epsMax ≤ (L.foldl PSDChunkResult.merge acc).epsMax := by
  induction L generalizing acc with
  | nil => simp [List.foldl]
  | cons x rest ih =>
    simp only [List.foldl]
    have hm : acc.epsMax ≤ (PSDChunkResult.merge acc x).epsMax := by
      cases hxf : x.first
      · simp [PSDChunkResult.merge, hacc, hxf]; split <;> omega
      · simp [merge_first_right acc x hacc hxf]
    exact Int.le_trans hm (ih _ (merge_not_first acc x hacc))

private theorem foldl_merge_epsMax_ge_mem (L : List PSDChunkResult) (acc : PSDChunkResult)
    {x : PSDChunkResult} (hx : x ∈ L) (hxf : x.first = false) :
    x.epsMax ≤ (L.foldl PSDChunkResult.merge acc).epsMax := by
  induction L generalizing acc with
  | nil => nomatch hx
  | cons y rest ih =>
    simp only [List.foldl]
    cases List.mem_cons.mp hx with
    | inl h =>
      subst h
      have hm : x.epsMax ≤ (PSDChunkResult.merge acc x).epsMax := by
        cases haf : acc.first
        · simp [PSDChunkResult.merge, haf, hxf]; split <;> omega
        · simp [merge_first_gen acc x haf]
      exact Int.le_trans hm
        (foldl_merge_epsMax_ge_acc rest _ (merge_right_not_first acc x hxf))
    | inr hyr => exact ih _ hyr

private theorem foldl_merge_minDiag_le_acc (L : List PSDChunkResult) (acc : PSDChunkResult)
    (hacc : acc.first = false) :
    (L.foldl PSDChunkResult.merge acc).minDiag ≤ acc.minDiag := by
  induction L generalizing acc with
  | nil => simp [List.foldl]
  | cons x rest ih =>
    simp only [List.foldl]
    have hm : (PSDChunkResult.merge acc x).minDiag ≤ acc.minDiag := by
      cases hxf : x.first
      · simp [PSDChunkResult.merge, hacc, hxf]; split <;> omega
      · simp [merge_first_right acc x hacc hxf]
    exact Int.le_trans (ih _ (merge_not_first acc x hacc)) hm

private theorem foldl_merge_minDiag_le_mem (L : List PSDChunkResult) (acc : PSDChunkResult)
    {x : PSDChunkResult} (hx : x ∈ L) (hxf : x.first = false) :
    (L.foldl PSDChunkResult.merge acc).minDiag ≤ x.minDiag := by
  induction L generalizing acc with
  | nil => nomatch hx
  | cons y rest ih =>
    simp only [List.foldl]
    cases List.mem_cons.mp hx with
    | inl h =>
      subst h
      have hm : (PSDChunkResult.merge acc x).minDiag ≤ x.minDiag := by
        cases haf : acc.first
        · simp [PSDChunkResult.merge, haf, hxf]; split <;> omega
        · simp [merge_first_gen acc x haf]
      exact Int.le_trans
        (foldl_merge_minDiag_le_acc rest _ (merge_right_not_first acc x hxf)) hm
    | inr hyr => exact ih _ hyr

private theorem foldl_merge_minDiag_ge (L : List PSDChunkResult) (acc : PSDChunkResult)
    (bound : Int) (hacc : acc.first = true ∨ bound ≤ acc.minDiag)
    (hL : ∀ x ∈ L, x.first = false → bound ≤ x.minDiag) :
    (L.foldl PSDChunkResult.merge acc).first = false →
    bound ≤ (L.foldl PSDChunkResult.merge acc).minDiag := by
  induction L generalizing acc with
  | nil =>
    simp [List.foldl]
    intro hf; exact (hacc.resolve_left (by rw [hf]; decide))
  | cons x rest ih =>
    simp only [List.foldl]
    have hL' : ∀ y ∈ rest, y.first = false → bound ≤ y.minDiag :=
      fun y hy hyf => hL y (List.mem_cons_of_mem _ hy) hyf
    suffices h : (PSDChunkResult.merge acc x).first = true ∨
        bound ≤ (PSDChunkResult.merge acc x).minDiag from ih _ h hL'
    cases haf : acc.first
    · cases hxf : x.first
      · right
        have hge_a := hacc.resolve_left (by rw [haf]; decide)
        have hge_x := hL x (.head rest) hxf
        simp [PSDChunkResult.merge, haf, hxf]; split <;> omega
      · right
        rw [merge_first_right acc x haf hxf]
        exact hacc.resolve_left (by rw [haf]; decide)
    · cases hxf : x.first
      · right
        rw [merge_first_gen acc x haf]
        exact hL x (.head rest) hxf
      · left
        rw [merge_first_gen acc x haf]
        exact hxf

/-! **Array ↔ List bridge** -/

private theorem forall_toList_of_forall_array {α : Type} {P : α → Prop}
    (a : Array α) (h : ∀ i, (hi : i < a.size) → P a[i]) :
    ∀ x ∈ a.toList, P x := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  exact h i hi

/-! **Merge fold bounds** -/

/-- After folding merge over results, epsMax ≤ upper bound. -/
private theorem mergeFoldl_epsMax_le (results : Array PSDChunkResult) (bound : Int)
    (hb : 0 ≤ bound)
    (h : ∀ i, (hi : i < results.size) → results[i].epsMax ≤ bound) :
    (results.toList.foldl PSDChunkResult.merge
      { epsMax := 0, minDiag := 0, first := true }).epsMax ≤ bound :=
  foldl_merge_epsMax_le results.toList _ bound hb
    (forall_toList_of_forall_array results h)

/-- After folding merge over results, epsMax ≥ any chunk's epsMax. -/
private theorem mergeFoldl_epsMax_ge (results : Array PSDChunkResult)
    (i : Nat) (hi : i < results.size) (hne : results[i].first = false) :
    results[i].epsMax ≤
    (results.toList.foldl PSDChunkResult.merge
      { epsMax := 0, minDiag := 0, first := true }).epsMax :=
  foldl_merge_epsMax_ge_mem results.toList _ (Array.getElem_mem_toList hi) hne

/-- After folding merge over results, minDiag ≥ lower bound. -/
private theorem mergeFoldl_minDiag_ge (results : Array PSDChunkResult) (bound : Int)
    (h : ∀ i, (hi : i < results.size) → results[i].first = false → bound ≤ results[i].minDiag) :
    (results.toList.foldl PSDChunkResult.merge
      { epsMax := 0, minDiag := 0, first := true }).first = false →
    bound ≤ (results.toList.foldl PSDChunkResult.merge
      { epsMax := 0, minDiag := 0, first := true }).minDiag := by
  apply foldl_merge_minDiag_ge results.toList _ bound (Or.inl rfl)
  intro x hx hxf
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  exact h i hi hxf

/-- After folding merge over results, minDiag ≤ any non-first chunk's minDiag. -/
private theorem mergeFoldl_minDiag_le (results : Array PSDChunkResult)
    (i : Nat) (hi : i < results.size) (hne : results[i].first = false) :
    (results.toList.foldl PSDChunkResult.merge
      { epsMax := 0, minDiag := 0, first := true }).minDiag ≤ results[i].minDiag :=
  foldl_merge_minDiag_le_mem results.toList _ (Array.getElem_mem_toList hi) hne

/-- After folding merge, if any chunk is non-first, merged is non-first. -/
private theorem mergeFoldl_not_first (results : Array PSDChunkResult)
    (i : Nat) (hi : i < results.size) (hne : results[i].first = false) :
    (results.toList.foldl PSDChunkResult.merge
      { epsMax := 0, minDiag := 0, first := true }).first = false :=
  foldl_merge_has_not_first results.toList _ (Array.getElem_mem_toList hi) hne


/-! **buildColumnLists partition** -/

/-- `buildColumnLists` expressed as `Nat.fold` via `forIn_range_eq_fold`. -/
private theorem buildColumnLists_eq_fold (n numChunks : Nat) :
    buildColumnLists n numChunks =
    Nat.fold n (fun j _ lists => lists.set! (j % numChunks) (lists[j % numChunks]!.push j))
      (Array.replicate numChunks (Array.mkEmpty (n / numChunks + 1))) := by
  unfold buildColumnLists
  exact forIn_range_eq_fold _ _ n

/-- `getElem!` after `set!` at same index. -/
private theorem getElem!_set!_eq (a : Array (Array Nat)) (i : Nat) (v : Array Nat)
    (h : i < a.size) : (a.set! i v)[i]! = v := by
  simp only [Array.set!, Array.setIfInBounds, h, dite_true]
  show (a.set i v h).getD i default = v
  unfold Array.getD
  simp [Array.size_set, h]

/-- `getElem!` after `set!` at different index. -/
private theorem getElem!_set!_ne (a : Array (Array Nat)) (i c : Nat) (v : Array Nat)
    (hne : i ≠ c) : (a.set! i v)[c]! = a[c]! := by
  simp only [Array.set!, Array.setIfInBounds]
  split
  · rename_i h
    show (a.set i v h).getD c default = a.getD c default
    unfold Array.getD
    simp only [Array.size_set]
    split
    · rename_i hc; exact Array.getElem_set_ne h hc hne
    · rfl
  · rfl

/-- Set at chunk `k % numChunks` preserves membership at other chunks. -/
private theorem bcl_step_preserves (lists : Array (Array Nat))
    (k j numChunks c : Nat) (hsize : lists.size = numChunks) (hc_lt : c < numChunks)
    (hmem : j ∈ lists[c]!.toList) :
    j ∈ (lists.set! (k % numChunks) (lists[k % numChunks]!.push k))[c]!.toList := by
  by_cases hc : k % numChunks = c
  · subst hc
    rw [getElem!_set!_eq _ _ _ (by omega)]
    simp only [Array.toList_push, List.mem_append, List.mem_singleton]
    left; exact hmem
  · rw [getElem!_set!_ne _ _ _ _ hc]; exact hmem

/-- Setting at chunk `k % numChunks` adds `k` to that chunk. -/
private theorem bcl_step_adds (lists : Array (Array Nat))
    (k numChunks : Nat) (hsize : lists.size = numChunks) (hnc : 0 < numChunks) :
    k ∈ (lists.set! (k % numChunks) (lists[k % numChunks]!.push k))[k % numChunks]!.toList := by
  rw [getElem!_set!_eq _ _ _ (by rw [hsize]; exact Nat.mod_lt _ hnc)]
  simp [Array.toList_push]

/-- Size of `set!`. -/
private theorem size_set! {α : Type} (a : Array α) (i : Nat) (v : α) :
    (a.set! i v).size = a.size := by
  simp [Array.set!, Array.setIfInBounds]; split <;> simp [Array.size_set]

/-- Fold invariant: size preserved and all `j < k` are in chunk `j % numChunks`. -/
private theorem bcl_fold_invariant (n numChunks : Nat) (hnc : 0 < numChunks) (k : Nat) :
    let result := Nat.fold k (fun j _ lists =>
      lists.set! (j % numChunks) (lists[j % numChunks]!.push j))
      (Array.replicate numChunks (Array.mkEmpty (n / numChunks + 1)))
    result.size = numChunks ∧
    ∀ j, j < k → j ∈ result[j % numChunks]!.toList := by
  induction k with
  | zero =>
    simp only [Nat.fold]
    exact ⟨Array.size_replicate, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨hsize, hmem⟩ := ih
    constructor
    · simp only [Nat.fold_succ]; rw [size_set!]; exact hsize
    · intro j hj
      simp only [Nat.fold_succ]
      by_cases hjm : j = m
      · subst hjm; exact bcl_step_adds _ _ _ hsize hnc
      · exact bcl_step_preserves _ _ _ _ _ hsize (Nat.mod_lt j hnc)
          (hmem j (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hj) hjm))

/-- Every `j < n` appears in `buildColumnLists n numChunks` at chunk `j % numChunks`. -/
private theorem buildColumnLists_mem (n numChunks j : Nat) (hj : j < n) (hnc : 0 < numChunks) :
    j ∈ (buildColumnLists n numChunks)[j % numChunks]!.toList := by
  rw [buildColumnLists_eq_fold]
  exact (bcl_fold_invariant n numChunks hnc n).2 j hj


/-! **Partition + merge = sequential fold** -/

/-- `buildColumnLists` has `numChunks` entries. -/
private theorem buildColumnLists_size (n numChunks : Nat) (hnc : 0 < numChunks) :
    (buildColumnLists n numChunks).size = numChunks := by
  rw [buildColumnLists_eq_fold]
  exact (bcl_fold_invariant n numChunks hnc n).1

/-- All entries in chunk `c` of `buildColumnLists n numChunks` are `< n`. -/
private theorem buildColumnLists_bound (n numChunks c : Nat)
    (hnc : 0 < numChunks) (x : Nat)
    (hx : x ∈ (buildColumnLists n numChunks)[c]!.toList) (hc : c < numChunks) :
    x < n := by
  rw [buildColumnLists_eq_fold] at hx
  -- Prove by extending fold invariant with upper bound property
  suffices h : ∀ c, c < numChunks → ∀ y ∈
      (Nat.fold n (fun j _ lists => lists.set! (j % numChunks) (lists[j % numChunks]!.push j))
        (Array.replicate numChunks (Array.mkEmpty (n / numChunks + 1))))[c]!.toList, y < n from
    h c hc x hx
  -- Induction on n
  suffices ∀ k, k ≤ n → ∀ c', c' < numChunks → ∀ y ∈
      (Nat.fold k (fun j _ lists => lists.set! (j % numChunks) (lists[j % numChunks]!.push j))
        (Array.replicate numChunks (Array.mkEmpty (n / numChunks + 1))))[c']!.toList, y < n by
    exact fun c' hc' y hy => this n (Nat.le_refl n) c' hc' y hy
  intro k hk
  induction k with
  | zero =>
    intro c' hc' y hy
    simp only [Nat.fold] at hy
    exfalso
    have hempty : (Array.replicate numChunks (Array.mkEmpty (n / numChunks + 1) : Array Nat)).getD c' default
        = Array.mkEmpty (n / numChunks + 1) := by
      unfold Array.getD; simp [Array.size_replicate, hc', Array.getElem_replicate]
    change y ∈ ((Array.replicate numChunks (Array.mkEmpty (n / numChunks + 1) : Array Nat)).getD c' default).toList at hy
    rw [hempty] at hy; exact absurd hy (List.not_mem_nil)
  | succ m ih =>
    intro c' hc' y hy
    simp only [Nat.fold_succ] at hy
    by_cases hmk : m % numChunks = c'
    · subst hmk
      rw [getElem!_set!_eq _ _ _ (by
        rw [(bcl_fold_invariant n numChunks hnc m).1]; exact Nat.mod_lt m hnc)] at hy
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hy
      cases hy with
      | inl h => exact ih (by omega) _ hc' _ h
      | inr h => omega
    · rw [getElem!_set!_ne _ _ _ _ hmk] at hy
      exact ih (by omega) c' hc' y hy

/-- Bridge: `a[i]! = a[i]` when `i < a.size`. -/
private theorem getElem!_eq_getElem {α : Type} [Inhabited α] (a : Array α) (i : Nat)
    (h : i < a.size) : a[i]! = a[i] := by
  show a.getD i default = a[i]; unfold Array.getD; simp [h]

/-- `epsMaxVal` is bounded by any common upper bound on `epsMaxCol`. -/
private theorem epsMaxVal_le_of_bounds (rotBytes certBytes : ByteArray) (n d : Nat)
    (c₁ c₂ c₃ : Int) (m : Nat) (b : Int) (hb : 0 ≤ b)
    (h : ∀ j, j < m → epsMaxCol rotBytes certBytes n d c₁ c₂ c₃ j (colSumZ certBytes n j) j ≤ b) :
    epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ m ≤ b := by
  induction m with
  | zero => simp [epsMaxVal]; exact hb
  | succ k ih =>
    simp only [epsMaxVal]
    exact Int.max_le.mpr ⟨ih (fun j hj => h j (by omega)), h k (by omega)⟩

/-- `minDiagVal` is bounded below by any common lower bound on diagonal entries. -/
private theorem le_minDiagVal_of_bounds (rotBytes certBytes : ByteArray) (n d : Nat)
    (c₁ c₂ c₃ : Int) (m : Nat) (b : Int) (hm : 1 ≤ m)
    (h : ∀ j, j < m → b ≤ pEntryPure rotBytes certBytes n d c₁ c₂ c₃ j j) :
    b ≤ minDiagVal rotBytes certBytes n d c₁ c₂ c₃ m := by
  induction m with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => simp [minDiagVal]; exact h 0 (by omega)
    | succ k' =>
      simp only [minDiagVal]
      exact Int.le_min.mpr ⟨ih (by omega) (fun j hj => h j (by omega)),
                            h (k' + 1) (by omega)⟩

/-- `PSDChunkResult.merge` is compatible with `psdColumnStep`: processing chunks
    independently then merging equals sequential processing. -/
private theorem merged_eq_sequential
    (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (hd : 0 < d) (hn : 0 < n)
    (hinv : ∀ k, k < n * d → decodeBase85Nat rotBytes (2 * k) < n) :
    let neighbors := decodeNeighbors rotBytes n d
    let step := psdColumnStep (mulAdjPre neighbors · n d) certBytes n c₁ c₂ c₃
    let init : PSDChunkResult := { epsMax := 0, minDiag := 0, first := true }
    let columnLists := buildColumnLists n 64
    let results := columnLists.map fun cols =>
      checkPSDColumns neighbors certBytes n d c₁ c₂ c₃ cols
    let merged := results.foldl PSDChunkResult.merge init
    merged.epsMax = epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ n ∧
    merged.minDiag = minDiagVal rotBytes certBytes n d c₁ c₂ c₃ n ∧
    merged.first = false := by
  -- Introduce let bindings
  intro neighbors _ init columnLists results merged
  -- Bridge merged (Array.foldl) to List.foldl form
  have hmerged_eq : merged = results.toList.foldl PSDChunkResult.merge init :=
    (Array.foldl_toList _ (xs := results)).symm
  -- Key sizes
  have hcl_size : columnLists.size = 64 := buildColumnLists_size n 64 (by omega)
  have hres_size : results.size = 64 := by
    show (columnLists.map _).size = 64; rw [Array.size_map]; exact hcl_size
  -- Bridge getElem! to getElem for columnLists
  have hcl_getElem : ∀ i (hi : i < 64),
      (buildColumnLists n 64)[i]! = columnLists[i]'(by rw [hcl_size]; exact hi) :=
    fun i hi => getElem!_eq_getElem columnLists i (by rw [hcl_size]; exact hi)
  -- Each result[i] = foldl step init over columnLists[i].toList
  have hresult_eq : ∀ i (hi : i < results.size),
      results[i] = (columnLists[i]'(by rw [hcl_size]; omega)).toList.foldl
        (stepFn rotBytes certBytes n d c₁ c₂ c₃) init := by
    intro i hi
    show (columnLists.map _)[i] = _
    rw [Array.getElem_map]; exact checkPSDColumns_eq_listFoldl _ certBytes n d c₁ c₂ c₃ _
  -- Column bounds: entries in each chunk are < n
  have hcol_bound : ∀ i (hi : i < 64),
      ∀ j ∈ (columnLists[i]'(by rw [hcl_size]; exact hi)).toList, j < n := by
    intro i hi j hj
    rw [← hcl_getElem i hi] at hj
    exact buildColumnLists_bound n 64 i (by omega) j hj hi
  -- Coverage: every j < n is in chunk j % 64
  have hcoverage : ∀ j, j < n →
      j ∈ (columnLists[j % 64]'(by rw [hcl_size]; exact Nat.mod_lt j (by omega))).toList := by
    intro j hj
    rw [← hcl_getElem (j % 64) (Nat.mod_lt j (by omega))]
    exact buildColumnLists_mem n 64 j hj (by omega)
  -- Chunk 0 is nonempty (has column 0)
  have hchunk0_ne : (columnLists[0]'(by rw [hcl_size]; omega)).toList ≠ [] := by
    intro hempty
    have h0 := hcoverage 0 hn
    simp only [Nat.zero_mod] at h0
    rw [hempty] at h0
    exact absurd h0 (List.not_mem_nil)
  -- init.epsMax = 0
  have hinit_eps : (0 : Int) ≤ init.epsMax := by show (0 : Int) ≤ 0; omega
  -- Each chunk result has epsMax ≤ epsMaxVal n
  have hchunk_eps_le : ∀ i (hi : i < results.size),
      results[i].epsMax ≤ epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ n := by
    intro i hi; rw [hresult_eq i hi]
    exact foldl_step_epsMax_le rotBytes certBytes n d c₁ c₂ c₃ hd hinv _ _
      (hcol_bound i (by omega)) hinit_eps (epsMaxVal_nonneg _ _ _ _ _ _ _ _)
  -- Chunk 0 has first = false
  have hchunk0_first : results[0].first = false := by
    rw [hresult_eq 0 (by omega)]
    exact foldl_step_not_first rotBytes certBytes n d c₁ c₂ c₃ hd hinv _ _
      (hcol_bound 0 (by omega)) hinit_eps hchunk0_ne
  -- merged.first = false
  have hmerged_first : (results.toList.foldl PSDChunkResult.merge init).first = false :=
    mergeFoldl_not_first results 0 (by omega) hchunk0_first
  -- merged.epsMax ≤ epsMaxVal n
  have heps_le : (results.toList.foldl PSDChunkResult.merge init).epsMax ≤
      epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ n :=
    mergeFoldl_epsMax_le results _ (epsMaxVal_nonneg _ _ _ _ _ _ _ _) hchunk_eps_le
  -- merged.epsMax ≥ epsMaxVal n (sandwich)
  have heps_ge : epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ n ≤
      (results.toList.foldl PSDChunkResult.merge init).epsMax := by
    apply epsMaxVal_le_of_bounds
    · -- 0 ≤ merged.epsMax: chunk 0 epsMax ≥ 0 and merged ≥ chunk 0
      exact Int.le_trans (by
        rw [hresult_eq 0 (by omega)]
        exact foldl_step_epsMax_mono _ _ _ _ _ _ _ hd hinv _ _
          (hcol_bound 0 (by omega)) hinit_eps)
        (mergeFoldl_epsMax_ge results 0 (by omega) hchunk0_first)
    · intro j hj
      have hmod : j % 64 < results.size := by omega
      have hj_in := hcoverage j hj
      have hchunk_nf : results[j % 64].first = false := by
        rw [hresult_eq (j % 64) hmod]
        exact foldl_step_not_first _ _ _ _ _ _ _ hd hinv _ _
          (hcol_bound (j % 64) (by omega)) hinit_eps
          (by intro h; rw [h] at hj_in; exact absurd hj_in (List.not_mem_nil))
      exact Int.le_trans (by
        rw [hresult_eq (j % 64) hmod]
        exact foldl_step_epsMax_ge _ _ _ _ _ _ _ hd hinv _ _
          (hcol_bound (j % 64) (by omega)) hinit_eps hj_in)
        (mergeFoldl_epsMax_ge results (j % 64) hmod hchunk_nf)
  -- merged.minDiag ≥ minDiagVal n
  have hmin_ge : minDiagVal rotBytes certBytes n d c₁ c₂ c₃ n ≤
      (results.toList.foldl PSDChunkResult.merge init).minDiag := by
    apply (mergeFoldl_minDiag_ge results _ (fun i hi hif => ?_)) hmerged_first
    rw [hresult_eq i hi] at hif ⊢
    have hne : (columnLists[i]'(by rw [hcl_size]; omega)).toList ≠ [] := by
      intro h; rw [h] at hif; simp [List.foldl] at hif
    exact foldl_step_minDiag_ge _ _ _ _ _ _ _ hd hinv _ _
      (hcol_bound i (by omega)) hinit_eps hn hne (Or.inl rfl)
  -- merged.minDiag ≤ minDiagVal n (sandwich)
  have hmin_le : (results.toList.foldl PSDChunkResult.merge init).minDiag ≤
      minDiagVal rotBytes certBytes n d c₁ c₂ c₃ n := by
    apply le_minDiagVal_of_bounds
    · omega
    · intro j hj
      have hmod : j % 64 < results.size := by omega
      have hj_in := hcoverage j hj
      have hchunk_nf : results[j % 64].first = false := by
        rw [hresult_eq (j % 64) hmod]
        exact foldl_step_not_first _ _ _ _ _ _ _ hd hinv _ _
          (hcol_bound (j % 64) (by omega)) hinit_eps
          (by intro h; rw [h] at hj_in; exact absurd hj_in (List.not_mem_nil))
      calc (results.toList.foldl PSDChunkResult.merge init).minDiag
        ≤ results[j % 64].minDiag := mergeFoldl_minDiag_le results (j % 64) hmod hchunk_nf
        _ ≤ pEntryPure _ _ _ _ _ _ _ j j := by
              rw [hresult_eq (j % 64) hmod]
              exact foldl_step_minDiag_le _ _ _ _ _ _ _ hd hinv _ _
                (hcol_bound (j % 64) (by omega)) hinit_eps hj_in
  rw [hmerged_eq]
  exact ⟨Int.le_antisymm heps_le heps_ge, Int.le_antisymm hmin_le hmin_ge, hmerged_first⟩


/-! **Main bridge theorem** -/

/-- `checkColumnNormBound = true` implies `checkColumnNormBoundPure = true`.
    Both compute the same `epsMax`, `minDiag` via `pEntryPure`-equivalent
    computations, then call `checkPerRow` identically. -/
theorem checkColumnNormBound_implies_pure
    (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (h : checkColumnNormBound rotBytes certBytes n d c₁ c₂ c₃ = true)
    (hinv : ∀ k, k < n * d → decodeBase85Nat rotBytes (2 * k) < n)
    (hn : 0 < n) (hd : 0 < d) :
    checkColumnNormBoundPure rotBytes certBytes n d c₁ c₂ c₃ = true := by
  -- Get the merged values equality (heps/hmin/hfirst are in Array.foldl form)
  have hseq := merged_eq_sequential rotBytes certBytes n d c₁ c₂ c₃ hd hn hinv
  obtain ⟨heps, hmin, hfirst⟩ := hseq
  -- Unfold checkColumnNormBound at h to extract checkPerRow
  unfold checkColumnNormBound at h
  -- Handle certBytes size check
  split at h
  · simp at h
  · -- merged.first check: hfirst says it's false
    simp only [hfirst] at h
    -- h: checkPerRow certBytes n merged.epsMax (merged.minDiag + merged.epsMax) n 0 0 = true
    -- Goal: checkColumnNormBoundPure ... = true
    unfold checkColumnNormBoundPure
    -- Handle n == 0 check: n ≠ 0 since hn : 0 < n
    have hnn : (n == 0) = false := by cases n with | zero => omega | succ _ => rfl
    simp only [hnn]
    -- Goal: checkPerRow certBytes n (epsMaxVal ...) (minDiagVal ... + epsMaxVal ...) n 0 0 = true
    rw [← heps, ← hmin]
    exact h

