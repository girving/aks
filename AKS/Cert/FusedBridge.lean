/-
  # Fused Bridge: `checkPSDColumnsFull` ↔ `checkPSDColumns`

  Proves that the fused PSD + column-norm computation in `checkPSDColumnsFull`
  produces the same PSD state as the unfused `checkPSDColumns`, and that the
  norm outputs match `zColNormPure`. Used by `FastProof.lean` to close
  `checkCertificate_eq_slow`.

  The new `checkPSDColumnsFull` uses scatter-based adjacency multiplication
  and buffer reuse. Under `NeighborSymm` (derived from `checkInvolution`),
  scatter = gather, and the ghost state (reused buffers) doesn't affect output.
-/

import CertCheck
import AKS.Misc.ForLoop
import AKS.Cert.ColumnNormBridge
import AKS.Cert.ScatterBridge

/-! **Fused decode step functions** -/

/-- Step function for the fused 3-variable decode loop (MProd version).
    Lean's do-block desugaring bundles `(arr, s, norm)` as
    `MProd (Array Int) (MProd Int Int)` with order `⟨arr, norm, s⟩`
    (last-declared variable is innermost). -/
private def fusedStepM (certBytes : ByteArray) (colStart : Nat) (k : Nat)
    (r : MProd (Array Int) (MProd Int Int)) : MProd (Array Int) (MProd Int Int) :=
  ⟨r.fst.set! k (decodeBase85Int certBytes (colStart + k)),
   r.snd.fst + intAbs (decodeBase85Int certBytes (colStart + k)),
   r.snd.snd + decodeBase85Int certBytes (colStart + k)⟩

/-- Step function on Prod `(arr, s, norm)` for reasoning. -/
private def fusedStepP (certBytes : ByteArray) (colStart : Nat) (k : Nat)
    (p : Array Int × Int × Int) : Array Int × Int × Int :=
  let v := decodeBase85Int certBytes (colStart + k)
  (p.1.set! k v, p.2.1 + v, p.2.2 + intAbs v)

/-! **MProd/Prod correspondence** -/

/-- MProd `⟨arr, norm, s⟩` corresponds to Prod `(arr, s, norm)` (swapped). -/
private def Corr3 {α β γ : Type} (m : MProd α (MProd β γ)) (p : α × γ × β) : Prop :=
  m.fst = p.1 ∧ m.snd.fst = p.2.2 ∧ m.snd.snd = p.2.1

private theorem fusedStep_corr (certBytes : ByteArray) (colStart k : Nat)
    (m : MProd (Array Int) (MProd Int Int)) (p : Array Int × Int × Int)
    (h : Corr3 m p) :
    Corr3 (fusedStepM certBytes colStart k m) (fusedStepP certBytes colStart k p) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [fusedStepM, fusedStepP, Corr3]
  exact ⟨by rw [h1], by rw [h2], by rw [h3]⟩

private theorem fold_corr3 {α β γ : Type}
    {step_m : Nat → MProd α (MProd β γ) → MProd α (MProd β γ)}
    {step_p : Nat → α × γ × β → α × γ × β}
    (hstep : ∀ k m p, Corr3 m p → Corr3 (step_m k m) (step_p k p))
    {init_m : MProd α (MProd β γ)} {init_p : α × γ × β}
    (hinit : Corr3 init_m init_p) (n : Nat) :
    Corr3 (Nat.fold n (fun k _ s => step_m k s) init_m)
           (Nat.fold n (fun k _ s => step_p k s) init_p) := by
  induction n with
  | zero => exact hinit
  | succ n ih => simp only [Nat.fold_succ]; exact hstep n _ _ ih

/-! **Fused do-block = Nat.fold on Prod** -/

/-- The body after `simp` is definitionally `ForInStep.yield (fusedStepM ...)`. -/
private theorem fusedBody_M (certBytes : ByteArray) (colStart k : Nat)
    (r : MProd (Array Int) (MProd Int Int)) :
    ForInStep.yield
      ⟨r.fst.set! k (decodeBase85Int certBytes (colStart + k)),
        r.snd.fst + intAbs (decodeBase85Int certBytes (colStart + k)),
        r.snd.snd + decodeBase85Int certBytes (colStart + k)⟩ =
    ForInStep.yield (fusedStepM certBytes colStart k r) := rfl

/-- The fused 3-variable decode loop equals `Nat.fold` with `fusedStepP`. -/
private theorem fusedDecode_eq_fold (certBytes : ByteArray) (n : Nat) (colStart j : Nat) :
    (Id.run do
      let mut arr := Array.replicate n (0 : Int)
      let mut s : Int := 0
      let mut norm : Int := 0
      for k in [:j+1] do
        let v := decodeBase85Int certBytes (colStart + k)
        arr := arr.set! k v
        s := s + v
        norm := norm + intAbs v
      return (arr, s, norm)) =
    Nat.fold (j + 1) (fun k _ s => fusedStepP certBytes colStart k s)
      (Array.replicate n 0, 0, 0) := by
  simp only [Id.run, bind, pure, Std.Range.forIn_eq_forIn_range', Std.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  have hbody_ext : (fun k (r : MProd (Array Int) (MProd Int Int)) =>
      ForInStep.yield
        ⟨r.fst.set! k (decodeBase85Int certBytes (colStart + k)),
          r.snd.fst + intAbs (decodeBase85Int certBytes (colStart + k)),
          r.snd.snd + decodeBase85Int certBytes (colStart + k)⟩) =
      (fun k r => ForInStep.yield (fusedStepM certBytes colStart k r)) :=
    funext fun k => funext fun r => fusedBody_M certBytes colStart k r
  rw [hbody_ext, forIn_range'_eq_fold (fusedStepM certBytes colStart)]
  simp only [Nat.zero_add]
  have corr := fold_corr3 (fusedStep_corr certBytes colStart)
    (⟨rfl, rfl, rfl⟩ : Corr3
      (⟨Array.replicate n (0:Int), (0:Int), (0:Int)⟩ : MProd _ (MProd _ _))
      ((Array.replicate n (0:Int), (0:Int), (0:Int)) : _ × _ × _))
    (j + 1)
  obtain ⟨c1, c2, c3⟩ := corr
  set mr := Nat.fold (j + 1) (fun k _ s => fusedStepM certBytes colStart k s)
    ⟨Array.replicate n (0:Int), (0:Int), (0:Int)⟩
  set pr := Nat.fold (j + 1) (fun k _ s => fusedStepP certBytes colStart k s)
    (Array.replicate n (0:Int), (0:Int), (0:Int))
  show (mr.fst, mr.snd.snd, mr.snd.fst) = pr
  exact Prod.ext c1 (Prod.ext c3 c2)

/-! **Fold projection lemmas** -/

private theorem fusedStepP_fst (certBytes : ByteArray) (colStart k : Nat)
    (s : Array Int × Int × Int) :
    (fusedStepP certBytes colStart k s).1 =
    s.1.set! k (decodeBase85Int certBytes (colStart + k)) := rfl

private theorem fusedStepP_snd_fst (certBytes : ByteArray) (colStart k : Nat)
    (s : Array Int × Int × Int) :
    (fusedStepP certBytes colStart k s).2.1 =
    s.2.1 + decodeBase85Int certBytes (colStart + k) := rfl

private theorem fusedStepP_snd_snd (certBytes : ByteArray) (colStart k : Nat)
    (s : Array Int × Int × Int) :
    (fusedStepP certBytes colStart k s).2.2 =
    s.2.2 + intAbs (decodeBase85Int certBytes (colStart + k)) := rfl

/-- `.1` of the fused fold = array-only fold (same as unfused `zCol`). -/
private theorem fusedFold_arr (certBytes : ByteArray) (colStart n j : Nat) :
    (Nat.fold (j + 1) (fun k _ s => fusedStepP certBytes colStart k s)
      (Array.replicate n (0 : Int), (0 : Int), (0 : Int))).1 =
    Nat.fold (j + 1) (fun k _ arr =>
      arr.set! k (decodeBase85Int certBytes (colStart + k)))
      (Array.replicate n (0 : Int)) := by
  suffices h : ∀ m (s : Array Int × Int × Int),
      (Nat.fold m (fun k _ s => fusedStepP certBytes colStart k s) s).1 =
      Nat.fold m (fun k _ arr => arr.set! k (decodeBase85Int certBytes (colStart + k))) s.1 from
    h (j + 1) _
  intro m; induction m with
  | zero => intro; rfl
  | succ m ih =>
    intro s
    simp only [Nat.fold_succ, fusedStepP_fst]
    exact congrArg (fun a => a.set! m (decodeBase85Int certBytes (colStart + m))) (ih s)

/-- `.2.1` of the fused fold = sum fold (sum of decoded values). -/
private theorem fusedFold_sum (certBytes : ByteArray) (colStart n j : Nat) :
    (Nat.fold (j + 1) (fun k _ s => fusedStepP certBytes colStart k s)
      (Array.replicate n (0 : Int), (0 : Int), (0 : Int))).2.1 =
    Nat.fold (j + 1) (fun k _ acc => acc + decodeBase85Int certBytes (colStart + k)) 0 := by
  suffices h : ∀ m (s : Array Int × Int × Int),
      (Nat.fold m (fun k _ s => fusedStepP certBytes colStart k s) s).2.1 =
      Nat.fold m (fun k _ acc => acc + decodeBase85Int certBytes (colStart + k)) s.2.1 from
    h (j + 1) _
  intro m; induction m with
  | zero => intro; rfl
  | succ m ih =>
    intro s
    simp only [Nat.fold_succ, fusedStepP_snd_fst]
    exact congrArg (· + decodeBase85Int certBytes (colStart + m)) (ih s)

/-- `.2.2` of the fused fold = norm fold (sum of |decoded values|). -/
private theorem fusedFold_norm (certBytes : ByteArray) (colStart n j : Nat) :
    (Nat.fold (j + 1) (fun k _ s => fusedStepP certBytes colStart k s)
      (Array.replicate n (0 : Int), (0 : Int), (0 : Int))).2.2 =
    Nat.fold (j + 1) (fun k _ acc =>
      acc + intAbs (decodeBase85Int certBytes (colStart + k))) 0 := by
  suffices h : ∀ m (s : Array Int × Int × Int),
      (Nat.fold m (fun k _ s => fusedStepP certBytes colStart k s) s).2.2 =
      Nat.fold m (fun k _ acc => acc + intAbs (decodeBase85Int certBytes (colStart + k))) s.2.2
    from h (j + 1) _
  intro m; induction m with
  | zero => intro; rfl
  | succ m ih =>
    intro s
    simp only [Nat.fold_succ, fusedStepP_snd_snd]
    exact congrArg (· + intAbs (decodeBase85Int certBytes (colStart + m))) (ih s)

/-! **Component lemmas: fused decode components = unfused components** -/

/-- The fused decode's array `.1` = the unfused single-variable decode array. -/
private theorem fused_arr_eq_unfused (certBytes : ByteArray) (n colStart j : Nat) :
    (Id.run do
      let mut arr := Array.replicate n (0 : Int)
      let mut s : Int := 0
      let mut norm : Int := 0
      for k in [:j+1] do
        let v := decodeBase85Int certBytes (colStart + k)
        arr := arr.set! k v; s := s + v; norm := norm + intAbs v
      return (arr, s, norm)).1 =
    (Id.run do
      let mut arr := Array.replicate n (0 : Int)
      for k in [:j+1] do arr := arr.set! k (decodeBase85Int certBytes (colStart + k))
      return arr) := by
  rw [fusedDecode_eq_fold, fusedFold_arr, ← forIn_range_eq_fold]

/-- The fused decode's sum `.2.1` = direct `Nat.fold` sum of decoded values. -/
private theorem fused_sum_is_fold (certBytes : ByteArray) (n colStart j : Nat) :
    (Id.run do
      let mut arr := Array.replicate n (0 : Int)
      let mut s : Int := 0
      let mut norm : Int := 0
      for k in [:j+1] do
        let v := decodeBase85Int certBytes (colStart + k)
        arr := arr.set! k v; s := s + v; norm := norm + intAbs v
      return (arr, s, norm)).2.1 =
    Nat.fold (j + 1) (fun k _ acc => acc + decodeBase85Int certBytes (colStart + k)) 0 := by
  rw [fusedDecode_eq_fold, fusedFold_sum]

/-- The unfused `colSum` (sum of `zCol[k]!`) equals the direct `Nat.fold` sum. -/
private theorem unfused_colSum_eq_fold (certBytes : ByteArray) (n j : Nat) (hj : j < n) :
    (Id.run do
      let mut s : Int := 0
      for k in [:j+1] do s := s +
        (Id.run do
          let mut arr := Array.replicate n (0 : Int)
          for k in [:j+1] do arr := arr.set! k (decodeBase85Int certBytes (j * (j+1) / 2 + k))
          return arr)[k]!
      return s) =
    Nat.fold (j + 1) (fun k _ acc => acc + decodeBase85Int certBytes (j * (j + 1) / 2 + k)) 0 := by
  rw [forIn_range_eq_fold]
  erw [forIn_range_eq_fold]
  symm
  apply fold_sum_congr
  intro k hk
  exact (fold_set_getD (fun i => decodeBase85Int certBytes (j * (j + 1) / 2 + i))
    n (j + 1) (by omega) k hk).symm

/-- The fused decode's norm `.2.2` = `Nat.fold` sum of `intAbs` of decoded values. -/
private theorem fused_norm_is_fold (certBytes : ByteArray) (n colStart j : Nat) :
    (Id.run do
      let mut arr := Array.replicate n (0 : Int)
      let mut s : Int := 0
      let mut norm : Int := 0
      for k in [:j+1] do
        let v := decodeBase85Int certBytes (colStart + k)
        arr := arr.set! k v; s := s + v; norm := norm + intAbs v
      return (arr, s, norm)).2.2 =
    Nat.fold (j + 1) (fun k _ acc =>
      acc + intAbs (decodeBase85Int certBytes (colStart + k))) 0 := by
  rw [fusedDecode_eq_fold, fusedFold_norm]

/-! **Per-column step (gather-based, for bridge reasoning)** -/

/-- Per-column step that fuses PSD + norm computation using GATHER (mulAdjPre).
    This is the old `psdColumnStepFull` from CertCheck.lean, moved here for
    bridge reasoning. Under `NeighborSymm`, the new scatter-based
    `checkPSDColumnsFull` produces the same per-column results. -/
private def psdColumnStepFull (neighbors : Array Nat) (d : Nat)
    (certBytes : ByteArray) (n : Nat) (c₁ c₂ c₃ : Int)
    (state : PSDChunkResult) (j : Nat) : PSDChunkResult × Int :=
  let colStart := j * (j + 1) / 2
  let (zCol, colSum, colNorm) := Id.run do
    let mut arr := Array.replicate n (0 : Int)
    let mut s : Int := 0
    let mut norm : Int := 0
    for k in [:j+1] do
      let v := decodeBase85Int certBytes (colStart + k)
      arr := arr.set! k v; s := s + v; norm := norm + intAbs v
    return (arr, s, norm)
  let bz := mulAdjPre neighbors zCol n d
  let newState := Id.run do
    let mut epsMax := state.epsMax
    let mut minDiag := state.minDiag
    let mut first := state.first
    for i in [:j+1] do
      let pij := c₁ * zCol[i]! - c₂ * mulAdjEntry neighbors bz d i + c₃ * colSum
      if i == j then
        if first then minDiag := pij; first := false
        else if pij < minDiag then minDiag := pij
      else if i < j then
        let absPij := if pij >= 0 then pij else -pij
        if absPij > epsMax then epsMax := absPij
    return { epsMax, minDiag, first }
  (newState, colNorm)

/-! **Per-column bridges** -/

set_option maxHeartbeats 800000 in
/-- The fused per-column step's PSD result `.1` equals the unfused `psdColumnStep`. -/
theorem psdColumnStepFull_fst (neighbors : Array Nat) (d : Nat)
    (certBytes : ByteArray) (n : Nat) (c₁ c₂ c₃ : Int)
    (state : PSDChunkResult) (j : Nat) (hj : j < n) :
    (psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ state j).1 =
    psdColumnStep neighbors d certBytes n c₁ c₂ c₃ state j := by
  simp only [psdColumnStepFull, psdColumnStep, fused_arr_eq_unfused, fused_sum_is_fold]
  erw [unfused_colSum_eq_fold certBytes n j hj]

set_option maxHeartbeats 800000 in
/-- The fused per-column step's norm output `.2` equals `zColNormPure`. -/
theorem psdColumnStepFull_snd (neighbors : Array Nat) (d : Nat)
    (certBytes : ByteArray) (n : Nat) (c₁ c₂ c₃ : Int)
    (state : PSDChunkResult) (j : Nat) (hj : j < n) :
    (psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ state j).2 =
    zColNormPure certBytes n j := by
  simp only [psdColumnStepFull]
  rw [fused_norm_is_fold]
  simp only [zColNormPure]
  rw [sumTo_tail_zero _ (j + 1) n (by omega)
    (fun l hl1 _ => by simp [certEntryInt, intAbs, show ¬(l ≤ j) from by omega])]
  rw [sumTo_eq_fold]
  symm
  apply fold_sum_congr
  intro k hk
  simp only [certEntryInt, show k ≤ j from by omega, ite_true]

/-! **Loop-level bridges** -/

/-- `forIn` on a list with yield = `List.foldl`. -/
private theorem list_forIn_yield_foldl {α β : Type} (l : List α) (init : β) (f : β → α → β) :
    (forIn (m := Id) l init (fun x s => ForInStep.yield (f s x))) = l.foldl f init := by
  induction l generalizing init with
  | nil => simp only [forIn, ForIn.forIn, List.forIn'_nil, List.foldl, pure]
  | cons x xs ih =>
    simp only [forIn, ForIn.forIn, List.forIn'_cons, List.foldl, bind]
    exact ih (f init x)

/-- `checkPSDColumns` as `List.foldl`. -/
private theorem checkPSDColumns_foldl (neighbors : Array Nat)
    (certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int) (cols : Array Nat) :
    checkPSDColumns neighbors certBytes n d c₁ c₂ c₃ cols =
    cols.toList.foldl (psdColumnStep neighbors d certBytes n c₁ c₂ c₃)
      { epsMax := 0, minDiag := 0, first := true } := by
  unfold checkPSDColumns; simp only [Id.run, bind, pure]
  rw [show forIn cols _ _ = forIn cols.toList _ _ from (Array.forIn_toList).symm]
  exact list_forIn_yield_foldl cols.toList _ _

/-- Swapped MProd fold corresponds to Prod fold. -/
private theorem foldl_mprod_swap {α β γ : Type}
    (step_m : MProd α β → γ → MProd α β)
    (step_p : β × α → γ → β × α)
    (hstep : ∀ j (m : MProd α β),
      (step_m m j).fst = (step_p (m.snd, m.fst) j).2 ∧
      (step_m m j).snd = (step_p (m.snd, m.fst) j).1)
    (init_m : MProd α β) (l : List γ) :
    let r := l.foldl step_m init_m
    r.snd = (l.foldl step_p (init_m.snd, init_m.fst)).1 ∧
    r.fst = (l.foldl step_p (init_m.snd, init_m.fst)).2 := by
  induction l generalizing init_m with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [show step_p (init_m.snd, init_m.fst) x =
      ((step_m init_m x).snd, (step_m init_m x).fst) from
        Prod.ext (hstep x init_m).2.symm (hstep x init_m).1.symm]
    exact ih (step_m init_m x)

/-! **`checkPSDColumnsFull` loop decomposition (under symmetry)** -/

/-! **Full state type and projection** -/

/-- Full mutable state of the `checkPSDColumnsFull` loop:
    `⟨bz, colNorms, epsMax, first, minDiag, zCol⟩`. -/
private abbrev FullState :=
  MProd (Array Int) (MProd (Array Int) (MProd Int (MProd Bool (MProd Int (Array Int)))))

/-- Generic `forIn`-to-`foldl` conversion for yield-only bodies:
    if the body always yields and projection commutes with each step,
    then `proj (forIn l init body) = l.foldl smallStep (proj init)`.
    Unlike type-specialized rewrites, this applies directly via `apply`
    and avoids matching inner `forIn`s. -/
private theorem forIn_yield_proj {S P : Type} (l : List Nat) (init : S)
    (body : Nat → S → Id (ForInStep S)) (proj : S → P) (smallStep : P → Nat → P)
    (hyield : ∀ j s, ∃ r, body j s = ForInStep.yield r)
    (hproj : ∀ j s r, body j s = ForInStep.yield r → proj r = smallStep (proj s) j) :
    proj (forIn (m := Id) l init body) = l.foldl smallStep (proj init) := by
  induction l generalizing init with
  | nil => simp [forIn, ForIn.forIn, List.forIn'_nil, pure]
  | cons x xs ih =>
    simp only [forIn, ForIn.forIn, List.forIn'_cons, bind, List.foldl_cons]
    obtain ⟨r, hr⟩ := hyield x init
    rw [show body x init = ForInStep.yield r from hr]
    show proj (forIn (m := Id) xs r body) = _
    rw [ih r, hproj x init r hr]

/-- Project `FullState` to the visible output `(PSDChunkResult, colNorms)`. -/
private def projFull (r : FullState) : PSDChunkResult × Array Int :=
  ({ epsMax := r.snd.snd.fst,
     minDiag := r.snd.snd.snd.snd.fst,
     first := r.snd.snd.snd.fst }, r.snd.fst)

/-! **Ghost state elimination infrastructure** -/

/-- Size preservation for zeroing fold. -/
private theorem zero_fold_size (arr : Array Int) (n : Nat) :
    (Nat.fold n (fun i _ a => a.setIfInBounds i 0) arr).size = arr.size := by
  induction n generalizing arr with
  | zero => simp [Nat.fold_zero]
  | succ k ih =>
    rw [Nat.fold_succ, Array.size_setIfInBounds]; exact ih _

/-- Zeroing fold: positions `< n` become `0`, rest unchanged. -/
private theorem zero_fold_getElem? (arr : Array Int) (n : Nat) (h : n ≤ arr.size) (v : Nat) :
    (Nat.fold n (fun i _ a => a.setIfInBounds i 0) arr)[v]? =
    if v < n then some 0 else arr[v]? := by
  induction n generalizing arr with
  | zero =>
    simp only [Nat.fold_zero]; rw [if_neg (by omega)]
  | succ k ih =>
    rw [Nat.fold_succ, Array.getElem?_setIfInBounds]
    by_cases hkv : k = v
    · subst hkv
      rw [if_pos rfl, if_pos (by rw [zero_fold_size]; omega)]
      simp [show k < k + 1 from by omega]
    · rw [if_neg hkv, ih _ (by omega)]
      by_cases hv : v < k
      · rw [if_pos hv, if_pos (by omega)]
      · rw [if_neg hv, if_neg (by omega)]

private theorem forIn_zero_eq_replicate (arr : Array Int) (n : Nat) (h : arr.size = n) :
    forIn (m := Id) (List.range' 0 n 1) arr
      (fun v (r : Array Int) => ForInStep.yield (r.set! v 0)) =
    Array.replicate n (0 : Int) := by
  rw [forIn_range'_eq_fold (fun v (a : Array Int) => a.set! v 0)]
  simp only [Nat.zero_add]
  show Nat.fold n (fun v _ a => a.setIfInBounds v 0) arr = Array.replicate n 0
  apply Array.ext_getElem?; intro i
  rw [zero_fold_getElem? arr n (by omega)]
  simp only [Array.getElem?_replicate]
  by_cases hi : i < n
  · rw [if_pos hi, if_pos hi]
  · rw [if_neg hi, if_neg hi]; simp [show ¬(i < arr.size) from by omega]

/-! **Decode+scatter loop body and independence** -/

/-- MProd state for the fused 4-var decode+scatter loop:
    `⟨bz, colNorm, colSum, zCol⟩`. -/
private abbrev DS4 := MProd (Array Int) (MProd Int (MProd Int (Array Int)))

/-- Body of the 4-var decode+scatter inner loop. -/
private def ds4Body (neighbors : Array Nat) (d : Nat)
    (certBytes : ByteArray) (colStart : Nat)
    (k : Nat) (r : DS4) : ForInStep DS4 :=
  let zk := decodeBase85Int certBytes (colStart + k)
  ForInStep.yield
    ⟨forIn (m := Id) (List.range' 0 d 1) r.fst (fun p bz =>
        ForInStep.yield (bz.set! neighbors[k * d + p]! (bz[neighbors[k * d + p]!]! + zk))),
     r.snd.fst + intAbs zk,
     r.snd.snd.fst + zk,
     r.snd.snd.snd.set! k zk⟩

/-- The first 3 components `(bz, colNorm, colSum)` of the decode+scatter result
    are independent of the initial `zCol`. -/
private theorem ds4_proj3_independent
    (neighbors : Array Nat) (d : Nat) (certBytes : ByteArray) (colStart : Nat)
    (l : List Nat) (bz : Array Int) (cn cs : Int) (zCol1 zCol2 : Array Int) :
    let r1 := forIn (m := Id) l ⟨bz, cn, cs, zCol1⟩ (ds4Body neighbors d certBytes colStart)
    let r2 := forIn (m := Id) l ⟨bz, cn, cs, zCol2⟩ (ds4Body neighbors d certBytes colStart)
    r1.fst = r2.fst ∧ r1.snd.fst = r2.snd.fst ∧ r1.snd.snd.fst = r2.snd.snd.fst := by
  induction l generalizing bz cn cs zCol1 zCol2 with
  | nil => simp [forIn, ForIn.forIn, List.forIn'_nil, pure]
  | cons x xs ih =>
    simp only [forIn, ForIn.forIn, List.forIn'_cons, bind, ds4Body]
    exact ih _ _ _ (zCol1.set! x _) (zCol2.set! x _)

/-- The `zCol` component of the decode+scatter result factors as an independent fold. -/
private theorem ds4_zCol_component
    (neighbors : Array Nat) (d : Nat) (certBytes : ByteArray) (colStart : Nat)
    (l : List Nat) (bz : Array Int) (cn cs : Int) (zCol : Array Int) :
    (forIn (m := Id) l ⟨bz, cn, cs, zCol⟩ (ds4Body neighbors d certBytes colStart)).snd.snd.snd =
    forIn (m := Id) l zCol (fun k (z : Array Int) =>
      ForInStep.yield (z.set! k (decodeBase85Int certBytes (colStart + k)))) := by
  induction l generalizing bz cn cs zCol with
  | nil => simp [forIn, ForIn.forIn, List.forIn'_nil, pure]
  | cons x xs ih =>
    simp only [forIn, ForIn.forIn, List.forIn'_cons, bind, ds4Body]
    exact ih _ _ _ _

/-- Size preservation for arbitrary fold-set. -/
private theorem fold_setD_size (g : Nat → Int) (arr : Array Int) (m : Nat) :
    (Nat.fold m (fun i _ a => a.setIfInBounds i (g i)) arr).size = arr.size := by
  induction m generalizing arr with
  | zero => simp [Nat.fold_zero]
  | succ k ih =>
    rw [Nat.fold_succ, Array.size_setIfInBounds]; exact ih _

/-- `getElem?` characterization for fold-set on arbitrary array:
    positions `< m` get `g v`, rest unchanged. -/
private theorem fold_setD_getElem? (g : Nat → Int) (arr : Array Int) (m : Nat)
    (hm : m ≤ arr.size) (v : Nat) :
    (Nat.fold m (fun i _ a => a.setIfInBounds i (g i)) arr)[v]? =
    if v < m then some (g v) else arr[v]? := by
  induction m generalizing arr with
  | zero =>
    simp only [Nat.fold_zero]; rw [if_neg (by omega)]
  | succ k ih =>
    rw [Nat.fold_succ, Array.getElem?_setIfInBounds]
    by_cases hkv : k = v
    · subst hkv
      rw [if_pos rfl, if_pos (by rw [fold_setD_size]; omega)]
      simp [show k < k + 1 from by omega]
    · rw [if_neg hkv, ih _ (by omega)]
      by_cases hv : v < k
      · rw [if_pos hv, if_pos (by omega)]
      · rw [if_neg hv, if_neg (by omega)]

/-- `getD` for fold-set on arbitrary array at set positions. -/
private theorem fold_setD_getD (g : Nat → Int) (arr : Array Int) (m : Nat)
    (hm : m ≤ arr.size) (k : Nat) (hk : k < m) :
    (Nat.fold m (fun i _ a => a.setIfInBounds i (g i)) arr).getD k 0 = g k := by
  have h := fold_setD_getElem? g arr m hm k
  rw [if_pos hk] at h
  show (if _ : k < _ then _ else 0) = g k
  rw [dif_pos (by rw [fold_setD_size]; omega)]
  exact Option.some.inj (by rw [Array.getElem?_eq_getElem (by rw [fold_setD_size]; omega)] at h; exact h)

/-- After decode+scatter, `zCol[i]!` = `decode(colStart + i)` for `i < j+1`,
    regardless of the initial `zCol` (as long as it has size `≥ j+1`). -/
private theorem ds4_zCol_getD
    (neighbors : Array Nat) (d : Nat) (certBytes : ByteArray) (colStart : Nat)
    (j : Nat) (bz : Array Int) (cn cs : Int) (zCol : Array Int) (hsize : zCol.size ≥ j + 1)
    (i : Nat) (hi : i < j + 1) :
    (forIn (m := Id) (List.range' 0 (j + 1) 1) ⟨bz, cn, cs, zCol⟩
      (ds4Body neighbors d certBytes colStart)).snd.snd.snd.getD i 0 =
    decodeBase85Int certBytes (colStart + i) := by
  rw [ds4_zCol_component]
  rw [forIn_range'_eq_fold
    (fun k (z : Array Int) => z.set! k (decodeBase85Int certBytes (colStart + k)))]
  simp only [Nat.zero_add]
  show (Nat.fold (j + 1) (fun k _ z =>
    z.setIfInBounds k (decodeBase85Int certBytes (colStart + k))) zCol).getD i 0 = _
  exact fold_setD_getD (fun k => decodeBase85Int certBytes (colStart + k))
    zCol (j + 1) (by omega) i hi

/-! **Component factoring: ds4 individual projections** -/

/-- The `.fst` (bz) of ds4Body factors as an independent scatter fold. -/
private theorem ds4_fst_component
    (neighbors : Array Nat) (d : Nat) (certBytes : ByteArray) (colStart : Nat)
    (l : List Nat) (bz : Array Int) (cn cs : Int) (zCol : Array Int) :
    (forIn (m := Id) l ⟨bz, cn, cs, zCol⟩ (ds4Body neighbors d certBytes colStart)).fst =
    forIn (m := Id) l bz (fun k (bz' : Array Int) =>
      let zk := decodeBase85Int certBytes (colStart + k)
      ForInStep.yield (forIn (m := Id) (List.range' 0 d 1) bz' (fun p bz'' =>
        ForInStep.yield (bz''.set! neighbors[k * d + p]! (bz''[neighbors[k * d + p]!]! + zk))))) := by
  induction l generalizing bz cn cs zCol with
  | nil => rfl
  | cons x xs ih =>
    simp only [forIn, ForIn.forIn, List.forIn'_cons, bind, ds4Body]
    exact ih _ _ _ _

/-- The `.snd.snd.fst` (colSum) of ds4Body factors as an independent sum fold. -/
private theorem ds4_colSum_component
    (neighbors : Array Nat) (d : Nat) (certBytes : ByteArray) (colStart : Nat)
    (l : List Nat) (bz : Array Int) (cn cs : Int) (zCol : Array Int) :
    (forIn (m := Id) l ⟨bz, cn, cs, zCol⟩ (ds4Body neighbors d certBytes colStart)).snd.snd.fst =
    forIn (m := Id) l cs (fun k (acc : Int) =>
      ForInStep.yield (acc + decodeBase85Int certBytes (colStart + k))) := by
  induction l generalizing bz cn cs zCol with
  | nil => rfl
  | cons x xs ih =>
    simp only [forIn, ForIn.forIn, List.forIn'_cons, bind, ds4Body]
    exact ih _ _ _ _

/-- The `.snd.fst` (colNorm) of ds4Body factors as an independent norm fold. -/
private theorem ds4_colNorm_component
    (neighbors : Array Nat) (d : Nat) (certBytes : ByteArray) (colStart : Nat)
    (l : List Nat) (bz : Array Int) (cn cs : Int) (zCol : Array Int) :
    (forIn (m := Id) l ⟨bz, cn, cs, zCol⟩ (ds4Body neighbors d certBytes colStart)).snd.fst =
    forIn (m := Id) l cn (fun k (acc : Int) =>
      ForInStep.yield (acc + intAbs (decodeBase85Int certBytes (colStart + k)))) := by
  induction l generalizing bz cn cs zCol with
  | nil => rfl
  | cons x xs ih =>
    simp only [forIn, ForIn.forIn, List.forIn'_cons, bind, ds4Body]
    exact ih _ _ _ _

/-! **Decoded column array** -/

/-- `arr[k]!` equals `arr.getD k 0` for `Array Int` (both default to 0 on OOB). -/
private theorem bang_eq_getD_int (arr : Array Int) (k : Nat) :
    arr[k]! = arr.getD k 0 := by
  unfold Array.getD
  by_cases h : k < arr.size
  · simp only [h, dite_true]
    show (if h' : k < arr.size then arr[k] else default) = arr[k]
    rw [dif_pos h]
  · simp only [h, dite_false]
    show (if h' : k < arr.size then arr[k] else default) = 0
    rw [dif_neg h]; rfl

/-- The decoded column array: `replicate n 0` with positions `0..j` filled with
    `decode(colStart + i)`. This is the pure result of the zCol fold. -/
private def decodedZCol (certBytes : ByteArray) (colStart n j : Nat) : Array Int :=
  Nat.fold (j + 1) (fun i _ (a : Array Int) =>
    a.setIfInBounds i (decodeBase85Int certBytes (colStart + i)))
    (Array.replicate n (0 : Int))

set_option maxRecDepth 512 in
private theorem decodedZCol_size (certBytes : ByteArray) (colStart n j : Nat) :
    (decodedZCol certBytes colStart n j).size = n := by
  unfold decodedZCol; rw [fold_setD_size]; simp [Array.size_replicate]

private theorem decodedZCol_getD (certBytes : ByteArray) (colStart n j : Nat) (hj : j < n)
    (k : Nat) (hk : k < j + 1) :
    (decodedZCol certBytes colStart n j).getD k 0 =
    decodeBase85Int certBytes (colStart + k) := by
  unfold decodedZCol; unfold Array.getD
  rw [dif_pos (by rw [fold_setD_size, Array.size_replicate]; omega)]
  have h := fold_setD_getElem? (fun i => decodeBase85Int certBytes (colStart + i))
    (Array.replicate n 0) (j + 1) (by rw [Array.size_replicate]; omega) k
  rw [if_pos hk, Array.getElem?_eq_getElem (by rw [fold_setD_size, Array.size_replicate]; omega)] at h
  exact Option.some.inj h

private theorem decodedZCol_bang (certBytes : ByteArray) (colStart n j : Nat) (hj : j < n)
    (k : Nat) (hk : k < j + 1) :
    (decodedZCol certBytes colStart n j)[k]! =
    decodeBase85Int certBytes (colStart + k) := by
  rw [bang_eq_getD_int]; exact decodedZCol_getD certBytes colStart n j hj k hk

private theorem decodedZCol_zero (certBytes : ByteArray) (colStart n j : Nat) (hj : j < n)
    (k : Nat) (hk : k ≥ j + 1) :
    (decodedZCol certBytes colStart n j).getD k 0 = 0 := by
  unfold decodedZCol; unfold Array.getD
  by_cases hk2 : k < (Nat.fold (j + 1) (fun i _ a => a.setIfInBounds i
    (decodeBase85Int certBytes (colStart + i))) (Array.replicate n 0)).size
  · rw [dif_pos hk2]
    have h := fold_setD_getElem? (fun i => decodeBase85Int certBytes (colStart + i))
      (Array.replicate n 0) (j + 1) (by rw [Array.size_replicate]; omega) k
    rw [if_neg (by omega), Array.getElem?_replicate,
        if_pos (by rw [fold_setD_size, Array.size_replicate] at hk2; exact hk2),
        Array.getElem?_eq_getElem hk2] at h
    exact Option.some.inj h
  · rw [dif_neg hk2]

/-- If two `forIn` body functions agree on all elements of the list,
    the `forIn` results are equal. -/
private theorem forIn_congr_body {S : Type} {α : Type} (l : List α) (init : S)
    (body1 body2 : α → S → Id (ForInStep S))
    (h : ∀ k, k ∈ l → ∀ s, body1 k s = body2 k s) :
    forIn (m := Id) l init body1 = forIn (m := Id) l init body2 := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [forIn, ForIn.forIn, List.forIn'_cons, bind]
    rw [h x (List.mem_cons_self ..)]
    cases body2 x init with
    | done r => rfl
    | yield r =>
      show forIn (m := Id) xs r body1 = forIn (m := Id) xs r body2
      exact ih r (fun k hk s => h k (List.mem_cons_of_mem _ hk) s)

/-! **Scatter bz = mulAdjPre (under NeighborSymm)** -/

set_option maxHeartbeats 3200000 in
/-- The `.fst` (bz) of the ds4 loop starting from `replicate n 0` equals
    `mulAdjPre neighbors (decodedZCol ...) n d` under `NeighborSymm`. -/
private theorem ds4_fst_eq_mulAdjPre
    (neighbors : Array Nat) (d : Nat) (certBytes : ByteArray) (n : Nat)
    (j : Nat) (hj : j < n) (hsym : NeighborSymm neighbors n d) :
    let colStart := j * (j + 1) / 2
    (forIn (m := Id) (List.range' 0 (j + 1) 1)
      (⟨Array.replicate n (0 : Int), (0 : Int), (0 : Int), Array.replicate n (0 : Int)⟩ : DS4)
      (ds4Body neighbors d certBytes colStart)).fst =
    mulAdjPre neighbors (decodedZCol certBytes colStart n j) n d := by
  intro colStart
  rw [ds4_fst_component]
  -- Show scatter fold = scatterMulAdj, then use scatterMulAdj_eq_mulAdjPre
  suffices h : forIn (m := Id) (List.range' 0 (j + 1) 1) (Array.replicate n (0 : Int))
    (fun k bz' =>
      let zk := decodeBase85Int certBytes (colStart + k)
      ForInStep.yield (forIn (m := Id) (List.range' 0 d 1) bz' (fun p bz'' =>
        ForInStep.yield (bz''.set! neighbors[k * d + p]! (bz''[neighbors[k * d + p]!]! + zk))))) =
    scatterMulAdj neighbors (decodedZCol certBytes colStart n j) n d (j + 1) by
    rw [h]; exact scatterMulAdj_eq_mulAdjPre neighbors _ n d (j + 1) (by omega)
      (decodedZCol_size certBytes colStart n j) hsym
      (fun k hk => decodedZCol_zero certBytes colStart n j hj k hk)
  simp only [scatterMulAdj, Id.run, bind, pure,
    Std.Range.forIn_eq_forIn_range', Std.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  -- Both are forIn with same init, bodies differ only in zk source
  apply forIn_congr_body
  intro k hk bz
  have hk_bound : k < j + 1 := by rw [List.mem_range'] at hk; omega
  congr 1; apply forIn_congr_body
  intro p _hp bz'; congr 1; congr 1; congr 1
  exact (decodedZCol_bang certBytes colStart n j hj k hk_bound).symm

/-! **Outer body definition (matches desugared form)** -/

/-- Body of `checkPSDColumnsFull`'s outer `forIn` loop, matching desugaring exactly.
    Extracts the desugared body to enable definitional matching via `rfl`. -/
private def outerBody (neighbors : Array Nat) (d : Nat)
    (certBytes : ByteArray) (n : Nat) (c₁ c₂ c₃ : Int)
    (j : Nat) (r : FullState) : ForInStep FullState :=
  let bz₀ := forIn (m := Id) (List.range' 0 n 1) r.fst
    (fun v bz => ForInStep.yield (bz.set! v 0))
  let colStart := j * (j + 1) / 2
  let ds := forIn (m := Id) (List.range' 0 (j + 1) 1)
    (⟨bz₀, (0 : Int), (0 : Int), r.snd.snd.snd.snd.snd⟩ : DS4)
    (ds4Body neighbors d certBytes colStart)
  let ps := forIn (m := Id) (List.range' 0 (j + 1) 1)
    (⟨r.snd.snd.fst, r.snd.snd.snd.fst, r.snd.snd.snd.snd.fst⟩ :
      MProd Int (MProd Bool Int))
    (fun i (st : MProd Int (MProd Bool Int)) =>
      let b2zi : Int := forIn (m := Id) (List.range' 0 d 1) (0 : Int)
        (fun p (acc : Int) => ForInStep.yield
          (acc + ds.fst[neighbors[i * d + p]!]!))
      let pij := c₁ * ds.snd.snd.snd[i]! - c₂ * b2zi + c₃ * ds.snd.snd.fst
      if i == j then
        if st.snd.fst then ForInStep.yield ⟨st.fst, false, pij⟩
        else if pij < st.snd.snd then ForInStep.yield ⟨st.fst, st.snd.fst, pij⟩
        else ForInStep.yield ⟨st.fst, st.snd.fst, st.snd.snd⟩
      else if i < j then
        let absPij := if pij >= 0 then pij else -pij
        if absPij > st.fst then ForInStep.yield ⟨absPij, st.snd.fst, st.snd.snd⟩
        else ForInStep.yield ⟨st.fst, st.snd.fst, st.snd.snd⟩
      else ForInStep.yield ⟨st.fst, st.snd.fst, st.snd.snd⟩)
  ForInStep.yield
    ⟨ds.fst, r.snd.fst.push ds.snd.fst, ps.fst, ps.snd.fst, ps.snd.snd, ds.snd.snd.snd⟩

set_option maxHeartbeats 12800000 in
/-- `checkPSDColumnsFull` = `projFull` of `forIn` with `outerBody`. -/
private theorem checkPSDColumnsFull_eq_forIn
    (neighbors : Array Nat) (certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : Int) (cols : Array Nat) :
    checkPSDColumnsFull neighbors certBytes n d c₁ c₂ c₃ cols =
    projFull (forIn (m := Id) cols.toList
      (⟨Array.replicate n 0, Array.mkEmpty cols.size, 0, true, 0,
        Array.replicate n 0⟩ : FullState)
      (fun j r => outerBody neighbors d certBytes n c₁ c₂ c₃ j r)) := by
  unfold checkPSDColumnsFull
  simp only [Id.run, bind, pure, projFull, outerBody,
    Std.Range.forIn_eq_forIn_range', Std.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [show forIn cols _ _ = forIn cols.toList _ _ from (Array.forIn_toList).symm]
  rfl

/-! **Per-column scatter step** -/

/-- Per-column step that fuses decode + scatter + PSD update.
    Uses fresh arrays for both `zCol` and `bz`. -/
private def psdColumnStepScatter (neighbors : Array Nat) (d : Nat)
    (certBytes : ByteArray) (n : Nat) (c₁ c₂ c₃ : Int)
    (state : PSDChunkResult) (j : Nat) : PSDChunkResult × Int :=
  let colStart := j * (j + 1) / 2
  let ds := forIn (m := Id) (List.range' 0 (j + 1) 1)
    (⟨Array.replicate n (0 : Int), (0 : Int), (0 : Int), Array.replicate n (0 : Int)⟩ : DS4)
    (ds4Body neighbors d certBytes colStart)
  let ps := forIn (m := Id) (List.range' 0 (j + 1) 1)
    (⟨state.epsMax, state.first, state.minDiag⟩ : MProd Int (MProd Bool Int))
    (fun i (st : MProd Int (MProd Bool Int)) =>
      let b2zi : Int := forIn (m := Id) (List.range' 0 d 1) (0 : Int)
        (fun p (acc : Int) => ForInStep.yield
          (acc + ds.fst[neighbors[i * d + p]!]!))
      let pij := c₁ * ds.snd.snd.snd[i]! - c₂ * b2zi + c₃ * ds.snd.snd.fst
      if i == j then
        if st.snd.fst then ForInStep.yield ⟨st.fst, false, pij⟩
        else if pij < st.snd.snd then ForInStep.yield ⟨st.fst, st.snd.fst, pij⟩
        else ForInStep.yield ⟨st.fst, st.snd.fst, st.snd.snd⟩
      else if i < j then
        let absPij := if pij >= 0 then pij else -pij
        if absPij > st.fst then ForInStep.yield ⟨absPij, st.snd.fst, st.snd.snd⟩
        else ForInStep.yield ⟨st.fst, st.snd.fst, st.snd.snd⟩
      else ForInStep.yield ⟨st.fst, st.snd.fst, st.snd.snd⟩)
  ({epsMax := ps.fst, minDiag := ps.snd.snd, first := ps.snd.fst}, ds.snd.fst)

/-! **`forIn` with invariant** -/

/-- `forIn`-to-`foldl` with invariant and membership: callbacks get `j ∈ l`. -/
private theorem forIn_yield_proj_inv {S P : Type} (l : List Nat) (init : S)
    (body : Nat → S → Id (ForInStep S)) (proj : S → P) (smallStep : P → Nat → P)
    (inv : S → Prop) (hinit : inv init)
    (hyield : ∀ j, j ∈ l → ∀ s, inv s → ∃ r, body j s = ForInStep.yield r)
    (hinv : ∀ j, j ∈ l → ∀ s r, inv s → body j s = ForInStep.yield r → inv r)
    (hproj : ∀ j, j ∈ l → ∀ s r, inv s → body j s = ForInStep.yield r →
      proj r = smallStep (proj s) j) :
    proj (forIn (m := Id) l init body) = l.foldl smallStep (proj init) := by
  induction l generalizing init with
  | nil => simp [forIn, ForIn.forIn, List.forIn'_nil, pure]
  | cons x xs ih =>
    simp only [forIn, ForIn.forIn, List.forIn'_cons, bind, List.foldl_cons]
    have hx : x ∈ x :: xs := List.mem_cons_self ..
    obtain ⟨r, hr⟩ := hyield x hx init hinit
    rw [show body x init = ForInStep.yield r from hr]
    show proj (forIn (m := Id) xs r body) = _
    rw [ih r (hinv x hx init r hinit hr)
      (fun j hj => hyield j (List.mem_cons_of_mem _ hj))
      (fun j hj => hinv j (List.mem_cons_of_mem _ hj))
      (fun j hj => hproj j (List.mem_cons_of_mem _ hj)),
      hproj x hx init r hinit hr]

/-! **Ghost state elimination** -/

/-- Invariant for the outer loop: `bz` and `zCol` buffers have size `n`. -/
private def fullInv (n : Nat) (s : FullState) : Prop :=
  s.fst.size = n ∧ s.snd.snd.snd.snd.snd.size = n

/-- Yield-only `forIn` preserves a `Nat`-valued projection. -/
private theorem forIn_yield_preserves {S : Type} {α : Type} (l : List α) (init : S)
    (body : α → S → ForInStep S) (proj : S → Nat)
    (h : ∀ k s, ∃ r, body k s = ForInStep.yield r ∧ proj r = proj s) :
    proj (forIn (m := Id) l init body) = proj init := by
  induction l generalizing init with
  | nil => simp [forIn, ForIn.forIn, List.forIn'_nil, pure]
  | cons x xs ih =>
    simp only [forIn, ForIn.forIn, List.forIn'_cons, bind]
    obtain ⟨r, hr, hproj⟩ := h x init
    simp only [hr]
    show proj (forIn (m := Id) xs r body) = proj init
    rw [ih, hproj]

/-- Inner scatter loop preserves `bz` array size. -/
private theorem scatter_inner_size (l : List Nat) (bz : Array Int) (g : Nat → Nat)
    (zk : Int) :
    (forIn (m := Id) l bz (fun p (a : Array Int) =>
      ForInStep.yield (a.set! (g p) (a[g p]! + zk)))).size = bz.size := by
  apply forIn_yield_preserves l bz _ (fun a => a.size)
  intro k a
  exact ⟨_, rfl, by simp [Array.set!, Array.size_setIfInBounds]⟩

/-- `ds4Body` preserves `bz` (`.fst`) size. -/
private theorem ds4_bz_size (neighbors : Array Nat) (d : Nat) (certBytes : ByteArray)
    (colStart : Nat) (l : List Nat) (init : DS4) :
    (forIn (m := Id) l init (ds4Body neighbors d certBytes colStart)).fst.size = init.fst.size := by
  apply forIn_yield_preserves l init _ (fun s => s.fst.size)
  intro k s
  refine ⟨_, rfl, ?_⟩
  show (forIn (m := Id) (List.range' 0 d 1) s.fst (fun p (a : Array Int) =>
    ForInStep.yield (a.set! neighbors[k * d + p]! (a[neighbors[k * d + p]!]! +
      decodeBase85Int certBytes (colStart + k))))).size = s.fst.size
  exact scatter_inner_size _ _ _ _

/-- `ds4Body` preserves `zCol` (`.snd.snd.snd`) size. -/
private theorem ds4_zCol_size (neighbors : Array Nat) (d : Nat) (certBytes : ByteArray)
    (colStart : Nat) (l : List Nat) (init : DS4) :
    (forIn (m := Id) l init (ds4Body neighbors d certBytes colStart)).snd.snd.snd.size =
    init.snd.snd.snd.size := by
  apply forIn_yield_preserves l init _ (fun s => s.snd.snd.snd.size)
  intro k s
  exact ⟨_, rfl, by simp [Array.set!, Array.size_setIfInBounds]⟩

/-- Zeroing `forIn` preserves array size. -/
private theorem forIn_zero_size (arr : Array Int) (n : Nat) :
    (forIn (m := Id) (List.range' 0 n 1) arr
      (fun v (r : Array Int) => ForInStep.yield (r.set! v 0))).size = arr.size := by
  apply forIn_yield_preserves (List.range' 0 n 1) arr _ (fun a => a.size)
  intro k a
  exact ⟨_, rfl, by simp [Array.set!, Array.size_setIfInBounds]⟩

/-- `outerBody` preserves the size invariant. -/
private theorem outerBody_preserves_inv (neighbors : Array Nat) (d : Nat)
    (certBytes : ByteArray) (n : Nat) (c₁ c₂ c₃ : Int)
    (j : Nat) (s : FullState) (_hj : j < n) (hinv : fullInv n s) :
    fullInv n (match outerBody neighbors d certBytes n c₁ c₂ c₃ j s with
      | .yield r => r | .done r => r) := by
  simp only [outerBody, fullInv]
  obtain ⟨hbz, hzCol⟩ := hinv
  constructor
  · rw [ds4_bz_size, forIn_zero_size, hbz]
  · rw [ds4_zCol_size, hzCol]

set_option maxHeartbeats 6400000 in
/-- Ghost state elimination: `projFull` of `outerBody` result depends only on `projFull`
    of the input (not on the `bz`/`zCol` buffers), so it equals `psdColumnStepScatter`. -/
private theorem outerBody_proj_eq_scatter
    (neighbors : Array Nat) (d : Nat)
    (certBytes : ByteArray) (n : Nat) (c₁ c₂ c₃ : Int)
    (j : Nat) (s : FullState) (hj : j < n) (hinv : fullInv n s) :
    let r := match outerBody neighbors d certBytes n c₁ c₂ c₃ j s with
      | .yield r => r | .done r => r
    projFull r =
    ((psdColumnStepScatter neighbors d certBytes n c₁ c₂ c₃ (projFull s).1 j).1,
     (projFull s).2.push (psdColumnStepScatter neighbors d certBytes n c₁ c₂ c₃ (projFull s).1 j).2) := by
  simp only [outerBody, psdColumnStepScatter, projFull, fullInv] at *
  obtain ⟨hbz_size, hzCol_size⟩ := hinv
  -- Step 1: Rewrite bz zeroing to replicate n 0
  rw [forIn_zero_eq_replicate s.fst n hbz_size]
  -- Name the two DS4 results
  set colStart := j * (j + 1) / 2
  set ds_old := forIn (m := Id) (List.range' 0 (j + 1) 1)
    (⟨Array.replicate n (0 : Int), (0 : Int), (0 : Int), s.snd.snd.snd.snd.snd⟩ : DS4)
    (ds4Body neighbors d certBytes colStart) with hds_old_def
  set ds_new := forIn (m := Id) (List.range' 0 (j + 1) 1)
    (⟨Array.replicate n (0 : Int), (0 : Int), (0 : Int), Array.replicate n (0 : Int)⟩ : DS4)
    (ds4Body neighbors d certBytes colStart) with hds_new_def
  -- Component equalities from ds4_proj3_independent
  have hproj := ds4_proj3_independent neighbors d certBytes colStart
    (List.range' 0 (j + 1) 1) (Array.replicate n 0) 0 0
    s.snd.snd.snd.snd.snd (Array.replicate n 0)
  have hbz_eq : ds_old.fst = ds_new.fst := hproj.1
  have hcn_eq : ds_old.snd.fst = ds_new.snd.fst := hproj.2.1
  have hcs_eq : ds_old.snd.snd.fst = ds_new.snd.snd.fst := hproj.2.2
  -- zCol[i]! equality for i in range: both getD = decode(colStart + i)
  -- Note: [i]! = getD i default, and default : Int = 0
  have hzCol_eq : ∀ i, i ∈ List.range' 0 (j + 1) 1 →
      ds_old.snd.snd.snd[i]! = ds_new.snd.snd.snd[i]! := by
    intro i hi
    have hi_bound : i < j + 1 := by rw [List.mem_range'] at hi; omega
    show ds_old.snd.snd.snd.getD i default = ds_new.snd.snd.snd.getD i default
    -- default : Int = 0, so getD i default = getD i 0
    show ds_old.snd.snd.snd.getD i 0 = ds_new.snd.snd.snd.getD i 0
    rw [hds_old_def, ds4_zCol_getD neighbors d certBytes colStart j
      (Array.replicate n 0) 0 0 s.snd.snd.snd.snd.snd (by omega) i hi_bound,
        hds_new_def, ds4_zCol_getD neighbors d certBytes colStart j
      (Array.replicate n 0) 0 0 (Array.replicate n 0) (by simp; omega) i hi_bound]
  -- All three ds_old components (.fst, .snd.snd.fst, .snd.snd.snd[i]!) appear inside
  -- lambdas in the PSD forIn body, so rw can't reach them directly.
  -- Strategy: prove ds_old = ds_new component-wise implies equal forIn results,
  -- then rewrite the colNorm and PSD parts separately.
  -- First rewrite colNorm (appears as free variable, not in lambda):
  rw [hcn_eq]
  -- Now prove the PSD forIn with ds_old = PSD forIn with ds_new.
  -- The key: forIn_congr_body lets us rewrite per-element.
  -- We need to match the EXACT body lambda from the goal.
  -- After simp [outerBody, psdColumnStepScatter, projFull], the PSD body uses
  -- ds_old.fst, ds_old.snd.snd.fst, ds_old.snd.snd.snd[i]! on LHS
  -- and ds_new versions on RHS.
  -- Prove forIn equality:
  suffices hpsd :
    (forIn (m := Id) (List.range' 0 (j + 1) 1)
      (⟨s.snd.snd.fst, s.snd.snd.snd.fst, s.snd.snd.snd.snd.fst⟩ :
        MProd Int (MProd Bool Int))
      (fun i (st : MProd Int (MProd Bool Int)) =>
        let b2zi : Int := forIn (m := Id) (List.range' 0 d 1) (0 : Int)
          (fun p (acc : Int) => ForInStep.yield (acc + ds_old.fst[neighbors[i * d + p]!]!))
        let pij := c₁ * ds_old.snd.snd.snd[i]! - c₂ * b2zi + c₃ * ds_old.snd.snd.fst
        if i == j then
          if st.snd.fst then ForInStep.yield ⟨st.fst, false, pij⟩
          else if pij < st.snd.snd then ForInStep.yield ⟨st.fst, st.snd.fst, pij⟩
          else ForInStep.yield ⟨st.fst, st.snd.fst, st.snd.snd⟩
        else if i < j then
          let absPij := if pij >= 0 then pij else -pij
          if absPij > st.fst then ForInStep.yield ⟨absPij, st.snd.fst, st.snd.snd⟩
          else ForInStep.yield ⟨st.fst, st.snd.fst, st.snd.snd⟩
        else ForInStep.yield ⟨st.fst, st.snd.fst, st.snd.snd⟩)) =
    (forIn (m := Id) (List.range' 0 (j + 1) 1)
      (⟨s.snd.snd.fst, s.snd.snd.snd.fst, s.snd.snd.snd.snd.fst⟩ :
        MProd Int (MProd Bool Int))
      (fun i (st : MProd Int (MProd Bool Int)) =>
        let b2zi : Int := forIn (m := Id) (List.range' 0 d 1) (0 : Int)
          (fun p (acc : Int) => ForInStep.yield (acc + ds_new.fst[neighbors[i * d + p]!]!))
        let pij := c₁ * ds_new.snd.snd.snd[i]! - c₂ * b2zi + c₃ * ds_new.snd.snd.fst
        if i == j then
          if st.snd.fst then ForInStep.yield ⟨st.fst, false, pij⟩
          else if pij < st.snd.snd then ForInStep.yield ⟨st.fst, st.snd.fst, pij⟩
          else ForInStep.yield ⟨st.fst, st.snd.fst, st.snd.snd⟩
        else if i < j then
          let absPij := if pij >= 0 then pij else -pij
          if absPij > st.fst then ForInStep.yield ⟨absPij, st.snd.fst, st.snd.snd⟩
          else ForInStep.yield ⟨st.fst, st.snd.fst, st.snd.snd⟩
        else ForInStep.yield ⟨st.fst, st.snd.fst, st.snd.snd⟩)) by
    -- Use hpsd to close the struct+push goal via congrArg
    exact congrArg (fun ps : MProd Int (MProd Bool Int) =>
      (PSDChunkResult.mk ps.fst ps.snd.snd ps.snd.fst,
       s.snd.fst.push ds_new.snd.fst)) hpsd
  -- Prove the PSD forIn equality via forIn_congr_body
  apply forIn_congr_body; intro i hi st
  rw [hbz_eq, hcs_eq, hzCol_eq i hi]

/-! **Per-column scatter = full bridge** -/

set_option maxHeartbeats 6400000 in
/-- Per-column: scatter-based step = gather-based step under `NeighborSymm`.
    The proof bridges `scatterMulAdj` → `mulAdjPre` via `NeighborSymm`. -/
private theorem psdColumnStepScatter_eq_full (neighbors : Array Nat) (d : Nat)
    (certBytes : ByteArray) (n : Nat) (c₁ c₂ c₃ : Int)
    (state : PSDChunkResult) (j : Nat) (hj : j < n)
    (hsym : NeighborSymm neighbors n d) :
    psdColumnStepScatter neighbors d certBytes n c₁ c₂ c₃ state j =
    psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ state j := by
  -- Unfold both definitions partially
  simp only [psdColumnStepScatter, psdColumnStepFull]
  set colStart := j * (j + 1) / 2
  -- Name the DS4 result from scatter
  set ds := forIn (m := Id) (List.range' 0 (j + 1) 1)
    (⟨Array.replicate n (0 : Int), (0 : Int), (0 : Int), Array.replicate n (0 : Int)⟩ : DS4)
    (ds4Body neighbors d certBytes colStart) with hds_def
  -- The fused decode in psdColumnStepFull produces (zCol, colSum, colNorm):
  set fusedResult := (Id.run do
    let mut arr := Array.replicate n (0 : Int)
    let mut s : Int := 0
    let mut norm : Int := 0
    for k in [:j+1] do
      let v := decodeBase85Int certBytes (colStart + k)
      arr := arr.set! k v; s := s + v; norm := norm + intAbs v
    return (arr, s, norm)) with hfused_def
  -- Key equalities:
  -- 1. ds.fst = mulAdjPre neighbors fusedResult.1 n d (under NeighborSymm)
  --    Actually, ds.fst = mulAdjPre neighbors (decodedZCol ...) n d, and
  --    fusedResult.1 = decodedZCol (they're the same array).
  -- 2. ds.snd.fst = fusedResult.2.2 (colNorm)
  -- 3. ds.snd.snd.fst = fusedResult.2.1 (colSum)
  -- 4. ds.snd.snd.snd[i]! = fusedResult.1[i]! for i < j+1 (zCol entries)
  -- Step 1: Show scatter colNorm = fused colNorm
  have hcn : ds.snd.fst =
      Nat.fold (j + 1) (fun k _ acc => acc + intAbs (decodeBase85Int certBytes (colStart + k))) 0 := by
    rw [hds_def, ds4_colNorm_component]
    rw [forIn_range'_eq_fold (fun k (acc : Int) => acc + intAbs (decodeBase85Int certBytes (colStart + k)))]
    simp only [Nat.zero_add]
  have hcn_fused : fusedResult.2.2 =
      Nat.fold (j + 1) (fun k _ acc => acc + intAbs (decodeBase85Int certBytes (colStart + k))) 0 := by
    rw [hfused_def, fused_norm_is_fold]
  have hcolNorm_eq : ds.snd.fst = fusedResult.2.2 := by rw [hcn, hcn_fused]
  -- Step 2: Show scatter colSum = fused colSum
  have hcs : ds.snd.snd.fst =
      Nat.fold (j + 1) (fun k _ acc => acc + decodeBase85Int certBytes (colStart + k)) 0 := by
    rw [hds_def, ds4_colSum_component]
    rw [forIn_range'_eq_fold (fun k (acc : Int) => acc + decodeBase85Int certBytes (colStart + k))]
    simp only [Nat.zero_add]
  have hcs_fused : fusedResult.2.1 =
      Nat.fold (j + 1) (fun k _ acc => acc + decodeBase85Int certBytes (colStart + k)) 0 := by
    rw [hfused_def, fused_sum_is_fold]
  have hcolSum_eq : ds.snd.snd.fst = fusedResult.2.1 := by rw [hcs, hcs_fused]
  -- Step 3: Show scatter bz = mulAdjPre neighbors (decodedZCol ...) n d (under NeighborSymm)
  have hbz : ds.fst = mulAdjPre neighbors (decodedZCol certBytes colStart n j) n d := by
    rw [hds_def]; exact ds4_fst_eq_mulAdjPre neighbors d certBytes n j hj hsym
  -- Step 4: Show fused zCol = decodedZCol
  -- fusedResult.1 = fused_arr_eq_unfused's result = unfused arr fold
  -- decodedZCol = Nat.fold with setIfInBounds
  -- Both build the same array: replicate n 0 with positions 0..j set to decode(colStart+i)
  have hzCol_arr : fusedResult.1 = decodedZCol certBytes colStart n j := by
    rw [hfused_def]
    -- fusedResult = Id.run do ... = Nat.fold via fusedDecode_eq_fold
    -- Then .1 = Nat.fold arr-only via fusedFold_arr
    rw [fusedDecode_eq_fold, fusedFold_arr]
    -- Now goal: Nat.fold (j+1) (fun k _ arr => arr.set! k (decode(colStart+k))) (replicate n 0)
    --         = decodedZCol certBytes colStart n j
    -- decodedZCol = Nat.fold (j+1) (fun i _ a => a.setIfInBounds i (decode(colStart+i))) (replicate n 0)
    -- set! = setIfInBounds, so these are definitionally equal
    rfl
  -- Step 5: Show scatter zCol[i]! = fused zCol[i]! for i in range
  -- ds.snd.snd.snd[i]! = decodedZCol[i]! = fusedResult.1[i]!
  have hzCol_entry : ∀ i, i ∈ List.range' 0 (j + 1) 1 →
      ds.snd.snd.snd[i]! = fusedResult.1[i]! := by
    intro i hi
    have hi_bound : i < j + 1 := by rw [List.mem_range'] at hi; omega
    show ds.snd.snd.snd.getD i default = fusedResult.1.getD i default
    show ds.snd.snd.snd.getD i 0 = fusedResult.1.getD i 0
    rw [hds_def, ds4_zCol_getD neighbors d certBytes colStart j
      (Array.replicate n 0) 0 0 (Array.replicate n 0) (by simp; omega) i hi_bound]
    rw [hzCol_arr, decodedZCol_getD certBytes colStart n j hj i hi_bound]
  -- Step 6: ds.fst = mulAdjPre neighbors fusedResult.1 n d
  have hbz_fused : ds.fst = mulAdjPre neighbors fusedResult.1 n d := by
    rw [hbz, hzCol_arr]
  -- Now assemble: the outputs are (PSDResult, colNorm) pairs
  -- First unfold the PSD loop structure on both sides:
  simp only [Id.run, bind, pure, Std.Range.forIn_eq_forIn_range', Std.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, mulAdjEntry]
  -- Rewrite scatter bz and colSum to match the full versions
  rw [hbz_fused, hcolSum_eq]
  -- Now both sides have the same bz (mulAdjPre) and colSum (fusedResult.2.1).
  -- The only difference: ds.snd.snd.snd[i]! vs fusedResult.1[i]! inside lambdas,
  -- and ds.snd.fst vs fusedResult.2.2 in the colNorm output.
  -- Rewrite colNorm:
  rw [hcolNorm_eq]
  -- Now only ds.snd.snd.snd[i]! vs fusedResult.1[i]! remains inside PSD lambda.
  -- Prove the PSD forIn equality via forIn_congr_body, then derive via congrArg.
  suffices hpsd :
    forIn (m := Id) (List.range' 0 (j + 1) 1)
      (⟨state.epsMax, state.first, state.minDiag⟩ : MProd Int (MProd Bool Int))
      (fun i (st : MProd Int (MProd Bool Int)) =>
        let b2zi : Int := forIn (m := Id) (List.range' 0 d 1) (0 : Int)
          (fun p (acc : Int) => ForInStep.yield
            (acc + (mulAdjPre neighbors fusedResult.1 n d)[neighbors[i * d + p]!]!))
        let pij := c₁ * ds.snd.snd.snd[i]! - c₂ * b2zi + c₃ * fusedResult.2.1
        if i == j then
          if st.snd.fst then ForInStep.yield ⟨st.fst, false, pij⟩
          else if pij < st.snd.snd then ForInStep.yield ⟨st.fst, st.snd.fst, pij⟩
          else ForInStep.yield ⟨st.fst, st.snd.fst, st.snd.snd⟩
        else if i < j then
          let absPij := if pij >= 0 then pij else -pij
          if absPij > st.fst then ForInStep.yield ⟨absPij, st.snd.fst, st.snd.snd⟩
          else ForInStep.yield ⟨st.fst, st.snd.fst, st.snd.snd⟩
        else ForInStep.yield ⟨st.fst, st.snd.fst, st.snd.snd⟩) =
      forIn (m := Id) (List.range' 0 (j + 1) 1)
      (⟨state.epsMax, state.first, state.minDiag⟩ : MProd Int (MProd Bool Int))
      (fun i (st : MProd Int (MProd Bool Int)) =>
        let b2zi : Int := forIn (m := Id) (List.range' 0 d 1) (0 : Int)
          (fun p (acc : Int) => ForInStep.yield
            (acc + (mulAdjPre neighbors fusedResult.1 n d)[neighbors[i * d + p]!]!))
        let pij := c₁ * fusedResult.1[i]! - c₂ * b2zi + c₃ * fusedResult.2.1
        if i == j then
          if st.snd.fst then ForInStep.yield ⟨st.fst, false, pij⟩
          else if pij < st.snd.snd then ForInStep.yield ⟨st.fst, st.snd.fst, pij⟩
          else ForInStep.yield ⟨st.fst, st.snd.fst, st.snd.snd⟩
        else if i < j then
          let absPij := if pij >= 0 then pij else -pij
          if absPij > st.fst then ForInStep.yield ⟨absPij, st.snd.fst, st.snd.snd⟩
          else ForInStep.yield ⟨st.fst, st.snd.fst, st.snd.snd⟩
        else ForInStep.yield ⟨st.fst, st.snd.fst, st.snd.snd⟩) by
    -- Close the Prod goal using hpsd
    exact congrArg (fun ps =>
      (PSDChunkResult.mk ps.fst ps.snd.snd ps.snd.fst, fusedResult.2.2)) hpsd
  -- Prove the PSD forIn equality
  apply forIn_congr_body; intro i hi st
  rw [hzCol_entry i hi]

/-! **Per-column projection lemma** -/

set_option maxHeartbeats 6400000 in
/-- The new scatter-based `checkPSDColumnsFull` = `List.foldl` over
    `psdColumnStepFull` (gather-based). Requires `NeighborSymm` because the
    scatter B·z = gather B·z only under adjacency symmetry, plus ghost state
    elimination (bz zeroed, zCol overwritten each column). -/
private theorem checkPSDColumnsFull_foldl
    (neighbors : Array Nat) (certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : Int) (cols : Array Nat)
    (hsym : NeighborSymm neighbors n d)
    (hcols : ∀ j ∈ cols.toList, j < n) :
    checkPSDColumnsFull neighbors certBytes n d c₁ c₂ c₃ cols =
    cols.toList.foldl
      (fun (p : PSDChunkResult × Array Int) j =>
        ((psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ p.1 j).1,
         p.2.push (psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ p.1 j).2))
      ({ epsMax := 0, minDiag := 0, first := true }, Array.mkEmpty cols.size) := by
  rw [checkPSDColumnsFull_eq_forIn]
  apply forIn_yield_proj_inv (S := FullState) (P := PSDChunkResult × Array Int)
    cols.toList _ _ projFull
    (fun p j => ((psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ p.1 j).1,
                 p.2.push (psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ p.1 j).2))
    (fullInv n) ⟨Array.size_replicate .., Array.size_replicate ..⟩
  -- hyield: the body always yields
  · intro j _ s _; exact ⟨_, rfl⟩
  -- hinv: invariant preserved
  · intro j hj s r hinv hr
    simp only [outerBody] at hr
    have := ForInStep.yield.inj hr; subst this
    exact outerBody_preserves_inv neighbors d certBytes n c₁ c₂ c₃ j s
      (hcols j hj) hinv
  -- hproj: projection commutes
  · intro j hj s r hinv hr
    simp only [outerBody] at hr
    have := ForInStep.yield.inj hr; subst this
    have hjn := hcols j hj
    have hscatter := outerBody_proj_eq_scatter neighbors d certBytes n c₁ c₂ c₃ j s hjn hinv
    simp only [outerBody] at hscatter
    rw [hscatter]
    congr 1
    · exact congrArg Prod.fst (psdColumnStepScatter_eq_full neighbors d certBytes n c₁ c₂ c₃
        (projFull s).1 j hjn hsym)
    · congr 1
      exact congrArg Prod.snd (psdColumnStepScatter_eq_full neighbors d certBytes n c₁ c₂ c₃
        (projFull s).1 j hjn hsym)

/-- `.1` of the fused column loop = the unfused `checkPSDColumns`. -/
theorem checkPSDColumnsFull_fst (neighbors : Array Nat) (certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : Int) (cols : Array Nat)
    (hsym : NeighborSymm neighbors n d)
    (hcols : ∀ j ∈ cols.toList, j < n) :
    (checkPSDColumnsFull neighbors certBytes n d c₁ c₂ c₃ cols).1 =
    checkPSDColumns neighbors certBytes n d c₁ c₂ c₃ cols := by
  rw [checkPSDColumnsFull_foldl neighbors certBytes n d c₁ c₂ c₃ cols hsym hcols,
      checkPSDColumns_foldl]
  suffices ∀ (l : List Nat) (s : PSDChunkResult) (ns : Array Int),
      (∀ j ∈ l, j < n) →
      (l.foldl
        (fun (p : PSDChunkResult × Array Int) j =>
          ((psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ p.1 j).1,
           p.2.push (psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ p.1 j).2))
        (s, ns)).1 =
      l.foldl (psdColumnStep neighbors d certBytes n c₁ c₂ c₃) s from
    this cols.toList _ _ hcols
  intro l; induction l with
  | nil => intros; rfl
  | cons x xs ih =>
    intro s ns hbnd
    simp only [List.foldl_cons]
    rw [psdColumnStepFull_fst neighbors d certBytes n c₁ c₂ c₃ s x (hbnd x (by simp))]
    exact ih (psdColumnStep neighbors d certBytes n c₁ c₂ c₃ s x)
      (ns.push (psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ s x).2)
      (fun y hy => hbnd y (by simp [hy]))

/-! **Norm array lookup** -/

/-- The `.2` norms array from `checkPSDColumnsFull` is the column norms in order. -/
theorem checkPSDColumnsFull_snd_toList (neighbors : Array Nat) (certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : Int) (cols : Array Nat)
    (hsym : NeighborSymm neighbors n d)
    (hcols : ∀ j ∈ cols.toList, j < n) :
    (checkPSDColumnsFull neighbors certBytes n d c₁ c₂ c₃ cols).2.toList =
    cols.toList.map (zColNormPure certBytes n) := by
  rw [checkPSDColumnsFull_foldl neighbors certBytes n d c₁ c₂ c₃ cols hsym hcols]
  suffices ∀ (l : List Nat) (s : PSDChunkResult) (ns : Array Int),
      (∀ j ∈ l, j < n) →
      (l.foldl
        (fun (p : PSDChunkResult × Array Int) j =>
          ((psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ p.1 j).1,
           p.2.push (psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ p.1 j).2))
        (s, ns)).2.toList = ns.toList ++ l.map (zColNormPure certBytes n) from by
    rw [this cols.toList _ _ hcols]; simp
  intro l; induction l with
  | nil =>
    intro s ns _; simp [List.foldl]
  | cons x xs ih =>
    intro s ns hbnd
    simp only [List.foldl_cons, List.map_cons]
    rw [ih _ _ (fun y hy => hbnd y (by simp [hy]))]
    rw [Array.toList_push,
        psdColumnStepFull_snd neighbors d certBytes n c₁ c₂ c₃ s x (hbnd x (by simp))]
    simp [List.append_assoc]

/-! **Fused norm lookup** -/

/-- Bridge: `a[i]! = a[i]` when `i < a.size`. -/
private theorem getElem!_eq_getElem' {α : Type} [Inhabited α] (a : Array α) (i : Nat)
    (h : i < a.size) : a[i]! = a[i] := by
  show a.getD i default = a[i]; unfold Array.getD; simp [h]

/-- Norm lookup from fused results: `results[i%64]!.2[i/64]! = zColNormPure certBytes n i`. -/
theorem fused_norm_lookup (neighbors : Array Nat) (certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : Int) (i : Nat) (hi : i < n)
    (hsym : NeighborSymm neighbors n d) :
    let columnLists := buildColumnLists n 64
    let results := columnLists.map fun cols =>
      checkPSDColumnsFull neighbors certBytes n d c₁ c₂ c₃ cols
    results[i % 64]!.2[i / 64]! = zColNormPure certBytes n i := by
  intro columnLists results
  have hcl_size : columnLists.size = 64 := buildColumnLists_size n 64 (by omega)
  have hmod : i % 64 < 64 := Nat.mod_lt i (by omega)
  -- Column bounds for chunk i%64
  have hcols_bound : ∀ j ∈ (columnLists[i % 64]!).toList, j < n := by
    intro j hj; exact buildColumnLists_bound n 64 (i % 64) (by omega) j hj hmod
  -- Inner bound: i/64 < chunk size
  have hinner : i / 64 < (buildColumnLists n 64)[i % 64]!.size :=
    buildColumnLists_inner_bound n 64 i hi (by omega)
  -- Column entry
  have hentry : (buildColumnLists n 64)[i % 64]![i / 64]! = i :=
    buildColumnLists_entry n 64 i hi (by omega)
  -- Norm array from checkPSDColumnsFull
  set cols := columnLists[i % 64]! with hcols_def
  have hsnd := checkPSDColumnsFull_snd_toList neighbors certBytes n d c₁ c₂ c₃ cols hsym hcols_bound
  -- results.size = 64
  have hres_size : results.size = 64 := by
    show (columnLists.map _).size = 64; rw [Array.size_map, hcl_size]
  -- results[i%64]! = checkPSDColumnsFull ... cols
  have hres_get : results[i % 64]! =
      checkPSDColumnsFull neighbors certBytes n d c₁ c₂ c₃ cols := by
    rw [getElem!_eq_getElem' _ _ (by rw [hres_size]; exact hmod)]
    show (columnLists.map _)[i % 64] = _
    simp only [Array.getElem_map]
    congr 1; exact (getElem!_eq_getElem' columnLists _ (by rw [hcl_size]; exact hmod)).symm
  rw [hres_get]
  -- Norms array size
  have hnorms_size : (checkPSDColumnsFull neighbors certBytes n d c₁ c₂ c₃ cols).2.size =
      cols.size := by
    have := congrArg List.length hsnd
    rw [Array.length_toList, List.length_map, Array.length_toList] at this; exact this
  -- (checkPSDColumnsFull ... cols).2[i/64]! = zColNormPure certBytes n i
  rw [getElem!_eq_getElem' _ _ (by rw [hnorms_size]; exact hinner)]
  -- Bridge through toList
  have hinner_list : i / 64 < (checkPSDColumnsFull neighbors certBytes n d c₁ c₂ c₃ cols).2.toList.length := by
    rw [Array.length_toList, hnorms_size]; exact hinner
  rw [show (checkPSDColumnsFull neighbors certBytes n d c₁ c₂ c₃ cols).2[i / 64] =
    (checkPSDColumnsFull neighbors certBytes n d c₁ c₂ c₃ cols).2.toList[i / 64] from
    (Array.getElem_toList hinner_list).symm]
  simp only [hsnd, List.getElem_map]
  -- Goal: zColNormPure certBytes n (cols.toList[i/64]) = zColNormPure certBytes n i
  congr 1
  -- cols.toList[i/64] = i
  rw [Array.getElem_toList hinner]
  rw [show (cols[i / 64]'hinner : Nat) = cols[i / 64]! from
    (getElem!_eq_getElem' cols _ hinner).symm]
  exact hentry

/-! **Prefix-sum = checkPerRow** -/

private def recCheck {α : Type} (check : α → Int → Bool) (step : α → Int → Int) :
    List α → Int → Bool
  | [], _ => true
  | x :: xs, prefSum =>
    check x prefSum && recCheck check step xs (step x prefSum)

private theorem list_forIn_neg_break_eq_recCheck
    {α : Type} (check : α → Int → Bool) (step : α → Int → Int)
    (l : List α) (prefSum : Int) :
    let body : α → MProd (Option Bool) Int → Id (ForInStep (MProd (Option Bool) Int)) :=
      fun i r =>
        if !(check i r.snd) then ForInStep.done ⟨some false, r.snd⟩
        else ForInStep.yield ⟨none, step i r.snd⟩
    let result := forIn (m := Id) l ⟨(none : Option Bool), prefSum⟩ body
    (match result.fst with | none => true | some a => a) =
    recCheck check step l prefSum := by
  induction l generalizing prefSum with
  | nil =>
    simp only [forIn, ForIn.forIn, List.forIn'_nil, pure, recCheck]
  | cons x xs ih =>
    simp only [recCheck]
    simp only [forIn, ForIn.forIn, List.forIn'_cons, bind, pure]
    cases hc : check x prefSum with
    | false => simp only [Bool.not_false, ite_true, Bool.false_and]
    | true =>
      simp only [Bool.not_true, Bool.true_and]
      exact ih (step x prefSum)

private theorem recCheck_range_eq_checkPerRow
    (certBytes : ByteArray) (n : Nat) (ε mdpe : Int)
    (getNorm : Nat → Int)
    (hNorm : ∀ i, i < n → getNorm i = zColNormPure certBytes n i) :
    ∀ remaining start prefSum,
    remaining + start = n →
    recCheck
      (fun i s => decide (certEntryInt certBytes i i * mdpe > ε * (s + (↑(n - i) : Int) * getNorm i)))
      (fun i s => s + getNorm i)
      (List.range' start remaining 1)
      prefSum =
    checkPerRow certBytes n ε mdpe remaining start prefSum := by
  intro remaining
  induction remaining with
  | zero =>
    intro start prefSum _
    simp only [List.range', recCheck, checkPerRow]
  | succ r ih =>
    intro start prefSum hsum
    simp only [List.range', recCheck, checkPerRow]
    rw [hNorm start (by omega)]
    congr 1
    exact ih (start + 1) (prefSum + zColNormPure certBytes n start) (by omega)

set_option maxHeartbeats 800000 in
/-- Prefix-sum for-loop with early return = `checkPerRow`. -/
theorem prefixSumLoop_eq_checkPerRow
    (certBytes : ByteArray) (n : Nat) (ε mdpe : Int) (getNorm : Nat → Int)
    (hNorm : ∀ i, i < n → getNorm i = zColNormPure certBytes n i) :
    (Id.run do
      let mut prefSum : Int := 0
      for i in [:n] do
        let si := getNorm i
        let ti := prefSum + (↑(n - i) : Int) * si
        if !(certEntryInt certBytes i i * mdpe > ε * ti) then
          return false
        prefSum := prefSum + si
      return true) =
    checkPerRow certBytes n ε mdpe n 0 0 := by
  simp only [Id.run, bind, pure, Std.Range.forIn_eq_forIn_range', Std.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  erw [list_forIn_neg_break_eq_recCheck
    (fun i s => decide (certEntryInt certBytes i i * mdpe > ε * (s + (↑(n - i) : Int) * getNorm i)))
    (fun i s => s + getNorm i)
    (List.range' 0 n 1) 0]
  exact recCheck_range_eq_checkPerRow certBytes n ε mdpe getNorm hNorm n 0 0 (by omega)

/-! **Fused map projection** -/

/-- All entries in any chunk of `buildColumnLists n 64` are `< n`. -/
private theorem buildColumnLists_mem_bound (n : Nat) (cols : Array Nat)
    (hmem : cols ∈ (buildColumnLists n 64).toList) :
    ∀ j ∈ cols.toList, j < n := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
  rw [Array.length_toList, buildColumnLists_size n 64 (by omega)] at hi
  intro j hj
  rw [← heq, Array.getElem_toList] at hj
  exact buildColumnLists_bound n 64 i (by omega) j
    (by rwa [getElem!_eq_getElem' _ _ (by rw [buildColumnLists_size n 64 (by omega)]; exact hi)])
    hi

/-- Mapping `.1` over fused results = mapping unfused `checkPSDColumns`.
    Requires `NeighborSymm` because scatter-based fused code = gather-based
    unfused code only under adjacency symmetry. -/
theorem fused_map_fst_eq (neighbors : Array Nat) (certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : Int)
    (hsym : NeighborSymm neighbors n d) :
    ((buildColumnLists n 64).map fun cols =>
      checkPSDColumnsFull neighbors certBytes n d c₁ c₂ c₃ cols).map (·.1) =
    (buildColumnLists n 64).map fun cols =>
      checkPSDColumns neighbors certBytes n d c₁ c₂ c₃ cols := by
  rw [Array.map_map]
  apply Array.map_congr_left
  intro cols hmem
  exact checkPSDColumnsFull_fst neighbors certBytes n d c₁ c₂ c₃ cols hsym
    (buildColumnLists_mem_bound n cols hmem.val)
