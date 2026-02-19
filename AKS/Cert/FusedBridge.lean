/-
  # Fused Bridge: `checkPSDColumnsFull` ↔ `checkPSDColumns`

  Proves that the fused PSD + column-norm computation in `checkPSDColumnsFull`
  produces the same PSD state as the unfused `checkPSDColumns`, and that the
  norm outputs match `zColNormPure`. Used by `FastProof.lean` to close
  `checkCertificateFast_eq_slow`.
-/

import CertCheck
import AKS.Misc.ForLoop
import AKS.Cert.ColumnNormBridge

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
  -- After simp: body has inlined `let v`, MProd order ⟨arr, norm, s⟩,
  -- and match at the end swaps: ⟨arr, norm, s⟩ => (arr, s, norm).
  have hbody_ext : (fun k (r : MProd (Array Int) (MProd Int Int)) =>
      ForInStep.yield
        ⟨r.fst.set! k (decodeBase85Int certBytes (colStart + k)),
          r.snd.fst + intAbs (decodeBase85Int certBytes (colStart + k)),
          r.snd.snd + decodeBase85Int certBytes (colStart + k)⟩) =
      (fun k r => ForInStep.yield (fusedStepM certBytes colStart k r)) :=
    funext fun k => funext fun r => fusedBody_M certBytes colStart k r
  rw [hbody_ext, forIn_range'_eq_fold (fusedStepM certBytes colStart)]
  simp only [Nat.zero_add]
  -- Goal: (match Nat.fold ... fusedStepM ⟨init⟩ with ⟨a,b,c⟩ => (a,c,b)) = Nat.fold ... fusedStepP init
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

/-- The unfused `colSum` (sum of `zCol[k]!`) equals the direct `Nat.fold` sum.
    Uses `erw` because the inner array do-block elaborates with `let` bindings
    while `forIn_range_eq_fold` uses `have` bindings. -/
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

/-- Swapped MProd fold corresponds to Prod fold: if step functions agree modulo swap,
    then the folds agree modulo swap. -/
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

set_option maxHeartbeats 1600000 in
/-- `checkPSDColumnsFull` as `List.foldl` on `PSDChunkResult × Array Int`. -/
private theorem checkPSDColumnsFull_foldl
    (neighbors : Array Nat) (certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : Int) (cols : Array Nat) :
    checkPSDColumnsFull neighbors certBytes n d c₁ c₂ c₃ cols =
    cols.toList.foldl
      (fun (p : PSDChunkResult × Array Int) j =>
        ((psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ p.1 j).1,
         p.2.push (psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ p.1 j).2))
      ({ epsMax := 0, minDiag := 0, first := true }, Array.mkEmpty cols.size) := by
  unfold checkPSDColumnsFull; simp only [Id.run, bind, pure]
  rw [show forIn cols _ _ = forIn cols.toList _ _ from (Array.forIn_toList).symm]
  erw [list_forIn_yield_foldl]
  exact Prod.ext
    (foldl_mprod_swap
      (fun (r : MProd (Array Int) PSDChunkResult) (j : Nat) =>
        ⟨r.fst.push (psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ r.snd j).snd,
         (psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ r.snd j).fst⟩)
      (fun (p : PSDChunkResult × Array Int) (j : Nat) =>
        ((psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ p.1 j).1,
         p.2.push (psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ p.1 j).2))
      (fun j m => ⟨rfl, rfl⟩)
      ⟨Array.mkEmpty cols.size, { epsMax := 0, minDiag := 0, first := true }⟩
      cols.toList).1
    (foldl_mprod_swap
      (fun (r : MProd (Array Int) PSDChunkResult) (j : Nat) =>
        ⟨r.fst.push (psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ r.snd j).snd,
         (psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ r.snd j).fst⟩)
      (fun (p : PSDChunkResult × Array Int) (j : Nat) =>
        ((psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ p.1 j).1,
         p.2.push (psdColumnStepFull neighbors d certBytes n c₁ c₂ c₃ p.1 j).2))
      (fun j m => ⟨rfl, rfl⟩)
      ⟨Array.mkEmpty cols.size, { epsMax := 0, minDiag := 0, first := true }⟩
      cols.toList).2

/-- `.1` of the fused column loop = the unfused `checkPSDColumns`. -/
theorem checkPSDColumnsFull_fst (neighbors : Array Nat) (certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : Int) (cols : Array Nat)
    (hcols : ∀ j ∈ cols.toList, j < n) :
    (checkPSDColumnsFull neighbors certBytes n d c₁ c₂ c₃ cols).1 =
    checkPSDColumns neighbors certBytes n d c₁ c₂ c₃ cols := by
  rw [checkPSDColumnsFull_foldl, checkPSDColumns_foldl]
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
    (hcols : ∀ j ∈ cols.toList, j < n) :
    (checkPSDColumnsFull neighbors certBytes n d c₁ c₂ c₃ cols).2.toList =
    cols.toList.map (zColNormPure certBytes n) := by
  rw [checkPSDColumnsFull_foldl]
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
    (n d : Nat) (c₁ c₂ c₃ : Int) (i : Nat) (hi : i < n) :
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
  have hsnd := checkPSDColumnsFull_snd_toList neighbors certBytes n d c₁ c₂ c₃ cols hcols_bound
  -- Chain: results[i%64]!.2[i/64]! → checkPSDColumnsFull(cols).2[i/64]!
  --        → hsnd gives toList = cols.toList.map norm
  --        → buildColumnLists_entry gives cols[i/64]! = i
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

/-- Mapping `.1` over fused results = mapping unfused `checkPSDColumns`. -/
theorem fused_map_fst_eq (neighbors : Array Nat) (certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : Int) :
    ((buildColumnLists n 64).map fun cols =>
      checkPSDColumnsFull neighbors certBytes n d c₁ c₂ c₃ cols).map (·.1) =
    (buildColumnLists n 64).map fun cols =>
      checkPSDColumns neighbors certBytes n d c₁ c₂ c₃ cols := by
  rw [Array.map_map]
  apply Array.map_congr_left
  intro cols hmem
  exact checkPSDColumnsFull_fst neighbors certBytes n d c₁ c₂ c₃ cols
    (buildColumnLists_mem_bound n cols hmem.val)
