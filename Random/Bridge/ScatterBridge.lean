module
/-
  # Scatter-Gather Bridge

  Proves `scatterMulAdj` = `mulAdjPre` when the neighbor array satisfies
  adjacency symmetry (from the rotation map involution). Used by
  `FusedBridge.lean` to bridge scatter-based `checkPSDColumnsFull` to the
  gather-based `psdColumnStep`.
-/

public import Random.Cert
public import Random.Misc.Fold
public import Random.Misc.ForLoop
public import AKS.Misc.List
public import Random.Bridge.ColumnNormBridge

@[expose] public section


/-! **Neighbor symmetry** -/

/-- Adjacency symmetry: for all v, w < n, the number of ports of v pointing
    to w equals the number of ports of w pointing to v. Expressed via the
    concrete `mulAdj` entries. -/
def NeighborSymm (neighbors : Array Nat) (n d : Nat) : Prop :=
  ∀ (z : Array Int), z.size = n →
    ∀ w, w < n →
    ∀ nz, nz ≤ n → (∀ k, k ≥ nz → z.getD k 0 = 0) →
    (scatterMulAdj neighbors z n d nz).getD w 0 =
    (mulAdjPre neighbors z n d).getD w 0

/-! **checkInvolution → checkInvAt** -/

set_option maxHeartbeats 800000 in
/-- The for-loop in `checkInvolution` returning true implies all `checkInvAt`
    pass. The body uses `bne` (from `!=`) for the second condition, matching
    the exact desugared form of `checkInvolution`. -/
private theorem checkInv_loop_implies_all (rotBytes : String) (n d : Nat)
    (s m : Nat)
    (h : (forIn (m := Id) (List.range' s m) true (fun k r =>
      let w := decodeBase85Nat rotBytes (2 * k)
      let q := decodeBase85Nat rotBytes (2 * k + 1)
      if (decide (w ≥ n) || decide (q ≥ d)) = true then
        pure (ForInStep.done false)
      else
        let k2 := w * d + q
        let v2 := decodeBase85Nat rotBytes (2 * k2)
        let p2 := decodeBase85Nat rotBytes (2 * k2 + 1)
        if (bne (v2 * d + p2) k) = true then
          pure (ForInStep.done false)
        else
          pure (ForInStep.yield r))) = true) :
    ∀ k, k ≥ s → k < s + m → checkInvAt rotBytes n d k = true := by
  induction m generalizing s with
  | zero => intro k hk1 hk2; omega
  | succ m ih =>
    simp only [List.range'_succ, forIn, ForIn.forIn, List.forIn'_cons, bind, pure] at h
    intro k hks hkm
    by_cases hc1 : (decide (decodeBase85Nat rotBytes (2 * s) ≥ n) ||
      decide (decodeBase85Nat rotBytes (2 * s + 1) ≥ d)) = true
    · -- First check triggers → done false → false = true in h
      simp only [hc1, ite_true] at h
      exact absurd h Bool.false_ne_true
    · simp only [Bool.not_eq_true] at hc1
      by_cases hc2 : bne (decodeBase85Nat rotBytes
        (2 * (decodeBase85Nat rotBytes (2 * s) * d + decodeBase85Nat rotBytes (2 * s + 1))) * d +
        decodeBase85Nat rotBytes
        (2 * (decodeBase85Nat rotBytes (2 * s) * d + decodeBase85Nat rotBytes (2 * s + 1)) + 1)) s = true
      · -- Second check triggers → done false
        simp only [hc1, hc2, ite_true] at h
        exact absurd h Bool.false_ne_true
      · -- Both pass → yield true, continues with rest
        simp only [Bool.not_eq_true] at hc2
        simp only [hc1, hc2] at h
        rcases Nat.eq_or_lt_of_le hks with rfl | hlt
        · -- k = s: extract checkInvAt
          unfold checkInvAt
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          -- Extract w < n, q < d from ¬cond1
          have hc1' := hc1
          simp only [ge_iff_le, Bool.or_eq_false_iff, decide_eq_false_iff_not,
            Nat.not_le] at hc1'
          -- Extract v2*d+p2 = s from bne ... = false
          simp [bne] at hc2
          exact ⟨⟨hc1'.1, hc1'.2⟩, hc2⟩
        · -- k > s: use IH
          exact ih (s + 1) h k hlt (by omega)

set_option maxHeartbeats 1600000 in
/-- From `checkInvolution = true`, extract per-index `checkInvAt` facts. -/
theorem checkInvolution_implies_checkInvAt (rotBytes : String) (n d : Nat)
    (h : checkInvolution rotBytes n d = true) :
    (rotBytes.utf8ByteSize = n * d * 2 * 5) ∧
    ∀ k, k < n * d → checkInvAt rotBytes n d k = true := by
  unfold checkInvolution at h
  by_cases hsize : rotBytes.utf8ByteSize = n * d * 2 * 5
  · simp only [hsize, bne_self_eq_false, Bool.false_eq_true, ite_false, Id.run] at h
    constructor
    · exact hsize
    · simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
        Nat.add_sub_cancel, Nat.div_one] at h
      intro k hk
      exact checkInv_loop_implies_all rotBytes n d 0 (n * d) h k (by omega) (by omega)
  · have : (rotBytes.utf8ByteSize != n * d * 2 * 5) = true := by
      simp [bne, BEq.beq]; exact hsize
    simp only [this, ite_true] at h
    exact absurd h Bool.false_ne_true

/-! **Involution → Neighbor symmetry** -/

/-! Helper lemmas -/

private theorem foldl_preserves_size {f : Array Int → Nat → Array Int}
    (hf : ∀ a i, (f a i).size = a.size) (l : List Nat) (init : Array Int) :
    (l.foldl f init).size = init.size := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih => simp [List.foldl]; rw [ih]; exact hf init x

private theorem getD_set!_eq (arr : Array Int) (i : Nat) (v : Int) (j : Nat) :
    (arr.set! i v).getD j 0 =
    if i = j ∧ i < arr.size then v else arr.getD j 0 := by
  show (arr.setIfInBounds i v).getD j 0 = _
  unfold Array.getD
  have hsz : (arr.setIfInBounds i v).size = arr.size := Array.size_setIfInBounds
  have hq := @Array.getElem?_setIfInBounds Int arr i j v
  by_cases hj : j < arr.size
  · have hjsib : j < (arr.setIfInBounds i v).size := hsz ▸ hj
    simp only [hjsib, hj, dite_true]
    by_cases hij : i = j
    · rw [if_pos ⟨hij, hij ▸ hj⟩]
      have hqj : (arr.setIfInBounds i v)[j]? = some v := by
        rw [hq, if_pos hij, if_pos (hij ▸ hj)]
      rw [Array.getElem?_eq_getElem hjsib] at hqj
      exact Option.some.inj hqj
    · rw [if_neg (fun ⟨h, _⟩ => hij h)]
      have hqj : (arr.setIfInBounds i v)[j]? = arr[j]? := by
        rw [hq, if_neg hij]
      rw [Array.getElem?_eq_getElem hjsib, Array.getElem?_eq_getElem hj] at hqj
      exact Option.some.inj hqj
  · have hjsib : ¬(j < (arr.setIfInBounds i v).size) := hsz ▸ hj
    simp only [hjsib, hj, dite_false]
    exact (if_neg (fun ⟨h1, h2⟩ => hj (h1 ▸ h2))).symm

/-- `List.foldl` congruence: if step functions agree pointwise, folds agree. -/
private theorem foldl_congr_fun {α β : Type} {f g : α → β → α} (l : List β) (init : α)
    (h : ∀ a b, f a b = g a b) :
    l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons]; rw [h]; exact ih (g init x)

/-! Port count: number of ports from v to w -/

/-- Number of ports `p < d` such that `neighbors.getD(v*d+p) 0 = w`. -/
private def portCount (neighbors : Array Nat) (d v w : Nat) : Nat :=
  Nat.fold d (fun p _ acc => if neighbors.getD (v * d + p) 0 = w then acc + 1 else acc) 0

/-- Generic: counting fold over `Int` = cast of counting fold over `Nat`. -/
private theorem count_fold_cast (m : Nat) (P : Nat → Prop) [DecidablePred P] :
    (Nat.fold m (fun p _ (acc : Int) => if P p then acc + 1 else acc) (0 : Int)) =
    ↑(Nat.fold m (fun p _ (acc : Nat) => if P p then acc + 1 else acc) (0 : Nat)) := by
  suffices ∀ (initI : Int) (initN : Nat), initI = ↑initN →
    Nat.fold m (fun p _ (acc : Int) => if P p then acc + 1 else acc) initI =
    ↑(Nat.fold m (fun p _ (acc : Nat) => if P p then acc + 1 else acc) initN) from
    this 0 0 (by simp)
  intro initI initN hinit
  induction m generalizing initI initN with
  | zero => simp [Nat.fold_zero, hinit]
  | succ m ih =>
    rw [Nat.fold_succ, Nat.fold_succ]
    split
    · have := ih initI initN hinit; push_cast at this ⊢; omega
    · exact ih _ _ hinit

/-- Int-valued counting fold equals Nat-valued portCount cast to Int. -/
private theorem count_fold_eq_portCount (neighbors : Array Nat) (d v w : Nat) :
    (Nat.fold d (fun p _ (acc : Int) => if neighbors.getD (v * d + p) 0 = w then acc + 1 else acc) (0 : Int)) =
    (portCount neighbors d v w : Int) := by
  unfold portCount
  exact count_fold_cast d (fun p => neighbors.getD (v * d + p) 0 = w)

/-! **checkInvAt properties** -/

/-- From `checkInvAt k = true`, extract vertex bound, port bound, and round-trip. -/
private theorem checkInvAt_spec (rotBytes : String) (n d k : Nat)
    (h : checkInvAt rotBytes n d k = true) :
    decodeBase85Nat rotBytes (2 * k) < n ∧
    decodeBase85Nat rotBytes (2 * k + 1) < d ∧
    decodeBase85Nat rotBytes (2 * (decodeBase85Nat rotBytes (2 * k) * d +
      decodeBase85Nat rotBytes (2 * k + 1))) * d +
    decodeBase85Nat rotBytes (2 * (decodeBase85Nat rotBytes (2 * k) * d +
      decodeBase85Nat rotBytes (2 * k + 1)) + 1) = k := by
  unfold checkInvAt at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- Decoded neighbors are in-bounds. -/
private theorem decoded_neighbor_bound (rotBytes : String) (n d : Nat)
    (hall : ∀ k, k < n * d → checkInvAt rotBytes n d k = true) :
    ∀ k, k < n * d → (decodeNeighbors rotBytes n d).getD k 0 < n := by
  intro k hk
  rw [decodeNeighbors_getD rotBytes n d k hk]
  exact (checkInvAt_spec rotBytes n d k (hall k hk)).1

/-! **Scatter characterization** -/

/-- Size of scatter inner loop output equals input size. -/
private theorem scatter_inner_size_getD (neighbors : Array Nat) (val : Int)
    (d offset : Nat) (bz : Array Int) :
    ((List.range' 0 d).foldl (fun bz' (p : Nat) =>
      bz'.set! (neighbors.getD (offset + p) 0) (bz'.getD (neighbors.getD (offset + p) 0) 0 + val)) bz).size = bz.size :=
  foldl_preserves_size (fun a _ => by simp [Array.set!, Array.size_setIfInBounds]) _ bz

/-- Scatter inner loop characterization: after processing all d ports starting at offset,
    `bz'[w] = bz[w] + count * val` where count = #{p < d : N[offset+p] = w}.
    All target positions must be in-bounds. -/
private theorem scatter_inner_getD (neighbors : Array Nat) (val : Int)
    (d offset : Nat) (bz : Array Int) (w : Nat) (hw : w < bz.size)
    (htarget : ∀ p, p < d → neighbors.getD (offset + p) 0 < bz.size) :
    ((List.range' 0 d).foldl (fun bz' (p : Nat) =>
      bz'.set! (neighbors.getD (offset + p) 0) (bz'.getD (neighbors.getD (offset + p) 0) 0 + val)) bz).getD w 0 =
    bz.getD w 0 + (Nat.fold d (fun p _ acc => if neighbors.getD (offset + p) 0 = w then acc + 1 else acc) 0 : Int) * val := by
  induction d generalizing bz with
  | zero => simp [List.range', Nat.fold_zero]
  | succ d ih =>
    rw [range'_zero_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil, Nat.fold_succ]
    set bz_mid := (List.range' 0 d).foldl _ bz
    have hsize_mid : bz_mid.size = bz.size :=
      scatter_inner_size_getD neighbors val d offset bz
    have hw_mid : w < bz_mid.size := hsize_mid ▸ hw
    have htgt_mid : ∀ p, p < d → neighbors.getD (offset + p) 0 < bz_mid.size := by
      intro p hp; rw [hsize_mid]; exact htarget p (by omega)
    have ih_val := ih bz hw (fun p hp => htarget p (by omega))
    -- Process port d: set! target (bz_mid.getD target 0 + val) at target = N[offset+d]
    set tgt := neighbors.getD (offset + d) 0
    have htgt : tgt < bz_mid.size := hsize_mid ▸ htarget d (by omega)
    rw [getD_set!_eq]
    rw [ih_val]
    -- Case split on whether tgt = w
    by_cases htw : tgt = w
    · rw [if_pos ⟨htw, htgt⟩, if_pos (show neighbors.getD (offset + d) 0 = w from htw)]
      -- bz_mid.getD tgt 0 = bz.getD w 0 + count_d * val
      have ih_tgt : bz_mid.getD tgt 0 =
          bz.getD tgt 0 + (Nat.fold d (fun p _ acc => if neighbors.getD (offset + p) 0 = tgt then acc + 1 else acc) 0 : Int) * val := by
        rw [htw]; exact ih bz hw (fun p hp => htarget p (by omega))
      rw [ih_tgt, htw]
      rw [Int.add_mul]; omega
    · rw [if_neg (fun ⟨h, _⟩ => htw h),
          if_neg (show ¬(neighbors.getD (offset + d) 0 = w) from htw)]

/-- The `getD`-based scatter: equivalent to `scatterMulAdj` when indices are in-bounds. -/
private def scatterGetD (neighbors : Array Nat) (zCol : Array Int) (n d nz : Nat) : Array Int :=
  (List.range' 0 nz).foldl (fun bz k =>
    (List.range' 0 d).foldl (fun bz' p =>
      let w := neighbors.getD (k * d + p) 0
      bz'.set! w (bz'.getD w 0 + zCol.getD k 0)) bz)
  (Array.replicate n (0 : Int))

private theorem scatterGetD_size (neighbors : Array Nat) (zCol : Array Int) (n d nz : Nat) :
    (scatterGetD neighbors zCol n d nz).size = n := by
  unfold scatterGetD
  rw [foldl_preserves_size (fun acc k =>
    foldl_preserves_size (fun a _ => by simp [Array.set!, Array.size_setIfInBounds]) _ acc) _ _]
  exact Array.size_replicate

/-- `scatterGetD` characterization: getD at position `w` after processing `nz` source vertices. -/
private theorem scatterGetD_getD (neighbors : Array Nat) (zCol : Array Int)
    (n d nz : Nat) (w : Nat) (hw : w < n)
    (htarget : ∀ k, k < nz → ∀ p, p < d → neighbors.getD (k * d + p) 0 < n) :
    (scatterGetD neighbors zCol n d nz).getD w 0 =
    Nat.fold nz (fun k _ acc => acc + (portCount neighbors d k w : Int) * zCol.getD k 0) 0 := by
  unfold scatterGetD
  induction nz with
  | zero =>
    simp only [List.range', List.foldl_nil, Nat.fold_zero]
    show (Array.replicate n (0 : Int)).getD w 0 = 0
    unfold Array.getD; simp [hw, Array.size_replicate]
  | succ nz ih =>
    rw [range'_zero_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil, Nat.fold_succ]
    set bz_mid := (List.range' 0 nz).foldl _ (Array.replicate n (0 : Int))
    have ih_val := ih (fun k hk p hp => htarget k (by omega) p hp)
    have hsize_mid : bz_mid.size = n := scatterGetD_size neighbors zCol n d nz
    have hw_mid : w < bz_mid.size := hsize_mid ▸ hw
    have htgt_mid : ∀ p, p < d → neighbors.getD (nz * d + p) 0 < bz_mid.size := by
      intro p hp; rw [hsize_mid]; exact htarget nz (by omega) p hp
    -- Apply inner loop characterization
    rw [scatter_inner_getD neighbors (zCol.getD nz 0) d (nz * d) bz_mid w hw_mid htgt_mid]
    rw [ih_val]
    -- portCount matches the count from scatter_inner_getD
    congr 1; congr 1; exact count_fold_eq_portCount neighbors d nz w

/-- `scatterMulAdj = scatterGetD` when the neighbor array and zCol have sufficient size.
    This bridges `getElem!` (panicking) with `getD` (defaulting to 0). -/
private theorem scatterMulAdj_eq_scatterGetD (neighbors : Array Nat) (zCol : Array Int)
    (n d nz : Nat) :
    scatterMulAdj neighbors zCol n d nz = scatterGetD neighbors zCol n d nz := by
  simp [scatterMulAdj, Id.run]
  show (List.foldl
    (fun b a =>
      List.foldl (fun b a_1 => b.setIfInBounds neighbors[a * d + a_1]! (b[neighbors[a * d + a_1]!]! + zCol[a]!)) b
        (List.range' 0 d))
    (Array.replicate n 0) (List.range' 0 nz)) = scatterGetD neighbors zCol n d nz
  simp only [scatterGetD, Array.set!]
  apply foldl_congr_fun
  intro bz k
  apply foldl_congr_fun
  intro bz' p
  simp only [Array.getElem!_eq_getD]; rfl

/-- Scatter outer loop: after processing all sources `k < nz`,
    `scatter[w] = ∑_{k<nz} portCount(k,w) * z[k]`. -/
private theorem scatter_outer_getD (neighbors : Array Nat) (zCol : Array Int)
    (n d nz : Nat) (w : Nat) (hw : w < n)
    (htarget : ∀ k, k < nz → ∀ p, p < d → neighbors.getD (k * d + p) 0 < n) :
    (scatterMulAdj neighbors zCol n d nz).getD w 0 =
    Nat.fold nz (fun k _ acc => acc + (portCount neighbors d k w : Int) * zCol.getD k 0) 0 := by
  rw [scatterMulAdj_eq_scatterGetD neighbors zCol n d nz]
  exact scatterGetD_getD neighbors zCol n d nz w hw htarget

/-! **Gather characterization via portCount** -/

/-- The gather sum `∑_{p<d} z[N[w*d+p]]` using getD. -/
private theorem gather_getD_eq_port_sum (neighbors : Array Nat) (z : Array Int)
    (n d w : Nat) (hw : w < n) :
    (mulAdjPre neighbors z n d).getD w 0 =
    Nat.fold d (fun p _ acc => acc + z.getD (neighbors.getD (w * d + p) 0) 0) 0 := by
  show (mulAdjWith _ z n d).getD w 0 = _
  rw [mulAdjWith_getD _ z n d w hw]
  simp only [Array.getElem!_eq_getD]; rfl

/-- Decompose count at `d+1` into count at `d` + indicator. -/
private theorem count_step (neighbors : Array Nat) (d offset v : Nat) :
    (Nat.fold (d + 1) (fun p _ acc => if neighbors.getD (offset + p) 0 = v then acc + 1 else acc) 0 : Int) =
    (Nat.fold d (fun p _ acc => if neighbors.getD (offset + p) 0 = v then acc + 1 else acc) 0 : Int) +
    if neighbors.getD (offset + d) 0 = v then 1 else 0 := by
  rw [Nat.fold_succ]
  by_cases h : neighbors.getD (offset + d) 0 = v
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

set_option maxHeartbeats 3200000 in
/-- Regrouping: `∑_{p<d} f(N[offset+p])` equals `∑_{v<n} portCount * f(v)`. -/
private theorem fold_regroup_by_target (neighbors : Array Nat) (f : Nat → Int)
    (d offset n : Nat)
    (hbnd : ∀ p, p < d → neighbors.getD (offset + p) 0 < n) :
    Nat.fold d (fun p _ acc => acc + f (neighbors.getD (offset + p) 0)) 0 =
    Nat.fold n (fun v _ acc =>
      acc + (Nat.fold d (fun p _ acc => if neighbors.getD (offset + p) 0 = v then acc + 1 else acc) 0 : Int) * f v) 0 := by
  induction d with
  | zero =>
    simp only [Nat.fold_zero]
    exact (fold_zero_terms n 0 (fun v => (0 : Int) * f v) (fun _ _ => by simp)).symm
  | succ d ih =>
    rw [Nat.fold_succ, ih (fun p hp => hbnd p (by omega))]
    set target := neighbors.getD (offset + d) 0
    have htarget : target < n := hbnd d (by omega)
    symm
    rw [fold_congr_acc n
      (fun v => (Nat.fold (d + 1) (fun p _ a => if neighbors.getD (offset + p) 0 = v then a + 1 else a) 0 : Int) * f v)
      (fun v => (Nat.fold d (fun p _ a => if neighbors.getD (offset + p) 0 = v then a + 1 else a) 0 : Int) * f v +
        (if neighbors.getD (offset + d) 0 = v then 1 else 0 : Int) * f v)
      0
      (fun v _ => by dsimp only []; rw [count_step]; exact Int.add_mul _ _ _)]
    rw [fold_add_distrib]
    congr 1
    rw [fold_congr_acc n
      (fun v => (if neighbors.getD (offset + d) 0 = v then 1 else 0 : Int) * f v)
      (fun v => if v = target then f target else 0) 0
      (fun v _ => by
        dsimp only []
        by_cases h : neighbors.getD (offset + d) 0 = v
        · rw [if_pos h, Int.one_mul, if_pos (show v = target from h ▸ rfl)]
          exact congrArg f h.symm
        · rw [if_neg h, Int.zero_mul, if_neg (show ¬(v = target) from fun hc => h (hc ▸ rfl))])]
    exact fold_ite_eq n target htarget (f target)

/-- `w * d + p < n * d` from `w < n` and `p < d`. -/
private theorem mul_add_lt_mul {w n p d : Nat} (hw : w < n) (hp : p < d) : w * d + p < n * d := by
  calc w * d + p < w * d + d := by omega
    _ = (w + 1) * d := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ n * d := Nat.mul_le_mul_right d (by omega)

/-- `mulAdjPre[w]` rewritten as portCount sum. -/
private theorem gather_getD_eq_portCount_sum (neighbors : Array Nat) (z : Array Int)
    (n d w : Nat) (hw : w < n)
    (hbnd : ∀ k, k < n * d → neighbors.getD k 0 < n) :
    (mulAdjPre neighbors z n d).getD w 0 =
    Nat.fold n (fun v _ acc => acc + (portCount neighbors d w v : Int) * z.getD v 0) 0 := by
  rw [gather_getD_eq_port_sum neighbors z n d w hw]
  rw [fold_regroup_by_target neighbors (fun v => z.getD v 0) d (w * d) n
    (fun p hp => hbnd (w * d + p) (mul_add_lt_mul hw hp))]
  exact fold_congr_acc n
    (fun v => (Nat.fold d (fun p _ (acc : Int) => if neighbors.getD (w * d + p) 0 = v then acc + 1 else acc) 0) * z.getD v 0)
    (fun v => (portCount neighbors d w v : Int) * z.getD v 0)
    0
    (fun v _ => by dsimp only []; congr 1; exact count_fold_eq_portCount neighbors d w v)

/-! **Port count symmetry from involution** -/

/-! Helper: `portCount` in "acc + indicator" form -/
private theorem portCount_as_sum (neighbors : Array Nat) (d v w : Nat) :
    portCount neighbors d v w =
    Nat.fold d (fun p _ acc => acc + if neighbors.getD (v * d + p) 0 = w then 1 else 0) 0 := by
  unfold portCount; congr 1; ext p _ acc; split <;> omega

/-! Helpers for block extraction from nested fold -/
private theorem fold_block_neq (d u v w : Nat) (huv : u ≠ v) (N : Array Nat) (init : Nat) :
    Nat.fold d (fun p _ acc =>
      acc + if u = v ∧ N.getD (u * d + p) 0 = w then 1 else 0) init = init := by
  suffices ∀ m, m ≤ d → Nat.fold m (fun p _ acc =>
      acc + if u = v ∧ N.getD (u * d + p) 0 = w then 1 else 0) init = init by
    exact this d (Nat.le_refl d)
  intro m; induction m with
  | zero => intros; simp [Nat.fold_zero]
  | succ m ih =>
    intro hm; rw [Nat.fold_succ, if_neg (fun ⟨h, _⟩ => huv h), Nat.add_zero]; exact ih (by omega)

private theorem nested_all_zero : ∀ (n d v w : Nat) (N : Array Nat),
    (∀ u, u < n → u ≠ v) →
    Nat.fold n (fun u _ acc_u =>
      Nat.fold d (fun p _ acc_p =>
        acc_p + if u = v ∧ N.getD (u * d + p) 0 = w then 1 else 0) acc_u) 0 = 0 := by
  intro n; induction n with
  | zero => intros; simp [Nat.fold_zero]
  | succ n ih =>
    intro d v w N hall
    rw [Nat.fold_succ, fold_block_neq d n v w (hall n (by omega)) N]
    exact ih d v w N (fun u hu => hall u (by omega))

/-- In a nested fold over `n` blocks of size `d`, only the `v`-th block contributes
    when the indicator filters on `u = v`. -/
private theorem nested_extract_block : ∀ (n d v w : Nat), v < n → ∀ (N : Array Nat),
    Nat.fold n (fun u _ acc_u =>
      Nat.fold d (fun p _ acc_p =>
        acc_p + if u = v ∧ N.getD (u * d + p) 0 = w then 1 else 0) acc_u) 0 =
    Nat.fold d (fun p _ acc => acc + if N.getD (v * d + p) 0 = w then 1 else 0) 0 := by
  intro n; induction n with
  | zero => intros; omega
  | succ n ih =>
    intro d v w hv N; rw [Nat.fold_succ]
    by_cases hnv : n = v
    · subst hnv; rw [nested_all_zero n d n w N (fun u hu => by omega)]
      congr 1; ext p _ acc; congr 1; simp only [true_and]
    · rw [fold_block_neq d n v w hnv N]; exact ih d v w (by omega) N

/-- Division of `u*d+p` by `d` when `p < d`. -/
private theorem mul_add_div_eq (u d p : Nat) (hd : 0 < d) (hp : p < d) :
    (u * d + p) / d = u := by
  rw [show u * d + p = p + u * d from by omega, Nat.add_mul_div_right p u hd,
      Nat.div_eq_of_lt hp, Nat.zero_add]

/-- `portCount(v,w) = flat count over `{0,...,n*d-1}` of `[k/d=v ∧ N[k]=w]`. -/
private theorem portCount_eq_flat_count (N : Array Nat) (n d v w : Nat) (hv : v < n)
    (hd : 0 < d) :
    portCount N d v w =
    Nat.fold (n * d) (fun k _ acc =>
      acc + if k / d = v ∧ N.getD k 0 = w then 1 else 0) 0 := by
  rw [portCount_as_sum, ← nested_extract_block n d v w hv N, ← fold_nested_to_flat_nat n d]
  congr 1; ext u _ acc_u; congr 1; ext p hp acc_p; congr 1
  have hdiv : (u * d + p) / d = u := mul_add_div_eq u d p hd hp
  rw [hdiv]

/-- The rotation map involution induces a bijection between
    `{p < d : N[v*d+p] = w}` and `{q < d : N[w*d+q] = v}`,
    so `portCount(v,w) = portCount(w,v)`. -/
private theorem portCount_symm (neighbors : Array Nat) (rotBytes : String)
    (n d v w : Nat) (hv : v < n) (hw : w < n)
    (hneq : neighbors = decodeNeighbors rotBytes n d)
    (hall : ∀ k, k < n * d → checkInvAt rotBytes n d k = true) :
    portCount neighbors d v w = portCount neighbors d w v := by
  -- Handle d = 0 trivially
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [portCount, Nat.fold_zero]
  -- Define the rotation function
  let rot : Nat → Nat := fun k =>
    decodeBase85Nat rotBytes (2 * k) * d + decodeBase85Nat rotBytes (2 * k + 1)
  -- Key properties from checkInvAt
  have hrot_bound : ∀ k, k < n * d → rot k < n * d := by
    intro k hk
    have spec := checkInvAt_spec rotBytes n d k (hall k hk)
    show decodeBase85Nat rotBytes (2 * k) * d + decodeBase85Nat rotBytes (2 * k + 1) < n * d
    calc decodeBase85Nat rotBytes (2 * k) * d + decodeBase85Nat rotBytes (2 * k + 1)
        < decodeBase85Nat rotBytes (2 * k) * d + d := by omega
      _ = (decodeBase85Nat rotBytes (2 * k) + 1) * d := (Nat.succ_mul _ d).symm
      _ ≤ n * d := Nat.mul_le_mul_right d (Nat.succ_le_of_lt spec.1)
  have hrot_inv : ∀ k, k < n * d → rot (rot k) = k := by
    intro k hk
    exact (checkInvAt_spec rotBytes n d k (hall k hk)).2.2
  -- Key: neighbors[k] = rot(k) / d
  have hneighbor_eq_div : ∀ k, k < n * d →
      neighbors.getD k 0 = rot k / d := by
    intro k hk
    have spec := checkInvAt_spec rotBytes n d k (hall k hk)
    rw [hneq, decodeNeighbors_getD rotBytes n d k hk]
    show decodeBase85Nat rotBytes (2 * k) =
      (decodeBase85Nat rotBytes (2 * k) * d + decodeBase85Nat rotBytes (2 * k + 1)) / d
    exact (mul_add_div_eq _ d _ hd spec.2.1).symm
  -- Flatten both portCounts
  rw [portCount_eq_flat_count neighbors n d v w hv hd,
      portCount_eq_flat_count neighbors n d w v hw hd]
  -- Apply involution to the LHS
  rw [fold_sum_invol (n * d) rot
    (fun k => if k / d = v ∧ neighbors.getD k 0 = w then 1 else 0)
    hrot_bound hrot_inv]
  -- Now LHS counts: ∑_k [rot(k)/d = v ∧ N[rot(k)] = w]
  -- Transform: rot(k)/d = N[k] and N[rot(k)] = k/d
  apply fold_congr_acc_nat
  intro k hk
  -- Show the indicators are equal after the rotation
  -- rot(k)/d = neighbors[k] and neighbors[rot(k)] = k/d
  have hneq1 : (rot k) / d = neighbors.getD k 0 := by
    rw [hneighbor_eq_div k hk]
  have hneq2 : neighbors.getD (rot k) 0 = k / d := by
    rw [hneighbor_eq_div (rot k) (hrot_bound k hk)]
    congr 1; exact hrot_inv k hk
  show (if (rot k) / d = v ∧ neighbors.getD (rot k) 0 = w then 1 else 0) =
       (if k / d = w ∧ neighbors.getD k 0 = v then 1 else 0)
  rw [hneq1, hneq2]
  -- Goal: (if N[k] = v ∧ k/d = w then 1 else 0) = (if k/d = w ∧ N[k] = v then 1 else 0)
  simp only [and_comm]

/-! **Main theorem** -/

set_option maxHeartbeats 800000 in
/-- From `checkInvolution = true`, derive `NeighborSymm` for decoded neighbors. -/
theorem checkInvolution_implies_neighborSymm (rotBytes : String) (n d : Nat)
    (h : checkInvolution rotBytes n d = true) :
    NeighborSymm (decodeNeighbors rotBytes n d) n d := by
  obtain ⟨_, hall⟩ := checkInvolution_implies_checkInvAt rotBytes n d h
  intro z hz w hw nz hnz hzero
  have hbnd := decoded_neighbor_bound rotBytes n d hall
  have htarget : ∀ k, k < nz → ∀ p, p < d →
      (decodeNeighbors rotBytes n d).getD (k * d + p) 0 < n := by
    intro k hk p hp; exact hbnd (k * d + p) (mul_add_lt_mul (Nat.lt_of_lt_of_le hk hnz) hp)
  have hnsz : (decodeNeighbors rotBytes n d).size = n * d := by
    unfold decodeNeighbors; exact Array.size_ofFn
  rw [scatter_outer_getD _ _ n d nz w hw htarget]
  rw [gather_getD_eq_portCount_sum _ z n d w hw hbnd]
  -- scatter[w] = ∑_{k<nz} portCount(k,w) * z.getD k 0
  -- gather[w] = ∑_{v<n} portCount(w,v) * z.getD v 0
  set N := decodeNeighbors rotBytes n d
  -- Step 1: replace portCount(w,v) with portCount(v,w) using symmetry
  have hsymm := fold_congr_step n (fun v acc =>
      acc + (portCount N d w v : Int) * z.getD v 0)
    (fun v acc => acc + (portCount N d v w : Int) * z.getD v 0) 0
    (fun v hv acc => by
      dsimp only []
      congr 1; congr 1
      exact_mod_cast portCount_symm N rotBytes n d w v hw hv rfl hall)
  rw [hsymm]
  -- Step 2: split gather at nz
  rw [fold_split_add n nz hnz]
  -- Step 3: tail terms vanish since z[v]=0 for v >= nz
  rw [fold_zero_terms (n - nz) _ (fun k =>
      (portCount N d (nz + k) w : Int) * z.getD (nz + k) 0)
    (fun k _ => by dsimp only []; rw [hzero (nz + k) (by omega)]; simp)]

/-- From `checkInvolution = true`, all neighbors are in-bounds. -/
theorem checkInvolution_neighbor_lt' (rotBytes : String) (n d : Nat)
    (h : checkInvolution rotBytes n d = true) :
    ∀ k, k < n * d → (decodeNeighbors rotBytes n d).getD k 0 < n := by
  obtain ⟨_, hall⟩ := checkInvolution_implies_checkInvAt rotBytes n d h
  intro k hk
  rw [decodeNeighbors_getD rotBytes n d k hk]
  have hka := hall k hk
  unfold checkInvAt at hka
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hka
  exact hka.1.1

/-! **Array-level scatter = gather** -/

theorem scatterMulAdj_size (neighbors : Array Nat) (zCol : Array Int) (n d nz : Nat) :
    (scatterMulAdj neighbors zCol n d nz).size = n := by
  simp [scatterMulAdj, Id.run]
  show (List.foldl _ (Array.replicate n 0) (List.range' 0 nz)).size = n
  rw [foldl_preserves_size]
  · exact Array.size_replicate
  · intro acc k
    exact foldl_preserves_size (fun _ _ => Array.size_setIfInBounds) (List.range' 0 d) acc

/-- Under `NeighborSymm`, `scatterMulAdj` = `mulAdjPre` (array equality). -/
theorem scatterMulAdj_eq_mulAdjPre (neighbors : Array Nat) (z : Array Int) (n d nz : Nat)
    (hnz : nz ≤ n) (hsize : z.size = n)
    (hsym : NeighborSymm neighbors n d)
    (hzero : ∀ k, k ≥ nz → z.getD k 0 = 0) :
    scatterMulAdj neighbors z n d nz = mulAdjPre neighbors z n d := by
  apply Array.ext
  · rw [scatterMulAdj_size, mulAdjPre_size]
  · intro i hi _
    have hin : i < n := by rw [scatterMulAdj_size] at hi; exact hi
    have h1 : (scatterMulAdj neighbors z n d nz)[i] =
      (scatterMulAdj neighbors z n d nz).getD i 0 := by
      simp [Array.getD, scatterMulAdj_size, hin]
    have h2 : (mulAdjPre neighbors z n d)[i] =
      (mulAdjPre neighbors z n d).getD i 0 := by
      simp [Array.getD, mulAdjPre_size, hin]
    rw [h1, h2]
    exact hsym z hsize i hin nz hnz hzero

end
