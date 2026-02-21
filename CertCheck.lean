/-
  # PSD Certificate Checker (precompiled)

  Decidable checks for `native_decide`:
  1. Rotation map is a valid involution (proves `RegularGraph`)
  2. `M = c₁I − c₂B² + c₃J` is positive definite via triangular certificate

  All data is base-85 encoded as `String` literals for compact storage.
  Each i32 value (interpreted as unsigned u32) is encoded as 5 ASCII chars
  (codepoints 33–117). Decoding uses `String.toUTF8` + `ByteArray.get!`.

  This file imports only `Init` (no Mathlib) so it can be precompiled into a
  shared library via `precompileModules := true` in `lakefile.lean`.

  **Keep this file minimal:** only runtime definitions used by `native_decide`,
  plus shared helpers (`sumTo`, `certEntryInt`, `intAbs`, `zColNormPure`) used by
  both runtime and proof-only code. Proof-only definitions go in `AKS/Cert/Defs.lean`.
  Proofs about these functions go in `AKS/Cert/Bridge.lean` (which can import Mathlib).
-/


/-! **Base-85 decoding** -/

/-- Decode the `k`-th unsigned i32 value from base-85 encoded bytes as `Nat`. -/
def decodeBase85Nat (bytes : ByteArray) (k : Nat) : Nat :=
  let pos := 5 * k
  let c0 := (bytes.get! pos).toNat - 33
  let c1 := (bytes.get! (pos + 1)).toNat - 33
  let c2 := (bytes.get! (pos + 2)).toNat - 33
  let c3 := (bytes.get! (pos + 3)).toNat - 33
  let c4 := (bytes.get! (pos + 4)).toNat - 33
  c0 + 85 * (c1 + 85 * (c2 + 85 * (c3 + 85 * c4)))

/-- Decode the `k`-th signed i32 value from base-85 encoded bytes as `Int`. -/
def decodeBase85Int (bytes : ByteArray) (k : Nat) : Int :=
  let u := decodeBase85Nat bytes k
  if u < 2^31 then (u : Int) else (u : Int) - (2^32 : Int)


/-! **Rotation map validation** -/

/-- Check that a base-85 encoded rotation map represents a valid involution.
    The rotation map has `n*d` pairs `(vertex, port)` as consecutive entries:
    entry `2*k` = destination vertex, entry `2*k+1` = destination port. -/
def checkInvolution (rotBytes : ByteArray) (n d : Nat) : Bool :=
  let nd := n * d
  if rotBytes.size != nd * 2 * 5 then false
  else Id.run do
    let mut ok := true
    for k in [:nd] do
      let w := decodeBase85Nat rotBytes (2 * k)
      let q := decodeBase85Nat rotBytes (2 * k + 1)
      if w >= n || q >= d then
        ok := false
        break
      let k2 := w * d + q
      let v2 := decodeBase85Nat rotBytes (2 * k2)
      let p2 := decodeBase85Nat rotBytes (2 * k2 + 1)
      if v2 * d + p2 != k then
        ok := false
        break
    return ok


/-! **Sparse matrix-vector product via rotation map** -/

/-- Common `mulAdj` parameterized by neighbor lookup function.
    `(mulAdjWith f z n d)[v] = ∑_{p<d} z[f(v*d+p)]!`. -/
@[inline] def mulAdjWith (getNeighbor : Nat → Nat) (z : Array Int)
    (n d : Nat) : Array Int :=
  .ofFn fun (v : Fin n) => Id.run do
    let mut acc : Int := 0
    for p in [:d] do
      let w := getNeighbor (v.val * d + p)
      acc := acc + z[w]!
    return acc

/-- Given base-85 encoded rotation map and vector `z`, compute `B·z` where `B`
    is the adjacency matrix. `(B·z)[v] = ∑_{p=0}^{d-1} z[neighbor(v,p)]`. -/
def mulAdj (rotBytes : ByteArray) (z : Array Int) (n d : Nat) : Array Int :=
  mulAdjWith (fun k => decodeBase85Nat rotBytes (2 * k)) z n d

/-- Pre-decode all neighbor vertices from the rotation map. -/
def decodeNeighbors (rotBytes : ByteArray) (n d : Nat) : Array Nat :=
  .ofFn (n := n * d) fun k => decodeBase85Nat rotBytes (2 * k.val)

/-- `mulAdj` with pre-decoded neighbor array. -/
def mulAdjPre (neighbors : Array Nat) (z : Array Int) (n d : Nat) : Array Int :=
  mulAdjWith (fun k => neighbors[k]!) z n d

/-- Single entry of `mulAdj`: `(B·z)[i] = ∑_{p<d} z[neighbors[i*d+p]]`.
    No array allocation — used to inline the second `mulAdj` in `psdColumnStep`. -/
@[inline] def mulAdjEntry (neighbors : Array Nat) (z : Array Int)
    (d i : Nat) : Int :=
  Id.run do
    let mut acc : Int := 0
    for p in [:d] do acc := acc + z[neighbors[i * d + p]!]!
    return acc


/-- Scatter-based `mulAdj`: compute `B·z` by iterating over nonzero entries of `z`
    (indices `0..nzCount-1`) and distributing contributions to neighbors.
    Equivalent to `mulAdjPre` when `z[k] = 0` for `k ≥ nzCount`. -/
@[inline] def scatterMulAdj (neighbors : Array Nat) (zCol : Array Int)
    (n d nzCount : Nat) : Array Int :=
  Id.run do
    let mut bz := Array.replicate n (0 : Int)
    for k in [:nzCount] do
      let zk := zCol[k]!
      for p in [:d] do
        let w := neighbors[k * d + p]!
        bz := bz.set! w (bz[w]! + zk)
    return bz


/-! **Diagonal positivity check** -/

/-- Check that all diagonal entries `Z[j,j]` in the packed certificate are positive.
    Column `j` of the upper-triangular matrix `Z` is stored at byte positions
    `j*(j+1)/2 + k` for `k = 0..j`, so `Z[j,j]` is at index `j*(j+1)/2 + j`. -/
def allDiagPositive (certBytes : ByteArray) (n : Nat) : Bool :=
  match n with
  | 0 => true
  | k + 1 =>
    allDiagPositive certBytes k &&
    decide (0 < decodeBase85Int certBytes (k * (k + 1) / 2 + k))


/-! **PSD Certificate Check** -/

/-- Per-chunk result from parallel PSD computation. -/
structure PSDChunkResult where
  epsMax : Int
  minDiag : Int
  first : Bool
  deriving Inhabited

/-- Merge two chunk results by taking the max epsMax and min minDiag. -/
def PSDChunkResult.merge (a b : PSDChunkResult) : PSDChunkResult :=
  if a.first then b
  else if b.first then a
  else {
    epsMax := if a.epsMax > b.epsMax then a.epsMax else b.epsMax
    minDiag := if a.minDiag < b.minDiag then a.minDiag else b.minDiag
    first := false
  }

/-- Per-column PSD update: process column `j`, return updated state.
    Uses scatter-based `mulAdj` for the first `B·z` (O((j+1)·d) instead of O(n·d))
    and `mulAdjEntry` for `(B²·z)[i]` inline (only for `i ≤ j`). -/
@[inline] def psdColumnStep (neighbors : Array Nat) (d : Nat)
    (certBytes : ByteArray) (n : Nat) (c₁ c₂ c₃ : Int)
    (state : PSDChunkResult) (j : Nat) (hj : j < n) : PSDChunkResult :=
  let colStart := j * (j + 1) / 2
  let zCol : Array Int := .ofFn fun (i : Fin n) =>
    if i.val ≤ j then decodeBase85Int certBytes (colStart + i.val) else 0
  let bz := mulAdjPre neighbors zCol n d
  let colSum := Id.run do
    let mut s : Int := 0
    for h : k in [:j+1] do
      have : k < zCol.size := by rw [Array.size_ofFn]; have := h.upper; simp at this; omega
      s := s + zCol[k]
    return s
  Id.run do
    let mut epsMax := state.epsMax
    let mut minDiag := state.minDiag
    let mut first := state.first
    for h : i in [:j+1] do
      have : i < zCol.size := by rw [Array.size_ofFn]; have := h.upper; simp at this; omega
      let pij := c₁ * zCol[i] - c₂ * mulAdjEntry neighbors bz d i + c₃ * colSum
      if i == j then
        if first then minDiag := pij; first := false
        else if pij < minDiag then minDiag := pij
      else if i < j then
        let absPij := if pij >= 0 then pij else -pij
        if absPij > epsMax then epsMax := absPij
    return { epsMax, minDiag, first }

/-- Process a subset of columns using pre-decoded neighbors, returning
    epsMax (max off-diagonal `|P[i,j]|` for `i < j`) and minDiag (min `P[j,j]`).
    Uses `mulAdjPre` (gather-based, not scatter), so the computation is
    structurally identical to `checkPSDCertificate` per-column via shared
    `psdColumnStep`. -/
def checkPSDColumns (neighbors : Array Nat) (certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : Int) (columns : Array (Fin n)) : PSDChunkResult :=
  let step := psdColumnStep neighbors d certBytes n c₁ c₂ c₃
  Id.run do
    let mut state : PSDChunkResult := { epsMax := 0, minDiag := 0, first := true }
    for jf in columns do state := step state jf.val jf.isLt
    return state

/-- Build interleaved column partition: column `j` goes to chunk `j % numChunks`.
    Shared between sequential and parallel PSD checks. -/
def buildColumnLists (n numChunks : Nat) : Array (Array (Fin n)) :=
  Id.run do
    let mut lists := Array.replicate numChunks (Array.mkEmpty (n / numChunks + 1))
    for h : j in [:n] do
      have hj : j < n := by have := h.upper; simp at this; omega
      let c := j % numChunks
      lists := lists.set! c (lists[c]!.push ⟨j, hj⟩)
    return lists

/-- Merge an array of chunk results into a single result, then check the
    Gershgorin threshold. Shared between sequential and parallel PSD checks. -/
@[inline] def checkPSDThreshold (results : Array PSDChunkResult)
    (n : Nat) : Bool :=
  let merged := results.foldl PSDChunkResult.merge
    { epsMax := 0, minDiag := 0, first := true }
  if merged.first then false
  else decide (merged.minDiag > merged.epsMax * (n * (n + 1) / 2))

/-- Check the PSD certificate for `M = c₁I − c₂B² + c₃J`.

    For each column `j` of `Z_int` (column-major packed, base-85 decoded):
    - Extract `z = Z_int[:,j]` from packed format
    - Compute `P[:,j] = M · z` using `c₁·z − c₂·B·(B·z) + c₃·(1ᵀz)·1`
    - Track `ε_max` (max upper-triangle `|P[i,j]|` for `i < j`)
    - Track `min_diag` (min diagonal `P[i,i]`)

    Then verify: `min_diag > ε_max · n · (n+1) / 2` (Gershgorin condition)
    AND all diagonal entries `Z[j,j] > 0`.

    Uses partition + merge structure (matching `checkPSDCertificatePar`) so the
    bridge `checkCertificate = checkCertificateSlow` is structurally trivial. -/
def checkPSDCertificate (rotBytes certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : Int) (tasks : Nat := 64) : Bool :=
  if certBytes.size != n * (n + 1) / 2 * 5 then false
  else allDiagPositive certBytes n &&
    let neighbors := decodeNeighbors rotBytes n d
    let columnLists := buildColumnLists n tasks
    let results := columnLists.map fun cols =>
      checkPSDColumns neighbors certBytes n d c₁ c₂ c₃ cols
    checkPSDThreshold results n


/-! **Rotation function from base-85 data** -/

/-- Decode a base-85 encoded rotation map into a rotation function `Fin n × Fin d → Fin n × Fin d`.
    Matches the `hmatch` hypothesis in `certificate_bridge`, so `(fun _ => rfl)` discharges it. -/
def rotFun (rotStr : String) (n d : Nat) (hn : 0 < n) (hd : 0 < d)
    (vp : Fin n × Fin d) : Fin n × Fin d :=
  let rotBytes := rotStr.toUTF8
  let k := vp.1.val * d + vp.2.val
  (⟨decodeBase85Nat rotBytes (2 * k) % n, Nat.mod_lt _ hn⟩,
   ⟨decodeBase85Nat rotBytes (2 * k + 1) % d, Nat.mod_lt _ hd⟩)

/-! **Pure involution spec (for `native_decide`)** -/

/-- Check involution at a single index: decoded `(w,q)` is in-bounds and round-trips. -/
def checkInvAt (rotBytes : ByteArray) (n d k : Nat) : Bool :=
  let w := decodeBase85Nat rotBytes (2 * k)
  let q := decodeBase85Nat rotBytes (2 * k + 1)
  decide (w < n) && decide (q < d) &&
  decide (decodeBase85Nat rotBytes (2 * (w * d + q)) * d +
          decodeBase85Nat rotBytes (2 * (w * d + q) + 1) = k)

/-- Check all indices from 0 to `m-1`. -/
def checkInvBelow (rotBytes : ByteArray) (n d : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => checkInvAt rotBytes n d k && checkInvBelow rotBytes n d k

/-- Pure recursive involution check. Computationally equivalent to `checkInvolution`
    but structured for formal reasoning (no imperative loop).
    Bridge proof: `checkInvolutionSpec_implies_rotFun_involution` in `CertificateBridge.lean`. -/
def checkInvolutionSpec (rotBytes : ByteArray) (n d : Nat) : Bool :=
  decide (rotBytes.size = n * d * 2 * 5) && checkInvBelow rotBytes n d (n * d)


/-! **Shared helpers for column-norm bound checking** -/

/-- Sum `f(0) + f(1) + ... + f(n-1)`. -/
def sumTo (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => sumTo f n + f n

/-- Certificate matrix entry `Z[i,j]` as integer. Zero when `i > j`. -/
def certEntryInt (certBytes : ByteArray) (i j : Nat) : Int :=
  if i ≤ j then decodeBase85Int certBytes (j * (j + 1) / 2 + i) else 0

/-- Integer absolute value. Works without Mathlib imports. -/
@[inline] def intAbs (x : Int) : Int := if x ≥ 0 then x else -x

/-- Column ℓ₁-norm of Z: `∑_{k<n} |Z[k,j]|`. -/
def zColNormPure (certBytes : ByteArray) (n j : Nat) : Int :=
  sumTo (fun k ↦ intAbs (certEntryInt certBytes k j)) n

/-- Per-row column-norm bound check. Checks rows `i, i+1, ..., i+remaining-1`.
    `prefSum` = `∑_{j<i} zColNormPure certBytes n j`. -/
def checkPerRow (certBytes : ByteArray) (n : Nat) (ε mdpe : Int)
    (remaining i : Nat) (prefSum : Int) : Bool :=
  match remaining with
  | 0 => true
  | r + 1 =>
    let si := zColNormPure certBytes n i
    let ti := prefSum + (↑(n - i) : Int) * si
    decide (certEntryInt certBytes i i * mdpe > ε * ti) &&
    checkPerRow certBytes n ε mdpe r (i + 1) (prefSum + si)

/-- Check column-norm bound: computes `epsMax`/`minDiag` via `checkPSDColumns`,
    then checks `Z[i,i]·(minDiag + epsMax) > epsMax·T_i` for each row. -/
def checkColumnNormBound (rotBytes certBytes : ByteArray) (n d : Nat)
    (c₁ c₂ c₃ : Int) (tasks : Nat := 64) : Bool :=
  if certBytes.size != n * (n + 1) / 2 * 5 then false
  else
    let neighbors := decodeNeighbors rotBytes n d
    let columnLists := buildColumnLists n tasks
    let results := columnLists.map fun cols =>
      checkPSDColumns neighbors certBytes n d c₁ c₂ c₃ cols
    let merged := results.foldl PSDChunkResult.merge
      { epsMax := 0, minDiag := 0, first := true }
    if merged.first then false
    else checkPerRow certBytes n merged.epsMax (merged.minDiag + merged.epsMax) n 0 0


/-! **Combined check** -/

/-- Full certificate check: involution + PSD + column-norm bound.
    Both rotation map and certificate are base-85 encoded `String`s.
    All sub-checks are O(n²·d), making `native_decide` feasible for n ≤ ~10000. -/
def checkCertificateSlow (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : Int) (tasks : Nat := 64) : Bool :=
  let rotBytes := rotStr.toUTF8
  let certBytes := certStr.toUTF8
  checkInvolution rotBytes n d &&
  checkPSDCertificate rotBytes certBytes n d c₁ c₂ c₃ tasks &&
  checkColumnNormBound rotBytes certBytes n d c₁ c₂ c₃ tasks


/-! **Parallel certificate checking** -/

/-- Parallel PSD certificate check: same result as `checkPSDCertificate` but
    spawns dedicated OS threads for each chunk via `Task.spawn`.

    Structure matches `checkPSDCertificate` exactly: same guards, same
    `buildColumnLists`, same `checkPSDColumns`, same `checkPSDThreshold`.
    The only difference is `Task.spawn` wrapping each chunk evaluation.
    Since `Task` is a transparent structure in Lean 4 (`Task.spawn fn = ⟨fn ()⟩`),
    the bridge `checkPSDCertificatePar = checkPSDCertificate` follows from
    `Array.map_map` + definitional unfolding. -/
def checkPSDCertificatePar (rotBytes certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : Int) (tasks : Nat := 64) : Bool :=
  if certBytes.size != n * (n + 1) / 2 * 5 then false
  else allDiagPositive certBytes n &&
    let neighbors := decodeNeighbors rotBytes n d
    let columnLists := buildColumnLists n tasks
    -- Spawn all tasks (all start running concurrently)
    let tasks := columnLists.map fun cols =>
      Task.spawn (prio := .dedicated) fun () =>
        checkPSDColumns neighbors certBytes n d c₁ c₂ c₃ cols
    -- Collect all results (each .get blocks until its task completes)
    let results := tasks.map Task.get
    checkPSDThreshold results n

/-- Process columns: PSD + column ℓ₁-norms in a single fused pass.
    Preallocates `zCol` and `bz` buffers outside the column loop and reuses them.
    The scatter is fused into the decode loop: for each decoded `z[k]`, we
    immediately distribute `z[k]` to `bz[neighbors[k*d+p]]` for all ports `p`.
    `B²z[i]` is then gathered inline from `bz`. -/
def checkPSDColumnsFull (neighbors : Array Nat) (certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : Int) (columns : Array (Fin n)) :
    PSDChunkResult × Array Int :=
  Id.run do
    let mut epsMax : Int := 0
    let mut minDiag : Int := 0
    let mut first := true
    let mut colNorms : Array Int := Array.mkEmpty columns.size
    let mut zCol := Array.replicate n (0 : Int)
    let mut bz := Array.replicate n (0 : Int)

    for jf in columns do
      let j := jf.val
      let colStart := j * (j + 1) / 2

      -- Zero bz for this column (zCol is overwritten before read, no zeroing needed)
      for v in [:n] do
        bz := bz.set! v 0

      -- Fused decode + scatter: build zCol, accumulate colSum/colNorm, scatter into bz
      let mut colSum : Int := 0
      let mut colNorm : Int := 0
      for k in [:j+1] do
        let zk := decodeBase85Int certBytes (colStart + k)
        zCol := zCol.set! k zk
        colSum := colSum + zk
        colNorm := colNorm + intAbs zk
        for p in [:d] do
          let w := neighbors[k * d + p]!
          bz := bz.set! w (bz[w]! + zk)

      -- PSD update with inline B²z[i] gathered from bz
      for i in [:j+1] do
        let mut b2zi : Int := 0
        for p in [:d] do
          let w := neighbors[i * d + p]!
          b2zi := b2zi + bz[w]!
        let pij := c₁ * zCol[i]! - c₂ * b2zi + c₃ * colSum
        if i == j then
          if first then
            minDiag := pij
            first := false
          else if pij < minDiag then
            minDiag := pij
        else if i < j then
          let absPij := if pij >= 0 then pij else -pij
          if absPij > epsMax then
            epsMax := absPij

      colNorms := colNorms.push colNorm

    return ({ epsMax, minDiag, first }, colNorms)

/-- Merged parallel certificate check: PSD + column-norm bound in one parallel pass.
    Same result as `checkCertificateSlow` (proved in `AKS/Cert/FastProof.lean`).
    Each parallel task computes both PSD state and column ℓ₁-norms via fused cert
    decode. The sequential prefix-sum check uses precomputed norms directly from
    chunk results: column `j`'s norm is `results[j % tasks].2[j / tasks]`. -/
def checkCertificate (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : Int) (tasks : Nat := 64) : Bool :=
  let rotBytes := rotStr.toUTF8
  let certBytes := certStr.toUTF8
  checkInvolution rotBytes n d &&
  if certBytes.size != n * (n + 1) / 2 * 5 then false
  else allDiagPositive certBytes n &&
    let neighbors := decodeNeighbors rotBytes n d
    let columnLists := buildColumnLists n tasks
    let spawned := columnLists.map fun cols =>
      Task.spawn (prio := .dedicated) fun () =>
        checkPSDColumnsFull neighbors certBytes n d c₁ c₂ c₃ cols
    let results := spawned.map Task.get
    let merged := (results.map (·.1)).foldl PSDChunkResult.merge
      { epsMax := 0, minDiag := 0, first := true }
    if merged.first then false
    else
      decide (merged.minDiag > merged.epsMax * (n * (n + 1) / 2)) &&
      Id.run do
        let ε := merged.epsMax
        let mdpe := merged.minDiag + ε
        let mut prefSum : Int := 0
        for i in [:n] do
          let si := results[i % tasks]!.2[i / tasks]!
          let ti := prefSum + (↑(n - i) : Int) * si
          if !(certEntryInt certBytes i i * mdpe > ε * ti) then
            return false
          prefSum := prefSum + si
        return true


