module

public import Random.Cert.ReadFFI

@[expose] public section
/-
  # PSD Certificate Checker (precompiled)

  Decidable checks for `native_decide`:
  1. Rotation map is a valid involution (proves `RegularGraph`)
  2. `M = c₁I − c₂B² + c₃J` is positive definite via triangular certificate

  All data is base-85 encoded as `String` literals for compact storage.
  Each i32 value (interpreted as unsigned u32) is encoded as 5 ASCII chars
  (codepoints 33–117). Decoding uses `String.getUTF8Byte` for zero-copy
  byte access (no `String.toUTF8` allocation).

  This lean_lib imports only `Init` (no Mathlib) so it can be precompiled into a
  shared library via `precompileModules := true` in `lakefile.lean`.
  `CertCheck.ReadFFI` provides `@[extern]` FFI declarations (`cachedString`,
  `mmapReadAscii`, `mmapPrepare`) whose `lp_` wrappers are compiled into
  `libaks_CertCheck.so`, available for `native_decide` at elaboration time.

  **Keep this file minimal:** only runtime definitions used by `native_decide`,
  plus shared helpers (`sumTo`, `certEntryInt`, `intAbs`, `zColNormPure`) used by
  both runtime and proof-only code. Proof-only definitions go in `AKS/Cert/Defs.lean`.
  Proofs about these functions go in `AKS/Cert/Bridge.lean` (which can import Mathlib).
-/


/-! **Zero-copy byte access** -/

/-- Read the `i`-th UTF-8 byte of a string without copying.
    At runtime, `String.getUTF8Byte` is `@[extern "lean_string_get_byte_fast"]`
    and `String.utf8ByteSize` is `@[extern "lean_string_utf8_byte_size"]` (O(1), cached).
    Returns 0 on out-of-bounds (matching `ByteArray.getD` default). -/
@[inline] def strGet! (s : String) (i : Nat) : UInt8 :=
  if h : i < s.utf8ByteSize then
    s.getUTF8Byte ⟨i⟩ (by simp [String.rawEndPos, String.Pos.Raw.lt_iff]; exact h)
  else
    0


/-! **Base-85 decoding** -/

/-- Decode the `k`-th unsigned i32 value from base-85 encoded string as `Nat`. -/
def decodeBase85Nat (s : String) (k : Nat) : Nat :=
  let pos := 5 * k
  let c0 := (strGet! s pos).toNat - 33
  let c1 := (strGet! s (pos + 1)).toNat - 33
  let c2 := (strGet! s (pos + 2)).toNat - 33
  let c3 := (strGet! s (pos + 3)).toNat - 33
  let c4 := (strGet! s (pos + 4)).toNat - 33
  c0 + 85 * (c1 + 85 * (c2 + 85 * (c3 + 85 * c4)))

/-- Decode the `k`-th signed i32 value from base-85 encoded string as `Int`. -/
def decodeBase85Int (s : String) (k : Nat) : Int :=
  let u := decodeBase85Nat s k
  if u < 2^31 then (u : Int) else (u : Int) - (2^32 : Int)


/-! **Compact rotation encoding** -/

/-- Convert compact 4-byte rotation encoding to standard 10-byte b85.
    Input: 4 bytes per half-edge (3 b85-encoded vertex digits + 1 b85-encoded port digit).
    Output: standard b85 string with 10 bytes per half-edge (5-byte vertex + 5-byte port).
    The `'!'` character (codepoint 33) represents base-85 digit 0. -/
def compactToB85 (s : String) : String :=
  let nd := s.utf8ByteSize / 4
  Id.run do
    let mut out : String := ""
    let bang := Char.ofNat 33
    for k in [:nd] do
      let pos := 4 * k
      out := out.push (Char.ofNat (strGet! s pos).toNat)
      out := out.push (Char.ofNat (strGet! s (pos + 1)).toNat)
      out := out.push (Char.ofNat (strGet! s (pos + 2)).toNat)
      out := out.push bang
      out := out.push bang
      out := out.push (Char.ofNat (strGet! s (pos + 3)).toNat)
      out := out.push bang
      out := out.push bang
      out := out.push bang
      out := out.push bang
    return out


/-! **Rotation map validation** -/

/-- Check that a base-85 encoded rotation map represents a valid involution.
    The rotation map has `n*d` pairs `(vertex, port)` as consecutive entries:
    entry `2*k` = destination vertex, entry `2*k+1` = destination port. -/
def checkInvolution (rotStr : String) (n d : Nat) : Bool :=
  let nd := n * d
  if rotStr.utf8ByteSize != nd * 2 * 5 then false
  else Id.run do
    let mut ok := true
    for k in [:nd] do
      let w := decodeBase85Nat rotStr (2 * k)
      let q := decodeBase85Nat rotStr (2 * k + 1)
      if w >= n || q >= d then
        ok := false
        break
      let k2 := w * d + q
      let v2 := decodeBase85Nat rotStr (2 * k2)
      let p2 := decodeBase85Nat rotStr (2 * k2 + 1)
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
def mulAdj (rotStr : String) (z : Array Int) (n d : Nat) : Array Int :=
  mulAdjWith (fun k => decodeBase85Nat rotStr (2 * k)) z n d

/-- Pre-decode all neighbor vertices from the rotation map. -/
def decodeNeighbors (rotStr : String) (n d : Nat) : Array Nat :=
  .ofFn (n := n * d) fun k => decodeBase85Nat rotStr (2 * k.val)

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

/-- Check that all diagonal entries `Z[j,j]` are positive.
    `entry j k` returns `Z[k,j]`, so the diagonal is `entry k k`. -/
def allDiagPositive (entry : Nat → Nat → Int) (n : Nat) : Bool :=
  match n with
  | 0 => true
  | k + 1 =>
    allDiagPositive entry k &&
    decide (0 < entry k k)


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
    (entry : Nat → Nat → Int) (n : Nat) (c₁ c₂ c₃ : Int)
    (state : PSDChunkResult) (j : Nat) (hj : j < n) : PSDChunkResult :=
  let zCol : Array Int := .ofFn fun (i : Fin n) =>
    if i.val ≤ j then entry j i.val else 0
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
def checkPSDColumns (neighbors : Array Nat) (entry : Nat → Nat → Int)
    (n d : Nat) (c₁ c₂ c₃ : Int) (columns : Array (Fin n)) : PSDChunkResult :=
  let step := psdColumnStep neighbors d entry n c₁ c₂ c₃
  Id.run do
    let mut state : PSDChunkResult := { epsMax := 0, minDiag := 0, first := true }
    for jf in columns do state := step state jf.val jf.isLt
    return state

/-- Round-robin column partition: column `j` goes to task `j % tasks`.
    Shared between sequential and parallel PSD checks. -/
def roundRobinPartition (n tasks : Nat) : Array (Array (Fin n)) :=
  Id.run do
    let mut lists := Array.replicate tasks (Array.mkEmpty (n / tasks + 1))
    for h : j in [:n] do
      have hj : j < n := by have := h.upper; simp at this; omega
      let c := j % tasks
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
def checkPSDCertificate (rotStr : String) (entry : Nat → Nat → Int)
    (n d : Nat) (c₁ c₂ c₃ : Int) (tasks : Nat := 64) : Bool :=
  allDiagPositive entry n &&
    let neighbors := decodeNeighbors rotStr n d
    let columnLists := roundRobinPartition n tasks
    let results := columnLists.map fun cols =>
      checkPSDColumns neighbors entry n d c₁ c₂ c₃ cols
    checkPSDThreshold results n


/-! **Rotation function from base-85 data** -/

/-- Decode a base-85 encoded rotation map into a rotation function `Fin n × Fin d → Fin n × Fin d`.
    Matches the `hmatch` hypothesis in `certificate_bridge`, so `(fun _ => rfl)` discharges it. -/
def rotFun (rotStr : String) (n d : Nat) (hn : 0 < n) (hd : 0 < d)
    (vp : Fin n × Fin d) : Fin n × Fin d :=
  let k := vp.1.val * d + vp.2.val
  (⟨decodeBase85Nat rotStr (2 * k) % n, Nat.mod_lt _ hn⟩,
   ⟨decodeBase85Nat rotStr (2 * k + 1) % d, Nat.mod_lt _ hd⟩)

/-! **Pure involution spec (for `native_decide`)** -/

/-- Check involution at a single index: decoded `(w,q)` is in-bounds and round-trips. -/
def checkInvAt (rotStr : String) (n d k : Nat) : Bool :=
  let w := decodeBase85Nat rotStr (2 * k)
  let q := decodeBase85Nat rotStr (2 * k + 1)
  decide (w < n) && decide (q < d) &&
  decide (decodeBase85Nat rotStr (2 * (w * d + q)) * d +
          decodeBase85Nat rotStr (2 * (w * d + q) + 1) = k)

/-- Check all indices from 0 to `m-1`. -/
def checkInvBelow (rotStr : String) (n d : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => checkInvAt rotStr n d k && checkInvBelow rotStr n d k

/-- Pure recursive involution check. Computationally equivalent to `checkInvolution`
    but structured for formal reasoning (no imperative loop).
    Bridge proof: `checkInvolutionSpec_implies_rotFun_involution` in `CertificateBridge.lean`. -/
def checkInvolutionSpec (rotStr : String) (n d : Nat) : Bool :=
  decide (rotStr.utf8ByteSize = n * d * 2 * 5) && checkInvBelow rotStr n d (n * d)


/-! **Shared helpers for column-norm bound checking** -/

/-- Sum `f(0) + f(1) + ... + f(n-1)`. -/
def sumTo (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => sumTo f n + f n

/-- Certificate matrix entry `Z[i,j]` as integer. Zero when `i > j`.
    `entry j k` returns the raw entry at column `j`, row `k`. -/
def certEntryInt (entry : Nat → Nat → Int) (i j : Nat) : Int :=
  if i ≤ j then entry j i else 0

/-- Integer absolute value. Works without Mathlib imports. -/
@[inline] def intAbs (x : Int) : Int := if x ≥ 0 then x else -x

/-- Column ℓ₁-norm of Z: `∑_{k<n} |Z[k,j]|`. -/
def zColNormPure (entry : Nat → Nat → Int) (n j : Nat) : Int :=
  sumTo (fun k ↦ intAbs (certEntryInt entry k j)) n

/-- Per-row column-norm bound check. Checks rows `i, i+1, ..., i+remaining-1`.
    `prefSum` = `∑_{j<i} zColNormPure entry n j`. -/
def checkPerRow (entry : Nat → Nat → Int) (n : Nat) (ε mdpe : Int)
    (remaining i : Nat) (prefSum : Int) : Bool :=
  match remaining with
  | 0 => true
  | r + 1 =>
    let si := zColNormPure entry n i
    let ti := prefSum + (↑(n - i) : Int) * si
    decide (entry i i * mdpe > ε * ti) &&
    checkPerRow entry n ε mdpe r (i + 1) (prefSum + si)

/-- Check column-norm bound: computes `epsMax`/`minDiag` via `checkPSDColumns`,
    then checks `Z[i,i]·(minDiag + epsMax) > epsMax·T_i` for each row. -/
def checkColumnNormBound (rotStr : String) (entry : Nat → Nat → Int)
    (n d : Nat) (c₁ c₂ c₃ : Int) (tasks : Nat := 64) : Bool :=
  let neighbors := decodeNeighbors rotStr n d
  let columnLists := roundRobinPartition n tasks
  let results := columnLists.map fun cols =>
    checkPSDColumns neighbors entry n d c₁ c₂ c₃ cols
  let merged := results.foldl PSDChunkResult.merge
    { epsMax := 0, minDiag := 0, first := true }
  if merged.first then false
  else checkPerRow entry n merged.epsMax (merged.minDiag + merged.epsMax) n 0 0


/-! **Combined check** -/

/-- Full certificate check: involution + PSD + column-norm bound.
    Generic over the entry function `entry j k = Z[k,j]`. -/
def checkCertificateSlowWith (rotStr : String) (entry : Nat → Nat → Int)
    (n d : Nat) (c₁ c₂ c₃ : Int) (tasks : Nat := 64) : Bool :=
  checkInvolution rotStr n d &&
  checkPSDCertificate rotStr entry n d c₁ c₂ c₃ tasks &&
  checkColumnNormBound rotStr entry n d c₁ c₂ c₃ tasks


/-! **Parallel certificate checking** -/

/-- Parallel PSD certificate check: same result as `checkPSDCertificate` but
    spawns dedicated OS threads for each chunk via `Task.spawn`.

    Structure matches `checkPSDCertificate` exactly: same guards, same
    `roundRobinPartition`, same `checkPSDColumns`, same `checkPSDThreshold`.
    The only difference is `Task.spawn` wrapping each chunk evaluation.
    Since `Task` is a transparent structure in Lean 4 (`Task.spawn fn = ⟨fn ()⟩`),
    the bridge `checkPSDCertificatePar = checkPSDCertificate` follows from
    `Array.map_map` + definitional unfolding. -/
def checkPSDCertificatePar (rotStr : String) (entry : Nat → Nat → Int)
    (n d : Nat) (c₁ c₂ c₃ : Int) (tasks : Nat := 64) : Bool :=
  allDiagPositive entry n &&
    let neighbors := decodeNeighbors rotStr n d
    let columnLists := roundRobinPartition n tasks
    -- Spawn all tasks (all start running concurrently)
    let tasks := columnLists.map fun cols =>
      Task.spawn (prio := .dedicated) fun () =>
        checkPSDColumns neighbors entry n d c₁ c₂ c₃ cols
    -- Collect all results (each .get blocks until its task completes)
    let results := tasks.map Task.get
    checkPSDThreshold results n

/-- Decode the `k`-th signed value from 4-byte base-128 encoded string.
    Range: [-134217728, 134217727]. Each entry: 4 bytes with values 0–127. -/
def decode128x4Int (s : String) (k : Nat) : Int :=
  let pos := 4 * k
  let b0 := (strGet! s pos).toNat
  let b1 := (strGet! s (pos + 1)).toNat
  let b2 := (strGet! s (pos + 2)).toNat
  let b3 := (strGet! s (pos + 3)).toNat
  (b0 + 128 * (b1 + 128 * (b2 + 128 * b3)) : Int) - 134217728

/-- Decode the `k`-th signed value from 5-byte base-128 encoded string.
    Range: [-17179869184, 17179869183]. Each entry: 5 bytes with values 0–127. -/
def decode128x5Int (s : String) (k : Nat) : Int :=
  let pos := 5 * k
  let b0 := (strGet! s pos).toNat
  let b1 := (strGet! s (pos + 1)).toNat
  let b2 := (strGet! s (pos + 2)).toNat
  let b3 := (strGet! s (pos + 3)).toNat
  let b4 := (strGet! s (pos + 4)).toNat
  (b0 + 128 * (b1 + 128 * (b2 + 128 * (b3 + 128 * b4))) : Int) - 17179869184

/-- Process columns: PSD + column ℓ₁-norms in a single fused pass.
    `entry j k` returns `Z[k,j]`. -/
@[inline] def checkPSDColumnsFull (neighbors : Array Nat)
    (n d : Nat) (c₁ c₂ c₃ : Int) (columns : Array (Fin n))
    (entry : Nat → Nat → Int) :
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

      -- Zero bz for this column (zCol is overwritten before read, no zeroing needed)
      for v in [:n] do
        bz := bz.set! v 0

      -- Fused decode + scatter: build zCol, accumulate colSum/colNorm, scatter into bz
      let mut colSum : Int := 0
      let mut colNorm : Int := 0
      for k in [:j+1] do
        let zk := entry j k
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

/-- Reconstruct column norms in column order from per-chunk fused results.
    `partition[ci]` lists columns for chunk `ci`; `results[ci].2` has their
    norms in the same order. Returns array where index `j` = norm of column `j`. -/
def flattenNorms {n : Nat} (partition : Array (Array (Fin n)))
    (results : Array (PSDChunkResult × Array Int)) : Array Int :=
  Id.run do
    let mut norms := Array.replicate n (0 : Int)
    for ci in [:partition.size] do
      let chunkNorms := results[ci]!.2
      let mut ki := 0
      for col in partition[ci]! do
        norms := norms.set! col.val chunkNorms[ki]!
        ki := ki + 1
    return norms

/-- Merged parallel certificate check: PSD + column-norm bound in one parallel pass.
    Same result as `checkCertificateSlowWith` (proved in `AKS/Cert/FastProof.lean`).
    Each parallel task computes both PSD state and column ℓ₁-norms via fused cert
    decode. The norm lookup uses `flattenNorms` to reconstruct column-order norms
    from per-chunk results, supporting arbitrary column partitions. -/
@[inline] def checkCertificateWith (rotStr : String) (entry : Nat → Nat → Int)
    (n d : Nat) (c₁ c₂ c₃ : Int)
    (partition : Array (Array (Fin n)) := roundRobinPartition n 64) : Bool :=
  checkInvolution rotStr n d &&
  allDiagPositive entry n &&
    let neighbors := decodeNeighbors rotStr n d
    let spawned := partition.map fun cols =>
      Task.spawn (prio := .dedicated) fun () =>
        checkPSDColumnsFull neighbors n d c₁ c₂ c₃ cols entry
    let results := spawned.map Task.get
    let merged := (results.map (·.1)).foldl PSDChunkResult.merge
      { epsMax := 0, minDiag := 0, first := true }
    if merged.first then false
    else
      decide (merged.minDiag > merged.epsMax * (n * (n + 1) / 2)) &&
      let norms := flattenNorms partition results
      Id.run do
        let ε := merged.epsMax
        let mdpe := merged.minDiag + ε
        let mut prefSum : Int := 0
        for i in [:n] do
          let si := norms[i]!
          let ti := prefSum + (↑(n - i) : Int) * si
          if !(entry i i * mdpe > ε * ti) then
            return false
          prefSum := prefSum + si
        return true

/-- Base-85 entry decoder: `Z[k,j]` from packed upper-triangular format. -/
@[inline] def b85entry (s : String) (j k : Nat) : Int :=
  decodeBase85Int s (j * (j + 1) / 2 + k)

/-- Base-128 entry decoder: off-diagonal from 4-byte format, diagonal = `scale`. -/
@[inline] def b128entry (scale : Int) (s : String) (j k : Nat) : Int :=
  if j == k then scale else decode128x4Int s (j * (j - 1) / 2 + k)

/-- Base-128 entry decoder: off-diagonal from 5-byte format, diagonal = `scale`. -/
@[inline] def b128x5entry (scale : Int) (s : String) (j k : Nat) : Int :=
  if j == k then scale else decode128x5Int s (j * (j - 1) / 2 + k)

/-- `checkCertificateWith` specialized to base-85 encoded certificate. -/
def checkCertificate (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : Int)
    (partition : Array (Array (Fin n)) := roundRobinPartition n 64) : Bool :=
  checkCertificateWith rotStr (b85entry certStr) n d c₁ c₂ c₃ partition

/-- `checkCertificateWith` specialized to 4-byte base-128 off-diagonal certificate.
    Diagonal entries are the constant `scale`. -/
def checkCertificateB128 (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : Int) (scale : Int)
    (partition : Array (Array (Fin n)) := roundRobinPartition n 64) : Bool :=
  checkCertificateWith rotStr (b128entry scale certStr) n d c₁ c₂ c₃ partition

/-- `checkCertificateWith` specialized to 5-byte base-128 off-diagonal certificate.
    Diagonal entries are the constant `scale`. -/
def checkCertificateB128x5 (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : Int) (scale : Int)
    (partition : Array (Array (Fin n)) := roundRobinPartition n 64) : Bool :=
  checkCertificateWith rotStr (b128x5entry scale certStr) n d c₁ c₂ c₃ partition

/-- `checkCertificateSlowWith` specialized to base-85 encoded certificate. -/
def checkCertificateSlow (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : Int) (tasks : Nat := 64) : Bool :=
  checkCertificateSlowWith rotStr (b85entry certStr) n d c₁ c₂ c₃ tasks

end
