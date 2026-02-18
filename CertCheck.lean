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

  **Keep this file minimal:** definitions only, no proofs about them.
  Proofs that these functions have desired properties go in
  `AKS/CertificateBridge.lean` (which can import Mathlib).
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
  Id.run do
    let mut result := Array.replicate n 0
    for v in [:n] do
      let mut acc : Int := 0
      for p in [:d] do
        let w := getNeighbor (v * d + p)
        acc := acc + z[w]!
      result := result.set! v acc
    return result

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


/-! **K = Z^T * M * Z diagonal dominance check** -/

/-- Check that K = Z^T · (M · Z) is strictly row-diag-dominant, where
    P = M · Z is computed column-by-column via `c₁·z − c₂·B²z + c₃·(1ᵀz)·1`,
    and K[i,j] = ∑_{k≤i} Z[k,i] · P[k,j].

    This is the concrete computational check corresponding to the formal
    `congruence_diagDominant` theorem in `CertificateBridge.lean`.
    Complexity: O(n²·d) for P, O(n³) for K — feasible for n ≤ ~2000. -/
def checkKRowDominant (rotBytes certBytes : ByteArray) (n d : Nat)
    (c₁ c₂ c₃ : Int) : Bool :=
  Id.run do
    -- Phase 1: Compute P = M · Z (stored row-major: P[i,j] = pMatrix[i*n+j])
    let mut pMatrix : Array Int := Array.replicate (n * n) 0
    for j in [:n] do
      let colStart := j * (j + 1) / 2
      let mut zCol := Array.replicate n (0 : Int)
      for k in [:j+1] do
        zCol := zCol.set! k (decodeBase85Int certBytes (colStart + k))
      let bz := mulAdj rotBytes zCol n d
      let b2z := mulAdj rotBytes bz n d
      let mut colSum : Int := 0
      for k in [:j+1] do
        colSum := colSum + zCol[k]!
      for i in [:n] do
        pMatrix := pMatrix.set! (i * n + j) (c₁ * zCol[i]! - c₂ * b2z[i]! + c₃ * colSum)
    -- Phase 2: For each row i of K = Z^T · P, check diagonal dominance
    for i in [:n] do
      let colStartI := i * (i + 1) / 2
      let mut diagVal : Int := 0
      let mut offDiagSum : Int := 0
      for j in [:n] do
        -- K[i,j] = ∑_{k=0}^{i} Z[k,i] · P[k,j]
        let mut kij : Int := 0
        for k in [:i+1] do
          let zki := decodeBase85Int certBytes (colStartI + k)
          kij := kij + zki * pMatrix[k * n + j]!
        if j == i then
          diagVal := kij
        else
          offDiagSum := offDiagSum + (if kij >= 0 then kij else -kij)
      if offDiagSum >= diagVal then return false
    return true


/-! **PSD Certificate Check** -/

/-- Per-chunk result from parallel PSD computation. -/
structure PSDChunkResult where
  epsMax : Int
  minDiag : Int
  first : Bool

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
    `doMulAdj` is the adjacency-vector product function (either `mulAdj` or
    `mulAdjPre`-based). Factored out so that `checkPSDCertificate` and
    `checkPSDColumns` share the exact same step function. -/
@[inline] def psdColumnStep (doMulAdj : Array Int → Array Int)
    (certBytes : ByteArray) (n : Nat) (c₁ c₂ c₃ : Int)
    (state : PSDChunkResult) (j : Nat) : PSDChunkResult :=
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
    let mut minDiag := state.minDiag
    let mut first := state.first
    for i in [:n] do
      let pij := c₁ * zCol[i]! - c₂ * b2z[i]! + c₃ * colSum
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
    (n d : Nat) (c₁ c₂ c₃ : Int) (columns : Array Nat) : PSDChunkResult :=
  let step := psdColumnStep (mulAdjPre neighbors · n d) certBytes n c₁ c₂ c₃
  Id.run do
    let mut state : PSDChunkResult := { epsMax := 0, minDiag := 0, first := true }
    for j in columns do state := step state j
    return state

/-- Build interleaved column partition: column `j` goes to chunk `j % numChunks`.
    Shared between sequential and parallel PSD checks. -/
def buildColumnLists (n numChunks : Nat) : Array (Array Nat) :=
  Id.run do
    let mut lists := Array.replicate numChunks (Array.mkEmpty (n / numChunks + 1))
    for j in [:n] do
      let c := j % numChunks
      lists := lists.set! c (lists[c]!.push j)
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
    bridge `checkCertificateFast = checkCertificateSlow` is structurally trivial. -/
def checkPSDCertificate (rotBytes certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : Int) : Bool :=
  if certBytes.size != n * (n + 1) / 2 * 5 then false
  else allDiagPositive certBytes n &&
    let neighbors := decodeNeighbors rotBytes n d
    let columnLists := buildColumnLists n 64
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


/-! **Pure functional definitions for bridge proofs** -/

/-- Sum `f(0) + f(1) + ... + f(n-1)`. -/
def sumTo (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => sumTo f n + f n

/-- Certificate matrix entry `Z[i,j]` as integer. Zero when `i > j`. -/
def certEntryInt (certBytes : ByteArray) (i j : Nat) : Int :=
  if i ≤ j then decodeBase85Int certBytes (j * (j + 1) / 2 + i) else 0

/-- Unnormalized adjacency-vector product: `(B·z)[v] = ∑_{p<d} z[neighbor(v,p) % n]`. -/
def adjMulPure (rotBytes : ByteArray) (z : Nat → Int) (n d v : Nat) : Int :=
  sumTo (fun p => z (decodeBase85Nat rotBytes (2 * (v * d + p)) % n)) d

/-- `P = M · Z` entry at `(k, j)` in integers. -/
def pEntryPure (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (k j : Nat) : Int :=
  let zj : Nat → Int := fun i => certEntryInt certBytes i j
  let b2zj_k := adjMulPure rotBytes (fun v => adjMulPure rotBytes zj n d v) n d k
  let colSum := sumTo (fun l => certEntryInt certBytes l j) n
  c₁ * certEntryInt certBytes k j - c₂ * b2zj_k + c₃ * colSum

/-- `K = Zᵀ · M · Z` entry at `(i, j)` in integers. -/
def kEntryPure (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (i j : Nat) : Int :=
  sumTo (fun k => certEntryInt certBytes k i *
    pEntryPure rotBytes certBytes n d c₁ c₂ c₃ k j) n

/-- Check diagonal dominance for row `i` (pure functional). -/
def checkRowDomPure (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (i : Nat) : Bool :=
  let diag := kEntryPure rotBytes certBytes n d c₁ c₂ c₃ i i
  let offDiag := sumTo (fun j =>
    if j == i then 0
    else let v := kEntryPure rotBytes certBytes n d c₁ c₂ c₃ i j
         if v >= 0 then v else -v) n
  decide (offDiag < diag)

/-- Check diagonal dominance for all rows `0..m-1` (pure functional). -/
def checkAllRowsDomPure (rotBytes certBytes : ByteArray) (n d : Nat)
    (c₁ c₂ c₃ : Int) : Nat → Bool
  | 0 => true
  | m + 1 => checkAllRowsDomPure rotBytes certBytes n d c₁ c₂ c₃ m &&
              checkRowDomPure rotBytes certBytes n d c₁ c₂ c₃ m


/-! **Pure recursive helpers for column-norm bound** -/

/-- Integer absolute value. Avoids notation ambiguity in match cases and
    works without Mathlib imports. Equals `|x|` from `Mathlib.Algebra.Abs`. -/
@[inline] def intAbs (x : Int) : Int := if x ≥ 0 then x else -x

/-- Column sum of certificate column `j`: `∑_{l<n} Z[l,j]`.
    Pre-computed and threaded through `epsMaxCol` to avoid O(n) recomputation
    per `pEntryPure` call, keeping total complexity O(n²d²) instead of O(n²d²+n³). -/
def colSumZ (certBytes : ByteArray) (n j : Nat) : Int :=
  sumTo (fun l ↦ certEntryInt certBytes l j) n

/-- Maximum `|P[k,j]|` for `k < bound`, with pre-computed column sum.
    The inlined P entry computation equals `pEntryPure k j` when
    `colSum = colSumZ certBytes n j`. -/
def epsMaxCol (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (j : Nat) (colSum : Int) : Nat → Int
  | 0 => 0
  | k + 1 =>
    let zj : Nat → Int := fun i ↦ certEntryInt certBytes i j
    let b2zj_k := adjMulPure rotBytes (fun v ↦ adjMulPure rotBytes zj n d v) n d k
    let pij := c₁ * certEntryInt certBytes k j - c₂ * b2zj_k + c₃ * colSum
    max (epsMaxCol rotBytes certBytes n d c₁ c₂ c₃ j colSum k) (intAbs pij)

/-- Maximum off-diagonal `|P[k,j]|` over `k < j`, for all `j < bound`. -/
def epsMaxVal (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int) : Nat → Int
  | 0 => 0
  | j + 1 =>
    max (epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ j)
        (epsMaxCol rotBytes certBytes n d c₁ c₂ c₃ j (colSumZ certBytes n j) j)

/-- Minimum diagonal `P[j,j]` over `j < bound`. Returns `0` for `bound = 0`. -/
def minDiagVal (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int) : Nat → Int
  | 0 => 0
  | 1 => pEntryPure rotBytes certBytes n d c₁ c₂ c₃ 0 0
  | m + 2 => min (minDiagVal rotBytes certBytes n d c₁ c₂ c₃ (m + 1))
                  (pEntryPure rotBytes certBytes n d c₁ c₂ c₃ (m + 1) (m + 1))

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

/-- Check column-norm bound using pure recursive functions.
    Computes `epsMax` (max off-diagonal `|P|`), `minDiag` (min diagonal `P`),
    and checks `Z[i,i]·(minDiag + epsMax) > epsMax·T_i` for each row `i`. -/
def checkColumnNormBound (rotBytes certBytes : ByteArray) (n d : Nat)
    (c₁ c₂ c₃ : Int) : Bool :=
  if certBytes.size != n * (n + 1) / 2 * 5 then false
  else
    let neighbors := decodeNeighbors rotBytes n d
    let columnLists := buildColumnLists n 64
    let results := columnLists.map fun cols =>
      checkPSDColumns neighbors certBytes n d c₁ c₂ c₃ cols
    let merged := results.foldl PSDChunkResult.merge
      { epsMax := 0, minDiag := 0, first := true }
    if merged.first then false
    else checkPerRow certBytes n merged.epsMax (merged.minDiag + merged.epsMax) n 0 0


/-- Pure recursive version of `checkColumnNormBound` for formal reasoning.
    Uses `epsMaxVal`/`minDiagVal` (pure recursive) instead of imperative `checkPSDColumns`.
    Equivalent to the imperative version but trivially amenable to spec proofs. -/
def checkColumnNormBoundPure (rotBytes certBytes : ByteArray) (n d : Nat)
    (c₁ c₂ c₃ : Int) : Bool :=
  if n == 0 then false
  else
    let ε := epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ n
    let δ := minDiagVal rotBytes certBytes n d c₁ c₂ c₃ n
    checkPerRow certBytes n ε (δ + ε) n 0 0


/-! **Fast implementations with pre-decoded data** -/

/-- Pre-decode all certificate Z entries (upper triangular, packed). -/
def decodeCertEntries (certBytes : ByteArray) (n : Nat) : Array Int :=
  Id.run do
    let total := n * (n + 1) / 2
    let mut arr := Array.replicate total 0
    for k in [:total] do
      arr := arr.set! k (decodeBase85Int certBytes k)
    return arr

/-- Fast K diagonal dominance check with pre-decoded data. -/
def checkKRowDominantPre (neighbors : Array Nat) (zEntries : Array Int)
    (n d : Nat) (c₁ c₂ c₃ : Int) : Bool :=
  Id.run do
    -- Phase 1: Compute P = M · Z
    let mut pMatrix : Array Int := Array.replicate (n * n) 0
    for j in [:n] do
      let colStart := j * (j + 1) / 2
      let mut zCol := Array.replicate n (0 : Int)
      for k in [:j+1] do
        zCol := zCol.set! k (zEntries[colStart + k]!)
      let bz := mulAdjPre neighbors zCol n d
      let b2z := mulAdjPre neighbors bz n d
      let mut colSum : Int := 0
      for k in [:j+1] do
        colSum := colSum + zCol[k]!
      for i in [:n] do
        pMatrix := pMatrix.set! (i * n + j) (c₁ * zCol[i]! - c₂ * b2z[i]! + c₃ * colSum)
    -- Phase 2: Check rows using pre-decoded Z
    for i in [:n] do
      let colStartI := i * (i + 1) / 2
      let mut diagVal : Int := 0
      let mut offDiagSum : Int := 0
      for j in [:n] do
        let mut kij : Int := 0
        for k in [:i+1] do
          kij := kij + zEntries[colStartI + k]! * pMatrix[k * n + j]!
        if j == i then
          diagVal := kij
        else
          offDiagSum := offDiagSum + (if kij >= 0 then kij else -kij)
      if offDiagSum >= diagVal then return false
    return true

/-- Fast PSD check with pre-decoded data. -/
def checkPSDCertificatePre (neighbors : Array Nat) (zEntries : Array Int)
    (certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int) : Bool :=
  if certBytes.size != n * (n + 1) / 2 * 5 then false
  else allDiagPositive certBytes n && Id.run do
    let mut epsMax : Int := 0
    let mut minDiag : Int := 0
    let mut first := true
    for j in [:n] do
      let colStart := j * (j + 1) / 2
      let mut zCol := Array.replicate n (0 : Int)
      for k in [:j+1] do
        zCol := zCol.set! k (zEntries[colStart + k]!)
      let bz := mulAdjPre neighbors zCol n d
      let b2z := mulAdjPre neighbors bz n d
      let mut colSum : Int := 0
      for k in [:j+1] do
        colSum := colSum + zCol[k]!
      for i in [:n] do
        let pij := c₁ * zCol[i]! - c₂ * b2z[i]! + c₃ * colSum
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
    let threshold := epsMax * (n * (n + 1) / 2)
    decide (minDiag > threshold)


/-! **Combined check** -/

/-- Full certificate check: involution + PSD + column-norm bound.
    Both rotation map and certificate are base-85 encoded `String`s.
    All sub-checks are O(n²·d), making `native_decide` feasible for n ≤ ~10000. -/
def checkCertificateSlow (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : Int) : Bool :=
  let rotBytes := rotStr.toUTF8
  let certBytes := certStr.toUTF8
  checkInvolution rotBytes n d &&
  checkPSDCertificate rotBytes certBytes n d c₁ c₂ c₃ &&
  checkColumnNormBound rotBytes certBytes n d c₁ c₂ c₃


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
    (n d : Nat) (c₁ c₂ c₃ : Int) : Bool :=
  if certBytes.size != n * (n + 1) / 2 * 5 then false
  else allDiagPositive certBytes n &&
    let neighbors := decodeNeighbors rotBytes n d
    let columnLists := buildColumnLists n 64
    -- Spawn all tasks (all start running concurrently)
    let tasks := columnLists.map fun cols =>
      Task.spawn (prio := .dedicated) fun () =>
        checkPSDColumns neighbors certBytes n d c₁ c₂ c₃ cols
    -- Collect all results (each .get blocks until its task completes)
    let results := tasks.map Task.get
    checkPSDThreshold results n

/-- Parallel certificate check: same result as `checkCertificateSlow` but splits
    the O(n²d) PSD column loop across 4 dedicated OS threads via `Task.spawn`
    with pre-decoded neighbors. Uses `checkColumnNormBound` directly (identical
    to slow version). -/
def checkCertificateFast (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : Int) : Bool :=
  let rotBytes := rotStr.toUTF8
  let certBytes := certStr.toUTF8
  checkInvolution rotBytes n d &&
  checkPSDCertificatePar rotBytes certBytes n d c₁ c₂ c₃ &&
  checkColumnNormBound rotBytes certBytes n d c₁ c₂ c₃


