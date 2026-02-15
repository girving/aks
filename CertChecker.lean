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

/-- Given base-85 encoded rotation map and vector `z`, compute `B·z` where `B`
    is the adjacency matrix. `(B·z)[v] = ∑_{p=0}^{d-1} z[neighbor(v,p)]`. -/
def mulAdj (rotBytes : ByteArray) (z : Array Int) (n d : Nat) : Array Int :=
  Id.run do
    let mut result := Array.replicate n 0
    for v in [:n] do
      let mut acc : Int := 0
      for p in [:d] do
        let k := v * d + p
        let w := decodeBase85Nat rotBytes (2 * k)
        acc := acc + z[w]!
      result := result.set! v acc
    return result


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

/-- Check the PSD certificate for `M = c₁I − c₂B² + c₃J`.

    For each column `j` of `Z_int` (column-major packed, base-85 decoded):
    - Extract `z = Z_int[:,j]` from packed format
    - Compute `P[:,j] = M · z` using `c₁·z − c₂·B·(B·z) + c₃·(1ᵀz)·1`
    - Track `ε_max` (max upper-triangle `|P[i,j]|` for `i < j`)
    - Track `min_diag` (min diagonal `P[i,i]`)

    Then verify: `min_diag > ε_max · n · (n+1) / 2` (Gershgorin condition)
    AND all diagonal entries `Z[j,j] > 0`. -/
def checkPSDCertificate (rotBytes certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : Int) : Bool :=
  if certBytes.size != n * (n + 1) / 2 * 5 then false
  else allDiagPositive certBytes n && Id.run do
    let mut epsMax : Int := 0
    let mut minDiag : Int := 0
    let mut first := true

    for j in [:n] do
      -- Extract column j: Z[k,j] for k = 0..j
      let colStart := j * (j + 1) / 2
      let mut zCol := Array.replicate n (0 : Int)
      for k in [:j+1] do
        zCol := zCol.set! k (decodeBase85Int certBytes (colStart + k))

      -- B·z and B²·z
      let bz := mulAdj rotBytes zCol n d
      let b2z := mulAdj rotBytes bz n d

      -- Column sum of z (only entries 0..j are nonzero)
      let mut colSum : Int := 0
      for k in [:j+1] do
        colSum := colSum + zCol[k]!

      -- P[:,j] = c₁·z - c₂·B²z + c₃·colSum
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

    -- Gershgorin check: minDiag > epsMax * n * (n+1) / 2
    let threshold := epsMax * (n * (n + 1) / 2)
    decide (minDiag > threshold)


/-! **Rotation function from base-85 data** -/

/-- Decode a base-85 encoded rotation map into a rotation function `Fin n × Fin d → Fin n × Fin d`.
    Matches the `hmatch` hypothesis in `certificate_bridge`, so `(fun _ => rfl)` discharges it. -/
def rotFun (rotStr : String) (n d : Nat) (hn : 0 < n) (hd : 0 < d)
    (vp : Fin n × Fin d) : Fin n × Fin d :=
  let rotBytes := rotStr.toUTF8
  let k := vp.1.val * d + vp.2.val
  (⟨decodeBase85Nat rotBytes (2 * k) % n, Nat.mod_lt _ hn⟩,
   ⟨decodeBase85Nat rotBytes (2 * k + 1) % d, Nat.mod_lt _ hd⟩)


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


/-! **Column-norm bound check (O(n²))** -/

/-- Check that Z column norms are bounded relative to diagonal entries.
    Combined with the PSD check (minDiag, epsMax), this implies K = Z^T M Z
    is strictly diag-dominant — without the O(n³) K computation.

    For each row i, diagonal dominance requires:
      Z[i,i] · (minDiag + epsMax) > epsMax · T_i
    where T_i = ∑_{j<i} S_j + (n-i) · S_i and S_j = ∑_{k≤j} |Z[k,j]|.

    This function recomputes minDiag and epsMax from the certificate, then
    checks the column-norm inequality. Complexity: O(n²·d) for minDiag/epsMax
    (same as PSD check), O(n²) for column norms. -/
def checkColumnNormBound (rotBytes certBytes : ByteArray) (n d : Nat)
    (c₁ c₂ c₃ : Int) : Bool :=
  if certBytes.size != n * (n + 1) / 2 * 5 then false
  else Id.run do
    -- Phase 1: Compute minDiag and epsMax (same as checkPSDCertificate)
    let mut epsMax : Int := 0
    let mut minDiag : Int := 0
    let mut first := true
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
    -- Phase 2: Compute column norms S_j = ∑_{k≤j} |Z[k,j]|
    let mut colNorms := Array.replicate n (0 : Int)
    for j in [:n] do
      let colStart := j * (j + 1) / 2
      let mut norm : Int := 0
      for k in [:j+1] do
        let entry := decodeBase85Int certBytes (colStart + k)
        norm := norm + (if entry >= 0 then entry else -entry)
      colNorms := colNorms.set! j norm
    -- Phase 3: Check Z[i,i] · (minDiag + epsMax) > epsMax · T_i for each row
    let mdpe := minDiag + epsMax  -- minDiag + epsMax
    let mut prefSum : Int := 0  -- ∑_{j<i} S_j
    for i in [:n] do
      let colStartI := i * (i + 1) / 2
      let diag := decodeBase85Int certBytes (colStartI + i)
      -- T_i = prefSum + (n - i) · S_i
      let ti := prefSum + (↑(n - i) : Int) * colNorms[i]!
      if !(diag * mdpe > epsMax * ti) then return false
      prefSum := prefSum + colNorms[i]!
    return true


/-! **Fast implementations with pre-decoded data** -/

/-- Pre-decode all neighbor vertices from the rotation map. -/
def decodeNeighbors (rotBytes : ByteArray) (n d : Nat) : Array Nat :=
  Id.run do
    let nd := n * d
    let mut arr := Array.replicate nd 0
    for k in [:nd] do
      arr := arr.set! k (decodeBase85Nat rotBytes (2 * k))
    return arr

/-- Pre-decode all certificate Z entries (upper triangular, packed). -/
def decodeCertEntries (certBytes : ByteArray) (n : Nat) : Array Int :=
  Id.run do
    let total := n * (n + 1) / 2
    let mut arr := Array.replicate total 0
    for k in [:total] do
      arr := arr.set! k (decodeBase85Int certBytes k)
    return arr

/-- `mulAdj` with pre-decoded neighbor array. -/
def mulAdjPre (neighbors : Array Nat) (z : Array Int) (n d : Nat) : Array Int :=
  Id.run do
    let mut result := Array.replicate n 0
    for v in [:n] do
      let mut acc : Int := 0
      for p in [:d] do
        let w := neighbors[v * d + p]!
        acc := acc + z[w]!
      result := result.set! v acc
    return result

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
def checkCertificate (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : Int) : Bool :=
  let rotBytes := rotStr.toUTF8
  let certBytes := certStr.toUTF8
  checkInvolution rotBytes n d &&
  checkPSDCertificate rotBytes certBytes n d c₁ c₂ c₃ &&
  checkColumnNormBound rotBytes certBytes n d c₁ c₂ c₃

