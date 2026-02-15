/-
  # PSD Certificate Checker

  Decidable checks for `native_decide`:
  1. Rotation map is a valid involution (proves `RegularGraph`)
  2. `M = c₁I − c₂B² + c₃J` is positive definite via triangular certificate

  All data is base-85 encoded as `String` literals for compact storage.
  Each i32 value (interpreted as unsigned u32) is encoded as 5 ASCII chars
  (codepoints 33–117). Decoding uses `String.toUTF8` + `ByteArray.get!`.
-/

import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation


/-! **Base-85 decoding** -/

/-- Decode the `k`-th unsigned i32 value from base-85 encoded bytes as `ℕ`. -/
def decodeBase85Nat (bytes : ByteArray) (k : Nat) : Nat :=
  let pos := 5 * k
  let c0 := (bytes.get! pos).toNat - 33
  let c1 := (bytes.get! (pos + 1)).toNat - 33
  let c2 := (bytes.get! (pos + 2)).toNat - 33
  let c3 := (bytes.get! (pos + 3)).toNat - 33
  let c4 := (bytes.get! (pos + 4)).toNat - 33
  c0 + 85 * (c1 + 85 * (c2 + 85 * (c3 + 85 * c4)))

/-- Decode the `k`-th signed i32 value from base-85 encoded bytes as `ℤ`. -/
def decodeBase85Int (bytes : ByteArray) (k : Nat) : ℤ :=
  let u := decodeBase85Nat bytes k
  if u < 2^31 then (u : ℤ) else (u : ℤ) - (2^32 : ℤ)


/-! **Rotation map validation** -/

/-- Check that a base-85 encoded rotation map represents a valid involution.
    The rotation map has `n*d` pairs `(vertex, port)` as consecutive entries:
    entry `2*k` = destination vertex, entry `2*k+1` = destination port. -/
def checkInvolution (rotBytes : ByteArray) (n d : ℕ) : Bool :=
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
def mulAdj (rotBytes : ByteArray) (z : Array ℤ) (n d : ℕ) : Array ℤ :=
  Id.run do
    let mut result := Array.replicate n 0
    for v in [:n] do
      let mut acc : ℤ := 0
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
def allDiagPositive (certBytes : ByteArray) (n : ℕ) : Bool :=
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
def checkKRowDominant (rotBytes certBytes : ByteArray) (n d : ℕ)
    (c₁ c₂ c₃ : ℤ) : Bool :=
  Id.run do
    -- Phase 1: Compute P = M · Z (stored row-major: P[i,j] = pMatrix[i*n+j])
    let mut pMatrix : Array ℤ := Array.replicate (n * n) 0
    for j in [:n] do
      let colStart := j * (j + 1) / 2
      let mut zCol := Array.replicate n (0 : ℤ)
      for k in [:j+1] do
        zCol := zCol.set! k (decodeBase85Int certBytes (colStart + k))
      let bz := mulAdj rotBytes zCol n d
      let b2z := mulAdj rotBytes bz n d
      let mut colSum : ℤ := 0
      for k in [:j+1] do
        colSum := colSum + zCol[k]!
      for i in [:n] do
        pMatrix := pMatrix.set! (i * n + j) (c₁ * zCol[i]! - c₂ * b2z[i]! + c₃ * colSum)
    -- Phase 2: For each row i of K = Z^T · P, check diagonal dominance
    for i in [:n] do
      let colStartI := i * (i + 1) / 2
      let mut diagVal : ℤ := 0
      let mut offDiagSum : ℤ := 0
      for j in [:n] do
        -- K[i,j] = ∑_{k=0}^{i} Z[k,i] · P[k,j]
        let mut kij : ℤ := 0
        for k in [:i+1] do
          let zki := decodeBase85Int certBytes (colStartI + k)
          kij := kij + zki * pMatrix[k * n + j]!
        if j == i then
          diagVal := kij
        else
          offDiagSum := offDiagSum + (if kij ≥ 0 then kij else -kij)
      if offDiagSum ≥ diagVal then return false
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
    (n d : ℕ) (c₁ c₂ c₃ : ℤ) : Bool :=
  if certBytes.size != n * (n + 1) / 2 * 5 then false
  else allDiagPositive certBytes n && Id.run do
    let mut epsMax : ℤ := 0
    let mut minDiag : ℤ := 0
    let mut first := true

    for j in [:n] do
      -- Extract column j: Z[k,j] for k = 0..j
      let colStart := j * (j + 1) / 2
      let mut zCol := Array.replicate n (0 : ℤ)
      for k in [:j+1] do
        zCol := zCol.set! k (decodeBase85Int certBytes (colStart + k))

      -- B·z and B²·z
      let bz := mulAdj rotBytes zCol n d
      let b2z := mulAdj rotBytes bz n d

      -- Column sum of z (only entries 0..j are nonzero)
      let mut colSum : ℤ := 0
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
def rotFun (rotStr : String) (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (vp : Fin n × Fin d) : Fin n × Fin d :=
  let rotBytes := rotStr.toUTF8
  let k := vp.1.val * d + vp.2.val
  (⟨decodeBase85Nat rotBytes (2 * k) % n, Nat.mod_lt _ hn⟩,
   ⟨decodeBase85Nat rotBytes (2 * k + 1) % d, Nat.mod_lt _ hd⟩)


/-! **Combined check** -/

/-- Full certificate check: involution + PSD + K diagonal dominance.
    Both rotation map and certificate are base-85 encoded `String`s. -/
def checkCertificate (rotStr certStr : String)
    (n d : ℕ) (c₁ c₂ c₃ : ℤ) : Bool :=
  let rotBytes := rotStr.toUTF8
  let certBytes := certStr.toUTF8
  checkInvolution rotBytes n d &&
  checkPSDCertificate rotBytes certBytes n d c₁ c₂ c₃ &&
  checkKRowDominant rotBytes certBytes n d c₁ c₂ c₃
