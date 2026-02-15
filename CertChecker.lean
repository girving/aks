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


/-! **PSD Certificate Check** -/

/-- Check the PSD certificate for `M = c₁I − c₂B² + c₃J`.

    For each column `j` of `Z_int` (column-major packed, base-85 decoded):
    - Extract `z = Z_int[:,j]` from packed format
    - Compute `P[:,j] = M · z` using `c₁·z − c₂·B·(B·z) + c₃·(1ᵀz)·1`
    - Track `ε_max` (max upper-triangle `|P[i,j]|` for `i < j`)
    - Track `min_diag` (min diagonal `P[i,i]`)

    Then verify: `min_diag > ε_max · n · (n+1) / 2` (Gershgorin condition). -/
def checkPSDCertificate (rotBytes certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : Int) : Bool :=
  if certBytes.size != n * (n + 1) / 2 * 5 then false
  else Id.run do
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


/-! **Combined check** -/

/-- Full certificate check: involution + PSD.
    Both rotation map and certificate are base-85 encoded `String`s. -/
def checkCertificate (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : Int) : Bool :=
  let rotBytes := rotStr.toUTF8
  let certBytes := certStr.toUTF8
  checkInvolution rotBytes n d &&
  checkPSDCertificate rotBytes certBytes n d c₁ c₂ c₃
