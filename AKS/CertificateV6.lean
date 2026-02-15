/-
  # Certificate Checker V6: ByteArray Direct (Skip Base-85)

  Optimization: pre-decode the rotation map from base-85 into a raw `ByteArray`
  with 4 bytes per entry (little-endian UInt32). Decoding at runtime is just
  4 byte reads + shifts instead of 5 reads + multiplications for base-85.

  The pre-decode happens once; the hot `mulAdj` loop uses the raw format.
-/

import AKS.Certificate


/-! **Pre-decode rotation map to raw LE32 ByteArray** -/

/-- Convert a base-85 rotation map to raw LE32 ByteArray. Each base-85 entry
    becomes 4 bytes (little-endian unsigned 32-bit). -/
def rotToRaw (rotBytes : ByteArray) : ByteArray :=
  let nEntries := rotBytes.size / 5
  Id.run do
    let mut result : ByteArray := .empty
    for k in [:nEntries] do
      let v := decodeBase85Nat rotBytes k
      result := result.push (UInt8.ofNat (v &&& 0xFF))
      result := result.push (UInt8.ofNat ((v >>> 8) &&& 0xFF))
      result := result.push (UInt8.ofNat ((v >>> 16) &&& 0xFF))
      result := result.push (UInt8.ofNat ((v >>> 24) &&& 0xFF))
    return result


/-! **Raw ByteArray decode** -/

/-- Decode the `k`-th UInt32 from a raw little-endian ByteArray. -/
def decodeRaw32 (bytes : ByteArray) (k : Nat) : Nat :=
  let off := 4 * k
  let b0 := (bytes.get! off).toNat
  let b1 := (bytes.get! (off + 1)).toNat
  let b2 := (bytes.get! (off + 2)).toNat
  let b3 := (bytes.get! (off + 3)).toNat
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)


/-! **Raw involution check** -/

/-- Check involution using raw ByteArray rotation map. -/
def checkInvolutionRaw (rotRaw : ByteArray) (n d : Nat) : Bool :=
  let nd := n * d
  if rotRaw.size != nd * 2 * 4 then false
  else Id.run do
    let mut ok := true
    for k in [:nd] do
      let w := decodeRaw32 rotRaw (2 * k)
      let q := decodeRaw32 rotRaw (2 * k + 1)
      if w >= n || q >= d then
        ok := false
        break
      let k2 := w * d + q
      let v2 := decodeRaw32 rotRaw (2 * k2)
      let p2 := decodeRaw32 rotRaw (2 * k2 + 1)
      if v2 * d + p2 != k then
        ok := false
        break
    return ok


/-! **Raw mulAdj** -/

/-- Matrix-vector product using raw ByteArray rotation map. -/
def mulAdjRaw (rotRaw : ByteArray) (z : Array ℤ) (n d : Nat) : Array ℤ :=
  Id.run do
    let mut result := Array.replicate n 0
    for v in [:n] do
      let mut acc : ℤ := 0
      for p in [:d] do
        let k := v * d + p
        let w := decodeRaw32 rotRaw (2 * k)
        acc := acc + z[w]!
      result := result.set! v acc
    return result


/-! **Raw PSD certificate check** -/

/-- PSD certificate check: raw ByteArray for rotation map, base-85 for cert. -/
def checkPSDCertificateRaw (rotRaw : ByteArray) (certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : ℤ) : Bool :=
  if certBytes.size != n * (n + 1) / 2 * 5 then false
  else Id.run do
    let mut epsMax : ℤ := 0
    let mut minDiag : ℤ := 0
    let mut first := true

    for j in [:n] do
      let colStart := j * (j + 1) / 2
      let mut zCol := Array.replicate n (0 : ℤ)
      for k in [:j+1] do
        zCol := zCol.set! k (decodeBase85Int certBytes (colStart + k))

      let bz := mulAdjRaw rotRaw zCol n d
      let b2z := mulAdjRaw rotRaw bz n d

      let mut colSum : ℤ := 0
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

/-- Full certificate check V6: pre-decode rot to raw, then check. -/
def checkCertificateV6 (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : ℤ) : Bool :=
  let rotBytes := rotStr.toUTF8
  let rotRaw := rotToRaw rotBytes
  let certBytes := certStr.toUTF8
  checkInvolutionRaw rotRaw n d &&
  checkPSDCertificateRaw rotRaw certBytes n d c₁ c₂ c₃
