/-
  # Certificate Checker V3: Int64 Arithmetic

  Optimization: replace `ℤ` (arbitrary-precision) with `Int64` in the hot
  path. Vertex indices still use `Nat` from `decodeBase85Nat`.

  Overflow analysis for n=1728, d=12:
  - Certificate values z[i]: up to ~10^8 (fits Int64)
  - mulAdj accumulator: d terms of z[w] ≤ 12 * 10^8 = 1.2×10^9 (fits)
  - c₁ * z[i]: 792 * 10^8 ≈ 7.9×10^10 (fits Int64's ±9.2×10^18)
  - c₂ * b2z[i]: 9 * 12 * 10^8 ≈ 1.08×10^10 (fits)
  - colSum: n * max_z ≈ 1728 * 10^8 = 1.7×10^11 (fits)
  - c₃ * colSum: 2 * 1.7×10^11 = 3.4×10^11 (fits)
  - pij: sum of above ≤ ~5×10^11 (fits)
  - epsMax * n*(n+1)/2: 5×10^11 * 1.5×10^6 ≈ 7.5×10^17 (fits Int64)
-/

import AKS.Certificate


/-! **Int64 decode for certificate values** -/

/-- Decode the `k`-th signed i32 value from base-85 as `Int64`. -/
def decodeBase85ToInt64 (bytes : ByteArray) (k : Nat) : Int64 :=
  let u : Int64 := decodeBase85Nat bytes k |>.toInt64
  if u < (2147483648 : Int64) then u else u - (4294967296 : Int64)


/-! **Int64 mulAdj** -/

/-- Matrix-vector product using Int64 for vector, Nat for vertex indices. -/
def mulAdjI64 (rotBytes : ByteArray) (z : Array Int64) (n d : Nat) : Array Int64 :=
  Id.run do
    let mut result := Array.replicate n (0 : Int64)
    for v in [:n] do
      let mut acc : Int64 := 0
      for p in [:d] do
        let k := v * d + p
        let w := decodeBase85Nat rotBytes (2 * k)
        acc := acc + z[w]!
      result := result.set! v acc
    return result


/-! **Int64 PSD certificate check** -/

/-- PSD certificate check with Int64 arithmetic. -/
def checkPSDCertificateI64 (rotBytes certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : Int64) : Bool :=
  if certBytes.size != n * (n + 1) / 2 * 5 then false
  else Id.run do
    let mut epsMax : Int64 := 0
    let mut minDiag : Int64 := 0
    let mut first := true

    for j in [:n] do
      let colStart := j * (j + 1) / 2
      let mut zCol := Array.replicate n (0 : Int64)
      for k in [:j+1] do
        zCol := zCol.set! k (decodeBase85ToInt64 certBytes (colStart + k))

      let bz := mulAdjI64 rotBytes zCol n d
      let b2z := mulAdjI64 rotBytes bz n d

      let mut colSum : Int64 := 0
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
          let absPij := if pij ≥ 0 then pij else -pij
          if absPij > epsMax then
            epsMax := absPij

    let threshold := epsMax * (n * (n + 1) / 2 : Nat).toInt64
    decide (minDiag > threshold)


/-! **Combined check** -/

/-- Full certificate check V3: Int64 arithmetic. -/
def checkCertificateV3 (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : Int64) : Bool :=
  let rotBytes := rotStr.toUTF8
  let certBytes := certStr.toUTF8
  checkInvolution rotBytes n d &&
  checkPSDCertificateI64 rotBytes certBytes n d c₁ c₂ c₃
