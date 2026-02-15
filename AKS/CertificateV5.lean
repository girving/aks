/-
  # Certificate Checker V5: Combined Optimizations

  Combines all three optimizations:
  - V2: Pre-decoded neighbor array (no base-85 in hot loop)
  - V3: Int64 arithmetic (no arbitrary-precision)
  - V4: Fused B²z (no intermediate array)

  Expected: 5-50x speedup over baseline.
-/

import AKS.Certificate


/-! **Pre-decode into neighbor array** -/

/-- Decode rotBytes into a flat neighbor array. `result[v*d+p] = neighbor vertex`. -/
def decodeNeighborsV5 (rotBytes : ByteArray) (n d : Nat) : Array Nat :=
  Id.run do
    let nd := n * d
    let mut arr := Array.replicate nd 0
    for k in [:nd] do
      arr := arr.set! k (decodeBase85Nat rotBytes (2 * k))
    return arr


/-! **Int64 decode for certificate** -/

/-- Decode the `k`-th signed i32 from base-85 as Int64. -/
private def decodeSignedI64 (bytes : ByteArray) (k : Nat) : Int64 :=
  let u : Int64 := decodeBase85Nat bytes k |>.toInt64
  if u < (2147483648 : Int64) then u else u - (4294967296 : Int64)


/-! **Fused B²z with pre-decoded neighbors and Int64** -/

/-- Compute B²z: pre-decoded neighbors, Int64, no intermediate array. -/
def mulAdj2V5 (neighbors : Array Nat) (z : Array Int64) (n d : Nat) : Array Int64 :=
  Id.run do
    let mut result := Array.replicate n (0 : Int64)
    for v in [:n] do
      let mut acc : Int64 := 0
      for p in [:d] do
        let w := neighbors[v * d + p]!
        for q in [:d] do
          let u := neighbors[w * d + q]!
          acc := acc + z[u]!
      result := result.set! v acc
    return result


/-! **PSD certificate check** -/

/-- PSD check: pre-decoded neighbors + Int64 + fused B²z. -/
def checkPSDCertificateV5 (neighbors : Array Nat) (certBytes : ByteArray)
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
        zCol := zCol.set! k (decodeSignedI64 certBytes (colStart + k))

      let b2z := mulAdj2V5 neighbors zCol n d

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

/-- Full certificate check V5: all optimizations combined. -/
def checkCertificateV5 (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : Int64) : Bool :=
  let rotBytes := rotStr.toUTF8
  let certBytes := certStr.toUTF8
  if !checkInvolution rotBytes n d then false
  else
    let neighbors := decodeNeighborsV5 rotBytes n d
    checkPSDCertificateV5 neighbors certBytes n d c₁ c₂ c₃
