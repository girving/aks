/-
  # Fast Certificate Checker

  Optimized version of `checkCertificateSlow` from `CertCheck.lean`.
  Key optimization: pre-decode the base-85 rotation map into an `Array Nat`
  once, so `mulAdj` becomes pure array lookups (no base-85 in hot loop).

  Benchmarked at 2.1x faster than baseline for n=1728, d=12.

  Note: pre-decoding the certificate entries does NOT help — each cert entry
  is already decoded exactly once (column j decodes entries 0..j, totaling
  n*(n+1)/2 with no repeats). Only the rotation map benefits from pre-decode
  because each `mulAdj` call re-reads all n*d entries (3456 calls total).

  Superseded by `checkCertificateFast` in `CertCheck.lean`.
  so `native_decide` automatically uses the fast version. The proof should
  be straightforward since both compute the same result — the only difference
  is when the base-85 decode happens (per-access vs upfront).
-/

import CertCheck


/-! **Pre-decode rotation map** -/

/-- Decode rotBytes into a flat neighbor array: `result[v*d+p] = neighbor vertex`. -/
def decodeNeighborsFast (rotBytes : ByteArray) (n d : Nat) : Array Nat :=
  Id.run do
    let nd := n * d
    let mut arr := Array.replicate nd 0
    for k in [:nd] do
      arr := arr.set! k (decodeBase85Nat rotBytes (2 * k))
    return arr


/-! **Fast mulAdj via pre-decoded array** -/

/-- `mulAdj` with pre-decoded neighbor array. No base-85 in the hot loop. -/
def mulAdjFast (neighbors : Array Nat) (z : Array ℤ) (n d : Nat) : Array ℤ :=
  Id.run do
    let mut result := Array.replicate n 0
    for v in [:n] do
      let mut acc : ℤ := 0
      for p in [:d] do
        let w := neighbors[v * d + p]!
        acc := acc + z[w]!
      result := result.set! v acc
    return result


/-! **Fast PSD certificate check** -/

/-- `checkPSDCertificate` with pre-decoded neighbor array. -/
def checkPSDCertificateFast (neighbors : Array Nat) (certBytes : ByteArray)
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

      let bz := mulAdjFast neighbors zCol n d
      let b2z := mulAdjFast neighbors bz n d

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


/-! **Combined fast check** -/

/-- Fast version of `checkCertificateSlow`. Same result, ~2x faster for large n.
    Pre-decodes rotation map once, then uses array lookups in the hot loop. -/
def checkCertificateFastV1 (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : ℤ) : Bool :=
  let rotBytes := rotStr.toUTF8
  let certBytes := certStr.toUTF8
  if !checkInvolution rotBytes n d then false
  else
    let neighbors := decodeNeighborsFast rotBytes n d
    checkPSDCertificateFast neighbors certBytes n d c₁ c₂ c₃
