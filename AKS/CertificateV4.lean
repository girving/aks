/-
  # Certificate Checker V4: Fused B²z Computation

  Optimization: instead of computing Bz then B(Bz), compute B²z directly
  by walking 2 hops: `(B²z)[v] = ∑_p ∑_q z[neighbor(neighbor(v,p), q)]`.

  This eliminates the intermediate array allocation and one full pass.
  Trade-off: O(n*d²) decodes vs 2*O(n*d), same for constant d but fewer
  array ops.
-/

import AKS.Certificate


/-! **Fused B²z** -/

/-- Compute B²z in one pass: for each vertex v, walk 2 hops through the
    rotation map. `(B²z)[v] = ∑_p ∑_q z[neighbor(neighbor(v,p), q)]`. -/
def mulAdj2 (rotBytes : ByteArray) (z : Array ℤ) (n d : Nat) : Array ℤ :=
  Id.run do
    let mut result := Array.replicate n 0
    for v in [:n] do
      let mut acc : ℤ := 0
      for p in [:d] do
        let k1 := v * d + p
        let w := decodeBase85Nat rotBytes (2 * k1)
        -- Second hop: walk from w through all its ports
        for q in [:d] do
          let k2 := w * d + q
          let u := decodeBase85Nat rotBytes (2 * k2)
          acc := acc + z[u]!
      result := result.set! v acc
    return result


/-! **PSD certificate check with fused B²z** -/

/-- PSD certificate check using fused B²z computation. -/
def checkPSDCertificateV4 (rotBytes certBytes : ByteArray)
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

      -- Fused B²z (single pass, no intermediate array)
      let b2z := mulAdj2 rotBytes zCol n d

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

/-- Full certificate check V4: fused B²z computation. -/
def checkCertificateV4 (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : ℤ) : Bool :=
  let rotBytes := rotStr.toUTF8
  let certBytes := certStr.toUTF8
  checkInvolution rotBytes n d &&
  checkPSDCertificateV4 rotBytes certBytes n d c₁ c₂ c₃
