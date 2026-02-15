/-
  # Certificate Checker V2: Pre-decoded Neighbor Array

  Optimization: decode the base-85 rotation map into a flat `Array Nat` at
  startup, so `mulAdj` becomes pure array lookups with no base-85 decoding
  in the hot loop.

  `neighbors[v*d+p] = destination vertex` (we only need the vertex, not the port).
-/

import AKS.Certificate


/-! **Pre-decode rotation map** -/

/-- Decode rotBytes into a flat neighbor array: `result[v*d+p] = neighbor vertex`. -/
def decodeNeighbors (rotBytes : ByteArray) (n d : Nat) : Array Nat :=
  Id.run do
    let nd := n * d
    let mut arr := Array.replicate nd 0
    for k in [:nd] do
      arr := arr.set! k (decodeBase85Nat rotBytes (2 * k))
    return arr


/-! **Optimized mulAdj via pre-decoded array** -/

/-- Matrix-vector product using pre-decoded neighbor array (no base-85 in hot loop). -/
def mulAdjV2 (neighbors : Array Nat) (z : Array ℤ) (n d : Nat) : Array ℤ :=
  Id.run do
    let mut result := Array.replicate n 0
    for v in [:n] do
      let mut acc : ℤ := 0
      for p in [:d] do
        let w := neighbors[v * d + p]!
        acc := acc + z[w]!
      result := result.set! v acc
    return result


/-! **Optimized involution check** -/

/-- Check involution using pre-decoded arrays (both vertex and port). -/
def checkInvolutionV2 (rotBytes : ByteArray) (n d : Nat) : Bool :=
  let nd := n * d
  if rotBytes.size != nd * 2 * 5 then false
  else Id.run do
    -- Pre-decode both vertex and port arrays
    let mut verts := Array.replicate nd 0
    let mut ports := Array.replicate nd 0
    for k in [:nd] do
      verts := verts.set! k (decodeBase85Nat rotBytes (2 * k))
      ports := ports.set! k (decodeBase85Nat rotBytes (2 * k + 1))
    -- Check involution
    let mut ok := true
    for k in [:nd] do
      let w := verts[k]!
      let q := ports[k]!
      if w >= n || q >= d then
        ok := false
        break
      let k2 := w * d + q
      if verts[k2]! * d + ports[k2]! != k then
        ok := false
        break
    return ok


/-! **Optimized PSD certificate check** -/

/-- PSD certificate check with pre-decoded neighbor array. -/
def checkPSDCertificateV2 (neighbors : Array Nat) (certBytes : ByteArray)
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

      let bz := mulAdjV2 neighbors zCol n d
      let b2z := mulAdjV2 neighbors bz n d

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

/-- Full certificate check V2: pre-decode neighbors, then check involution + PSD. -/
def checkCertificateV2 (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : ℤ) : Bool :=
  let rotBytes := rotStr.toUTF8
  let certBytes := certStr.toUTF8
  -- Still use original involution check (it's one-time cost)
  if !checkInvolution rotBytes n d then false
  else
    let neighbors := decodeNeighbors rotBytes n d
    checkPSDCertificateV2 neighbors certBytes n d c₁ c₂ c₃
