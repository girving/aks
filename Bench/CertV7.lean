/-
  # Certificate Checker V7: Optimized PSD Check

  Optimizations over V2 (pre-decoded neighbors):
  1. **Buffer reuse**: Preallocate zCol, bz once and reuse across columns
     instead of allocating fresh arrays per column.
  2. **Sparse first mulAdj**: For column j, zCol has only j+1 nonzero entries.
     Use scatter (iterate over nonzero z entries) instead of gather.
  3. **Inline second mulAdj**: Only compute (B²z)[i] for i in [0, j] (the
     entries we actually check), not all n entries. Inlined into Gershgorin loop.
  4. **Truncated inner loop**: Iterate i in [:j+1] instead of [:n].

  Key insight for (3): the Gershgorin check only needs b2z[i] for i ≤ j,
  but the full mulAdj computes it for all n vertices. Inlining saves ~50%
  of the second mulAdj work.

  Run: `lake exe cert-bench`
-/

import CertCheck
import Bench.CertFast


/-! **Optimized PSD check** -/

/-- `checkPSDCertificate` with all optimizations. -/
def checkPSDCertificateV7 (neighbors : Array Nat) (certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : Int) : Bool :=
  if certBytes.size != n * (n + 1) / 2 * 5 then false
  else Id.run do
    let mut epsMax : Int := 0
    let mut minDiag : Int := 0
    let mut first := true

    -- Preallocate buffers (reused across columns)
    let mut zCol := Array.replicate n (0 : Int)
    let mut bz := Array.replicate n (0 : Int)

    for j in [:n] do
      let colStart := j * (j + 1) / 2

      -- Zero bz for scatter
      for v in [:n] do
        bz := bz.set! v 0

      -- Combined: decode cert → zCol, scatter → bz, accumulate colSum
      let mut colSum : Int := 0
      for k in [:j+1] do
        let zk := decodeBase85Int certBytes (colStart + k)
        zCol := zCol.set! k zk
        colSum := colSum + zk
        for p in [:d] do
          let w := neighbors[k * d + p]!
          bz := bz.set! w (bz[w]! + zk)

      -- Gershgorin check with inlined B²z computation
      -- Instead of computing all n entries of b2z = B·bz, compute only
      -- (B·bz)[i] = ∑_p bz[neighbor(i,p)] for i ≤ j, which is all we need.
      for i in [:j+1] do
        -- Inline (B²z)[i] = (B·bz)[i]
        let mut b2zi : Int := 0
        for p in [:d] do
          let w := neighbors[i * d + p]!
          b2zi := b2zi + bz[w]!
        let pij := c₁ * zCol[i]! - c₂ * b2zi + c₃ * colSum
        if i == j then
          if first then
            minDiag := pij
            first := false
          else if pij < minDiag then
            minDiag := pij
        else  -- i < j
          let absPij := if pij >= 0 then pij else -pij
          if absPij > epsMax then
            epsMax := absPij

      -- No need to zero zCol: columns are in ascending order,
      -- so the next column overwrites all entries.

    let threshold := epsMax * (n * (n + 1) / 2)
    decide (minDiag > threshold)


/-! **Combined check** -/

/-- Full certificate check V7. -/
def checkCertificateV7 (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : Int) : Bool :=
  let rotBytes := rotStr.toUTF8
  let certBytes := certStr.toUTF8
  if !checkInvolution rotBytes n d then false
  else
    let neighbors := decodeNeighborsFast rotBytes n d
    checkPSDCertificateV7 neighbors certBytes n d c₁ c₂ c₃
