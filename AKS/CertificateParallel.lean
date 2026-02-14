/-
  # Task-Parallel Certificate Checker

  Parallelized version of `checkPSDCertificate`: splits the n independent
  column computations across multiple OS threads via `Task.spawn`.

  Key: use `Task.spawn` (pure tasks), not `IO.asTask` (IO tasks). The IO
  variant adds overhead that cancels the parallelism benefit.

  Each column j independently:
  1. Extracts column j from the triangular certificate
  2. Computes B·z and B²·z (two matrix-vector products via rotation map)
  3. Computes P[:,j] = c₁·z - c₂·B²z + c₃·(1ᵀz)·1
  4. Tracks epsMax (max off-diagonal |P[i,j]|) and minDiag (min diagonal P[j,j])

  Uses pre-decoded neighbor array (the V2/Fast optimization) to avoid
  base-85 decoding in the hot loop.
-/

import AKS.Certificate
import AKS.CertificateFast


/-! **Chunk result type** -/

/-- Result from processing a chunk of columns: `(epsMax, minDiag, first)`.
    `first = true` means no diagonal entry was seen (chunk was empty). -/
structure ChunkResult where
  epsMax : ℤ
  minDiag : ℤ
  first : Bool
  deriving Repr

/-- Merge two chunk results by taking the max epsMax and min minDiag. -/
def ChunkResult.merge (a b : ChunkResult) : ChunkResult :=
  if a.first then b
  else if b.first then a
  else {
    epsMax := if a.epsMax > b.epsMax then a.epsMax else b.epsMax
    minDiag := if a.minDiag < b.minDiag then a.minDiag else b.minDiag
    first := false
  }


/-! **Per-chunk PSD computation** -/

/-- Process columns `[lo, hi)` of the PSD certificate, returning the chunk's
    `(epsMax, minDiag, first)`. Uses pre-decoded neighbor array for fast
    matrix-vector products. -/
def checkPSDChunk (neighbors : Array Nat) (certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : ℤ) (lo hi : Nat) : ChunkResult :=
  Id.run do
    let mut epsMax : ℤ := 0
    let mut minDiag : ℤ := 0
    let mut first := true

    for j in [lo:hi] do
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

    return { epsMax, minDiag, first }


/-! **Parallel PSD certificate check** -/

/-- Check the PSD certificate using task parallelism.
    Splits `n` columns into `numChunks` chunks, processes each on a dedicated
    OS thread via `Task.spawn`, then merges results. -/
def checkPSDCertificateParallel (neighbors : Array Nat) (certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : ℤ) (numChunks : Nat := 4) : IO Bool := do
  if certBytes.size != n * (n + 1) / 2 * 5 then return false

  -- Compute chunk boundaries
  let nc := if numChunks == 0 then 1 else numChunks
  let chunkSize := (n + nc - 1) / nc

  -- Launch pure tasks on dedicated OS threads
  let mut tasks : Array (Task ChunkResult) := #[]
  for c in [:nc] do
    let lo := c * chunkSize
    let hi := min ((c + 1) * chunkSize) n
    if lo < hi then
      let task := Task.spawn (prio := .dedicated) fun () =>
        checkPSDChunk neighbors certBytes n d c₁ c₂ c₃ lo hi
      tasks := tasks.push task

  -- Collect results
  let mut merged : ChunkResult := { epsMax := 0, minDiag := 0, first := true }
  for task in tasks do
    merged := merged.merge task.get

  -- Gershgorin check
  let threshold := merged.epsMax * (n * (n + 1) / 2)
  return !merged.first && decide (merged.minDiag > threshold)


/-! **Combined parallel check** -/

/-- Full certificate check with parallel PSD verification.
    Pre-decodes the rotation map, validates involution sequentially,
    then runs PSD check in parallel. -/
def checkCertificateParallel (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : ℤ) (numChunks : Nat := 4) : IO Bool := do
  let rotBytes := rotStr.toUTF8
  let certBytes := certStr.toUTF8
  if !checkInvolution rotBytes n d then return false
  let neighbors := decodeNeighborsFast rotBytes n d
  checkPSDCertificateParallel neighbors certBytes n d c₁ c₂ c₃ numChunks
