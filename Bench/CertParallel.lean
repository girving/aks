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
  base-85 decoding in the hot loop. Also uses V7 optimizations: buffer reuse,
  truncated inner loop, sparse first mulAdj.
-/

import CertCheck


/-! **Chunk result type** -/

/-- Result from processing a chunk of columns: `(epsMax, minDiag, first)`.
    `first = true` means no diagonal entry was seen (chunk was empty). -/
structure ChunkResult where
  epsMax : Int
  minDiag : Int
  first : Bool
  deriving Repr, Inhabited

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

/-- Process a list of column indices with buffer reuse, truncated loop, and
    sparse first mulAdj. Columns must be processed in order within the chunk
    for buffer reuse correctness (ascending column indices). -/
def checkPSDChunk (neighbors : Array Nat) (certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : Int) (columns : Array Nat) : ChunkResult :=
  Id.run do
    let mut epsMax : Int := 0
    let mut minDiag : Int := 0
    let mut first := true

    -- Preallocate buffers (reused across columns within this chunk)
    let mut zCol := Array.replicate n (0 : Int)
    let mut bz := Array.replicate n (0 : Int)

    for j in columns do
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

      -- Gershgorin check with inlined B²z
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
        else
          let absPij := if pij >= 0 then pij else -pij
          if absPij > epsMax then
            epsMax := absPij

    return { epsMax, minDiag, first }


/-! **Parallel PSD certificate check** -/

/-- Check the PSD certificate using task parallelism.
    Interleaves columns across chunks for load balancing (column j has
    O(j + n*d) work, so contiguous chunks are unbalanced).
    Uses `Task.spawn .dedicated` to run on dedicated OS threads. -/
def checkPSDCertificateParallel (neighbors : Array Nat) (certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : Int) (numChunks : Nat := 4) : IO Bool := do
  if certBytes.size != n * (n + 1) / 2 * 5 then return false

  let nc := if numChunks == 0 then 1 else numChunks

  -- Build interleaved column lists for load balancing
  -- Chunk c gets columns c, c+nc, c+2*nc, ...
  let mut columnLists := Array.replicate nc (Array.mkEmpty (n / nc + 1))
  for j in [:n] do
    let c := j % nc
    columnLists := columnLists.set! c (columnLists[c]!.push j)

  -- Launch pure tasks on dedicated OS threads
  let mut tasks : Array (Task ChunkResult) := #[]
  for c in [:nc] do
    let cols := columnLists[c]!
    if cols.size > 0 then
      let task := Task.spawn (prio := .dedicated) fun () =>
        checkPSDChunk neighbors certBytes n d c₁ c₂ c₃ cols
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
    (n d : Nat) (c₁ c₂ c₃ : Int) (numChunks : Nat := 4) : IO Bool := do
  let rotBytes := rotStr.toUTF8
  let certBytes := certStr.toUTF8
  if !checkInvolution rotBytes n d then return false
  let neighbors := decodeNeighbors rotBytes n d
  checkPSDCertificateParallel neighbors certBytes n d c₁ c₂ c₃ numChunks
