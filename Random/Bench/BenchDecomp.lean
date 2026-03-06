module
/-
  # Column Partition Benchmark

  Tests different column-to-task assignments for the parallel PSD checker.
  Validates at n=20736 (fast), then runs key comparisons at n=65536.

  Strategies:
  - **interleaved** (current `roundRobinPartition`): column j → task j % T
  - **contiguous**: column j → task j·T/n (poor load balance, great locality)
  - **balanced**: contiguous blocks with equal-work boundaries at n·√(t/T)
  - **block-interleaved**: blocks of B columns round-robin to tasks

  Run: `lake exe bench-decomp`
-/

public import Random.Cert

@[expose] public section


/-! **Alternative partition strategies** -/

/-- Contiguous column partition: task `t` gets columns `[t·n/T, (t+1)·n/T)`. -/
def contiguousColumnLists (n numChunks : Nat) : Array (Array (Fin n)) :=
  if numChunks == 0 then #[]
  else Id.run do
    let mut lists := Array.replicate numChunks (Array.mkEmpty (n / numChunks + 1))
    for h : j in [:n] do
      have hj : j < n := by have := h.upper; simp at this; omega
      let c := min (j * numChunks / n) (numChunks - 1)
      lists := lists.set! c (lists[c]!.push ⟨j, hj⟩)
    return lists

/-- Balanced contiguous partition: boundaries at `n·√(t/T)` so each task
    gets roughly equal work. Implemented as `c = T·j²/n²`. -/
def balancedColumnLists (n numChunks : Nat) : Array (Array (Fin n)) :=
  if numChunks == 0 then #[]
  else Id.run do
    let nn := n * n
    let mut lists := Array.replicate numChunks (Array.mkEmpty (n / numChunks + 1))
    for h : j in [:n] do
      have hj : j < n := by have := h.upper; simp at this; omega
      let c := if nn == 0 then 0 else min (numChunks * j * j / nn) (numChunks - 1)
      lists := lists.set! c (lists[c]!.push ⟨j, hj⟩)
    return lists

/-- Block-interleaved partition: blocks of `blockSize` columns round-robin
    assigned to tasks. -/
def blockInterleavedColumnLists (n numChunks blockSize : Nat) : Array (Array (Fin n)) :=
  if numChunks == 0 then #[]
  else
    let bs := if blockSize == 0 then 1 else blockSize
    Id.run do
      let mut lists := Array.replicate numChunks (Array.mkEmpty (n / numChunks + 1))
      for h : j in [:n] do
        have hj : j < n := by have := h.upper; simp at this; omega
        let block := j / bs
        let c := block % numChunks
        lists := lists.set! c (lists[c]!.push ⟨j, hj⟩)
      return lists


/-! **Partition-generic checker** -/

/-- Certificate checker taking an explicit column partition. -/
@[inline] def checkWithPartition (rotStr : String) (entry : Nat → Nat → Int)
    (n d : Nat) (c₁ c₂ c₃ : Int) (partition : Array (Array (Fin n))) : Bool :=
  checkInvolution rotStr n d &&
  allDiagPositive entry n &&
    let neighbors := decodeNeighbors rotStr n d
    let spawned := partition.map fun cols =>
      Task.spawn (prio := .dedicated) fun () =>
        checkPSDColumnsFull neighbors n d c₁ c₂ c₃ cols entry
    let results := spawned.map Task.get
    let merged := (results.map (·.1)).foldl PSDChunkResult.merge
      { epsMax := 0, minDiag := 0, first := true }
    if merged.first then false
    else
      decide (merged.minDiag > merged.epsMax * (n * (n + 1) / 2)) &&
      let norms := flattenNorms partition results
      Id.run do
        let ε := merged.epsMax
        let mdpe := merged.minDiag + ε
        let mut prefSum : Int := 0
        for i in [:n] do
          let si := norms[i]!
          let ti := prefSum + (↑(n - i) : Int) * si
          if !(entry i i * mdpe > ε * ti) then
            return false
          prefSum := prefSum + si
        return true


/-! **Benchmark harness** -/

def fmtNs (ns : Nat) : String :=
  if ns < 1000 then s!"{ns} ns"
  else if ns < 1000000 then
    let us := ns / 1000
    let frac := (ns % 1000) / 100
    s!"{us}.{frac} μs"
  else if ns < 1000000000 then
    let ms := ns / 1000000
    let frac := (ns % 1000000) / 100000
    s!"{ms}.{frac} ms"
  else
    let sec := ns / 1000000000
    let frac := (ns % 1000000000) / 100000000
    s!"{sec}.{frac} s"

@[noinline] def evalBool (f : Unit → Bool) : IO Bool := do
  return f ()

def bench (label : String) (f : Unit → Bool) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStr s!"  {label} ..."
  stdout.flush
  let t0 ← IO.monoNanosNow
  let ok ← evalBool f
  let t1 ← IO.monoNanosNow
  let elapsed := t1 - t0
  let pad := String.ofList (List.replicate (24 - min label.length 24) ' ')
  stdout.putStr s!"\r  {label}{pad} ok={ok}  [{fmtNs elapsed}]\n"
  stdout.flush

def runSuite (label : String) (rotStr : String) (entry : Nat → Nat → Int)
    (n d : Nat) (c₁ c₂ c₃ : Int) (taskCounts : List Nat) : IO Unit := do
  IO.println s!"=== {label} (n={n}, d={d}) ==="
  IO.println ""
  for tasks in taskCounts do
    IO.println s!"--- tasks={tasks} ---"

    bench "interleaved" fun () =>
      checkWithPartition rotStr entry n d c₁ c₂ c₃ (roundRobinPartition n tasks)

    bench "contiguous" fun () =>
      checkWithPartition rotStr entry n d c₁ c₂ c₃ (contiguousColumnLists n tasks)

    bench "balanced" fun () =>
      checkWithPartition rotStr entry n d c₁ c₂ c₃ (balancedColumnLists n tasks)

    bench s!"block-256" fun () =>
      checkWithPartition rotStr entry n d c₁ c₂ c₃
        (blockInterleavedColumnLists n tasks 256)

    IO.println ""

def main (args : List String) : IO UInt32 := do
  let mode := args.headD "small"

  if mode == "small" || mode == "all" then
    -- Quick validation at n=20736
    IO.print "Loading n=20736..."
    let t0 ← IO.monoNanosNow
    let rot20k ← loadAsciiFile "data/20736/rot_map.b85"
    let cert20k ← loadAsciiFile "data/20736/cert_z.b128"
    let t1 ← IO.monoNanosNow
    IO.println s!" [{fmtNs (t1 - t0)}]"
    IO.println ""

    runSuite "n=20736 b128" rot20k (b128entry 2000000000 cert20k)
      20736 12 792 9 2 [4, 8, 16]

  if mode == "large" || mode == "all" then
    -- Full benchmark at n=65536
    IO.print "Loading n=65536..."
    let t0 ← IO.monoNanosNow
    let rot65k ← loadAsciiFile "data/65536/rot_map.b85"
    let cert65k ← loadAsciiFile "data/65536/cert_z.b128"
    let t1 ← IO.monoNanosNow
    IO.println s!" [{fmtNs (t1 - t0)}]"
    IO.println ""

    runSuite "n=65536 b128" rot65k (b128entry 2000000000 cert65k)
      65536 16 760 9 2 [4, 8, 16]

  IO.println "Done."
  return 0

end
