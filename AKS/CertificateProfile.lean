/-
  # Certificate Checker Profiling for n=1728

  Profiles the individual steps of `native_decide` certificate checking
  for the 1728-vertex, 12-regular graph. The goal is to find what's slow
  when `native_decide` times out at 120s on `Random1728.lean`.

  Run: `lake exe cert-profile`
-/

import AKS.Certificate
import AKS.CertificateFast
import AKS.NpyReader

def rotData1728p : String := bin_base85% "data/1728/rot_map.bin"
def certData1728p : String := bin_base85% "data/1728/cert_z.bin"

/-- Format nanoseconds as human-readable string. -/
def fmtNsP (ns : Nat) : String :=
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

/-- Time a pure computation via thunk, printing result + elapsed. -/
def timedP (name : String) (f : Unit → String) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let result := f ()
  IO.print s!"  {name}: {result}"
  let t1 ← IO.monoNanosNow
  IO.println s!"  [{fmtNsP (t1 - t0)}]"

def main : IO UInt32 := do
  IO.println "=== Certificate Profiling: n=1728, d=12 ==="
  IO.println ""

  let n := 1728
  let d := 12
  let c₁ : ℤ := 792
  let c₂ : ℤ := 9
  let c₃ : ℤ := 2

  -- Data sizes
  IO.println "--- Data sizes ---"
  IO.println s!"  rotData1728 string length: {rotData1728p.length}"
  IO.println s!"  certData1728 string length: {certData1728p.length}"
  IO.println ""

  -- Pre-convert for subsequent tests
  let rotBytes := rotData1728p.toUTF8
  let certBytes := certData1728p.toUTF8

  -- 1. Time String.toUTF8 conversion
  IO.println "--- String.toUTF8 ---"
  timedP "rot toUTF8      " fun () =>
    s!"size={rotData1728p.toUTF8.size}"
  timedP "cert toUTF8     " fun () =>
    s!"size={certData1728p.toUTF8.size}"
  IO.println ""

  -- 2. Time checkInvolution alone
  IO.println "--- checkInvolution (n=1728, d=12) ---"
  timedP "checkInvolution " fun () =>
    s!"ok={checkInvolution rotBytes n d}"
  IO.println ""

  -- 3. Time a single mulAdj call
  IO.println "--- Single mulAdj (B*ones, n=1728, d=12) ---"
  timedP "mulAdj (ones)   " fun () => Id.run do
    let zOnes := Array.replicate n (1 : ℤ)
    let bz := mulAdj rotBytes zOnes n d
    let mut s : ℤ := 0
    for i in [:n] do s := s + bz[i]!
    return s!"sum={s}"
  IO.println ""

  -- 4. Time B²*ones (two mulAdj calls)
  IO.println "--- Double mulAdj (B²*ones, n=1728, d=12) ---"
  timedP "B²*ones         " fun () => Id.run do
    let zOnes := Array.replicate n (1 : ℤ)
    let bz := mulAdj rotBytes zOnes n d
    let b2z := mulAdj rotBytes bz n d
    let mut s : ℤ := 0
    for i in [:n] do s := s + b2z[i]!
    return s!"sum={s}"
  IO.println ""

  -- 5. Time checkPSDCertificate alone (baseline, the main bottleneck)
  IO.println "--- checkPSDCertificate (n=1728, d=12) ---"
  IO.println "  (1728 columns × 2 mulAdj calls each = 3456 matvec products)"
  timedP "checkPSD        " fun () =>
    s!"ok={checkPSDCertificate rotBytes certBytes n d c₁ c₂ c₃}"
  IO.println ""

  -- 6. Time checkPSD with diagnostics (forces evaluation of margin)
  IO.println "--- checkPSD with diagnostics ---"
  timedP "checkPSD (diag) " fun () => Id.run do
    let mut epsMax : ℤ := 0
    let mut minDiag : ℤ := 0
    let mut first := true
    for j in [:n] do
      let colStart := j * (j + 1) / 2
      let mut zCol := Array.replicate n (0 : ℤ)
      for k in [:j+1] do
        zCol := zCol.set! k (decodeBase85Int certBytes (colStart + k))
      let bz := mulAdj rotBytes zCol n d
      let b2z := mulAdj rotBytes bz n d
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
    return s!"ok={decide (minDiag > threshold)} minDiag={minDiag} epsMax={epsMax} threshold={threshold}"
  IO.println ""

  -- 7. Time checkCertificate end-to-end (from String)
  IO.println "--- checkCertificate (end-to-end, from String) ---"
  timedP "checkCertificate" fun () =>
    s!"ok={checkCertificate rotData1728p certData1728p n d c₁ c₂ c₃}"
  IO.println ""

  -- 8. Time the Fast version for comparison
  IO.println "--- checkCertificateFast (V2 pre-decoded) ---"
  timedP "fast version    " fun () =>
    s!"ok={checkCertificateFast rotData1728p certData1728p n d c₁ c₂ c₃}"
  IO.println ""

  -- 9. Breakdown: decode vs compute
  IO.println "--- Breakdown: decode cost ---"
  timedP "decode all cert " fun () => Id.run do
    -- Time just decoding all n*(n+1)/2 cert entries
    let total := n * (n + 1) / 2
    let mut s : ℤ := 0
    for k in [:total] do
      s := s + decodeBase85Int certBytes k
    return s!"sum={s} (over {total} entries)"
  IO.println ""

  timedP "decode all rot  " fun () => Id.run do
    -- Time decoding all n*d rotation map entries
    let nd := n * d
    let mut s : Nat := 0
    for k in [:nd] do
      s := s + decodeBase85Nat rotBytes (2 * k)
    return s!"sum={s} (over {nd} entries)"
  IO.println ""

  -- 10. Repeated runs for consistency
  IO.println "--- Repeated runs (3x checkCertificate) ---"
  for i in [:3] do
    timedP s!"run {i}           " fun () =>
      s!"ok={checkCertificate rotData1728p certData1728p n d c₁ c₂ c₃}"
  IO.println ""

  -- Analysis
  IO.println "=== Analysis ==="
  IO.println "  Expected breakdown for n=1728:"
  IO.println "    checkInvolution: ~5% (one pass over rotation map)"
  IO.println "    checkPSD:        ~95% (dominated by 3456 mulAdj calls)"
  IO.println "  Within checkPSD:"
  IO.println "    base-85 decode:  ~60% (decode cert + decode rot per mulAdj)"
  IO.println "    integer arith:   ~40% (multiply-accumulate in inner loop)"

  return 0
