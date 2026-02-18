/-
  # Certificate Checker Benchmarks

  Benchmarks for the certificate checking pipeline at various graph sizes.
  Each function returns data that gets printed, forcing evaluation.

  Run: `lake exe cert-bench`
-/

import CertCheck
import Bench.CertV2
import Bench.CertParallel
import Bench.CertV7
import AKS.Cert.Read

#eval ensureCertificateData 16 4
#eval ensureCertificateData 1728 12

/-- Format nanoseconds as human-readable string. -/
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

/-- Like `checkPSDCertificate` but returns (ok, minDiag, epsMax) for diagnostics. -/
def checkPSDWithMargin (rotBytes certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : ℤ) : Bool × ℤ × ℤ :=
  if certBytes.size != n * (n + 1) / 2 * 5 then (false, 0, 0)
  else Id.run do
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
    return (decide (minDiag > threshold), minDiag, epsMax)

/-- Time a named computation, print result + elapsed. -/
def timed (name : String) (f : Unit → String) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let result := f ()
  IO.print s!"  {name}: {result}"
  let t1 ← IO.monoNanosNow
  IO.println s!" [{fmtNs (t1 - t0)}]"

/-- Time an IO computation, print result + elapsed. -/
def timedIO (name : String) (f : IO String) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let result ← f
  IO.print s!"  {name}: {result}"
  let t1 ← IO.monoNanosNow
  IO.println s!" [{fmtNs (t1 - t0)}]"

/-- Baseline benchmark suite for one graph size. -/
def benchBaseline (label : String) (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : ℤ) : IO Unit := do
  IO.println s!"--- {label} (n={n}, d={d}) ---"
  let rotBytes := rotStr.toUTF8
  let certBytes := certStr.toUTF8

  timed "baseline checkPSD" fun () =>
    let (ok, minDiag, epsMax) := checkPSDWithMargin rotBytes certBytes n d c₁ c₂ c₃
    s!"ok={ok} minDiag={minDiag} epsMax={epsMax}"

  timed "baseline full    " fun () =>
    s!"ok={checkCertificateSlow rotStr certStr n d c₁ c₂ c₃}"

  -- V2: pre-decoded neighbors
  let neighbors := decodeNeighbors rotBytes n d
  timed "V2 pre-decoded   " fun () =>
    s!"ok={checkPSDCertificateV2 neighbors certBytes n d c₁ c₂ c₃}"

  timed "V2 full          " fun () =>
    s!"ok={checkCertificateV2 rotStr certStr n d c₁ c₂ c₃}"

  -- V7: buffer reuse + truncated loop + sparse mulAdj + inlined B²z
  timed "V7 buf+trunc+spr " fun () =>
    s!"ok={checkCertificateV7 rotStr certStr n d c₁ c₂ c₃}"

  -- Parallel: task-parallel PSD check (various chunk counts)
  for numChunks in [2, 4, 8] do
    let label := s!"parallel ({numChunks} chunks)"
    let padded := label ++ String.ofList (List.replicate (17 - label.length) ' ')
    timedIO padded do
      let ok ← checkCertificateParallel rotStr certStr n d c₁ c₂ c₃ numChunks
      return s!"ok={ok}"

  IO.println ""

def rotData16 : String := bin_base85% "data/16/rot_map.bin"
def certData16 : String := bin_base85% "data/16/cert_z.bin"

def rotData1728 : String := bin_base85% "data/1728/rot_map.bin"
def certData1728 : String := bin_base85% "data/1728/cert_z.bin"

def main : IO UInt32 := do
  IO.println "=== Certificate Checker Benchmarks ==="
  IO.println ""

  benchBaseline "n=16" rotData16 certData16 16 4 216 9 1
  benchBaseline "n=1728" rotData1728 certData1728 1728 12 792 9 2

  IO.println "Done."
  return 0
