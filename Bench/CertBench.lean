/-
  # Certificate Checker Benchmarks

  Benchmarks for the certificate checking pipeline at various graph sizes.
  Each function returns data that gets printed, forcing evaluation.

  Run: `lake exe cert-bench`
-/

import CertCheck
import AKS.Cert.Read

#eval ensureCertificateData 16 4
#eval ensureCertificateData 1728 12
#eval ensureCertificateData 20736 12

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

/-- Time a named computation, print result + elapsed. -/
def timed (name : String) (f : Unit → String) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let result := f ()
  IO.print s!"  {name}: {result}"
  let t1 ← IO.monoNanosNow
  IO.println s!" [{fmtNs (t1 - t0)}]"

/-- Benchmark suite for one graph size. -/
def benchSuite (label : String) (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : Int) : IO Unit := do
  IO.println s!"--- {label} (n={n}, d={d}) ---"

  timed "baseline full    " fun () =>
    s!"ok={checkCertificateSlow rotStr certStr n d c₁ c₂ c₃}"

  for numTasks in [1, 4, 16, 64] do
    let label := s!"tasks={numTasks}"
    let padded := label ++ String.ofList (List.replicate (17 - label.length) ' ')
    timed padded fun () =>
      s!"ok={checkCertificate rotStr certStr n d c₁ c₂ c₃ numTasks}"

  IO.println ""

/-- Fast-only benchmark for large graphs (skips slow baseline and parallel variants). -/
def benchFastOnly (label : String) (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : Int) : IO Unit := do
  IO.println s!"--- {label} (n={n}, d={d}) ---"

  timed "prod fast        " fun () =>
    s!"ok={checkCertificate rotStr certStr n d c₁ c₂ c₃}"

  IO.println ""

def rotData16 : String := bin_base85% "data/16/rot_map.b85"
def certData16 : String := bin_base85% "data/16/cert_z.b85"

def rotData1728 : String := bin_base85% "data/1728/rot_map.b85"
def certData1728 : String := bin_base85% "data/1728/cert_z.b85"

def main : IO UInt32 := do
  IO.println "=== Certificate Checker Benchmarks ==="
  IO.println ""

  benchSuite "n=16" rotData16 certData16 16 4 216 9 1
  benchSuite "n=1728" rotData1728 certData1728 1728 12 792 9 2

  IO.println "--- n=20736 (n=20736, d=12) ---"
  IO.print "  loading data..."
  let t0 ← IO.monoNanosNow
  let rotStr ← loadBase85 "data/20736/rot_map.b85"
  let certStr ← loadBase85 "data/20736/cert_z.b85"
  let t1 ← IO.monoNanosNow
  IO.println s!" [{fmtNs (t1 - t0)}]"

  timed "prod fast        " fun () =>
    s!"ok={checkCertificate rotStr certStr 20736 12 792 9 2}"

  IO.println ""
  IO.println "Done."
  return 0
