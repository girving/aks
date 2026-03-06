module
/-
  # Certificate Checker Benchmarks

  Benchmarks for the certificate checking pipeline at various graph sizes.
  Each function returns data that gets printed, forcing evaluation.

  Run: `lake exe cert-bench`
-/

public import Random.Cert
public import Random.Bridge.Read

@[expose] public section


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

  for numTasks in ([1, 4, 16, 64] : List Nat) do
    let label := s!"tasks={numTasks}"
    let padded := label ++ String.ofList (List.replicate (17 - label.length) ' ')
    timed padded fun () =>
      s!"ok={checkCertificate rotStr certStr n d c₁ c₂ c₃ (roundRobinPartition n numTasks)}"

  IO.println ""

/-- Fast-only benchmark for large graphs (skips slow baseline and parallel variants). -/
def benchFastOnly (label : String) (rotStr certStr : String)
    (n d : Nat) (c₁ c₂ c₃ : Int) : IO Unit := do
  IO.println s!"--- {label} (n={n}, d={d}) ---"

  timed "prod fast        " fun () =>
    s!"ok={checkCertificate rotStr certStr n d c₁ c₂ c₃}"

  IO.println ""

def rotData16 : String := ascii_file% "data/16/rot_map.b85"
def certData16 : String := ascii_file% "data/16/cert_z.b85"

def rotData1728 : String := ascii_file% "data/1728/rot_map.b85"
def certData1728 : String := ascii_file% "data/1728/cert_z.b85"

def main : IO UInt32 := do
  IO.println "=== Certificate Checker Benchmarks ==="
  IO.println ""

  benchSuite "n=16" rotData16 certData16 16 4 216 9 1
  benchSuite "n=1728" rotData1728 certData1728 1728 12 792 9 2

  IO.println "--- n=20736 b85 (scale=350M) ---"
  IO.print "  loading data..."
  let t0 ← IO.monoNanosNow
  let rotStr ← loadAsciiFile "/tmp/cert20736_b85_s350m/rot_map.b85"
  let certB85 ← loadAsciiFile "/tmp/cert20736_b85_s350m/cert_z.b85"
  let t1 ← IO.monoNanosNow
  IO.println s!" [{fmtNs (t1 - t0)}]"

  timed "b85 fast         " fun () =>
    s!"ok={checkCertificate rotStr certB85 20736 12 792 9 2}"

  IO.println ""

  IO.println "--- n=20736 b128 (scale=350M) ---"
  IO.print "  loading data..."
  let t2 ← IO.monoNanosNow
  let certB128 ← loadAsciiFile "/tmp/cert20736_b128/cert_z.b128"
  let t3 ← IO.monoNanosNow
  IO.println s!" [{fmtNs (t3 - t2)}]"

  timed "b128 fast        " fun () =>
    s!"ok={checkCertificateB128 rotStr certB128 20736 12 792 9 2 350000000}"

  IO.println ""
  IO.println "Done."
  return 0

end
