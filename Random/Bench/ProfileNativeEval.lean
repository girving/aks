module
/-
  Profile the actual computation time via #eval (uses the interpreter).
  This measures how long checkPSDCertificate takes in Lean's interpreter,
  which is closer to what native_decide experiences during elaboration.
-/

public import Random.Cert
public import Random.Bridge.Read

@[expose] public section


def rotData1728 : String := ascii_file% "data/1728/rot_map.b85"
def certData1728 : String := ascii_file% "data/1728/cert_z.b85"

-- #eval runs through the interpreter. Times here approximate native_decide cost.
-- Use IO.println between timestamps to force evaluation (println is strict).
#eval show IO Unit from do
  IO.println "Starting profiling..."

  let t0 ← IO.monoNanosNow
  IO.println s!"rotData1728.utf8ByteSize = {rotData1728.utf8ByteSize}"
  let t1 ← IO.monoNanosNow

  IO.println s!"certData1728.utf8ByteSize = {certData1728.utf8ByteSize}"
  let t2 ← IO.monoNanosNow

  let invOk := checkInvolution rotData1728 1728 12
  IO.println s!"checkInvolution = {invOk}"
  let t3 ← IO.monoNanosNow
  IO.println s!"  checkInvolution: {(t3 - t2) / 1000000} ms"

  let psdOk := checkPSDCertificate rotData1728 (b85entry certData1728) 1728 12 792 9 2
  IO.println s!"checkPSDCertificate = {psdOk}"
  let t4 ← IO.monoNanosNow
  IO.println s!"  checkPSDCertificate: {(t4 - t3) / 1000000} ms"

  let fullOk := checkCertificateSlow rotData1728 certData1728 1728 12 792 9 2
  IO.println s!"checkCertificateSlow = {fullOk}"
  let t5 ← IO.monoNanosNow
  IO.println s!"  checkCertificateSlow: {(t5 - t4) / 1000000} ms"

  IO.println s!"total from first timestamp: {(t5 - t0) / 1000000} ms"

end
