/-
  Profile the actual computation time via #eval (uses the interpreter).
  This measures how long checkPSDCertificate takes in Lean's interpreter,
  which is closer to what native_decide experiences during elaboration.
-/

import AKS.Certificate
import AKS.NpyReader

def rotData1728 : String := bin_base85% "data/1728/rot_map.bin"
def certData1728 : String := bin_base85% "data/1728/cert_z.bin"

-- #eval runs through the interpreter. Times here approximate native_decide cost.
-- Use IO.println between timestamps to force evaluation (println is strict).
#eval show IO Unit from do
  IO.println "Starting profiling..."

  let t0 ← IO.monoNanosNow
  let rotBytes := rotData1728.toUTF8
  IO.println s!"rotBytes.size = {rotBytes.size}"
  let t1 ← IO.monoNanosNow
  IO.println s!"  rot toUTF8: {(t1 - t0) / 1000000} ms"

  let certBytes := certData1728.toUTF8
  IO.println s!"certBytes.size = {certBytes.size}"
  let t2 ← IO.monoNanosNow
  IO.println s!"  cert toUTF8: {(t2 - t1) / 1000000} ms"

  let invOk := checkInvolution rotBytes 1728 12
  IO.println s!"checkInvolution = {invOk}"
  let t3 ← IO.monoNanosNow
  IO.println s!"  checkInvolution: {(t3 - t2) / 1000000} ms"

  let psdOk := checkPSDCertificate rotBytes certBytes 1728 12 792 9 2
  IO.println s!"checkPSDCertificate = {psdOk}"
  let t4 ← IO.monoNanosNow
  IO.println s!"  checkPSDCertificate: {(t4 - t3) / 1000000} ms"

  let fullOk := checkCertificateSlow rotData1728 certData1728 1728 12 792 9 2
  IO.println s!"checkCertificateSlow = {fullOk}"
  let t5 ← IO.monoNanosNow
  IO.println s!"  checkCertificateSlow: {(t5 - t4) / 1000000} ms"

  IO.println s!"total from first timestamp: {(t5 - t0) / 1000000} ms"
