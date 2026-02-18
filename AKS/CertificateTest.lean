/-
  # Certificate Checker Unit Tests

  Tests for the base-85 decoding, involution checking, matrix-vector product,
  and PSD certificate verification in `Certificate.lean`.

  Run: `lake exe cert-test`
-/

import AKS.Certificate
import AKS.NpyReader

/-- Encode a Nat as 5 base-85 bytes. -/
def encodeBase85 (u : Nat) : ByteArray :=
  Id.run do
    let mut result : ByteArray := .empty
    let mut v := u
    for _ in [:5] do
      result := result.push (UInt8.ofNat (v % 85 + 33))
      v := v / 85
    return result

/-- Encode a list of (vertex, port) pairs into a base-85 rotation ByteArray. -/
def encodeRotMap (entries : Array (Nat × Nat)) : ByteArray :=
  Id.run do
    let mut result : ByteArray := .empty
    for (w, q) in entries do
      result := result.append (encodeBase85 w)
      result := result.append (encodeBase85 q)
    return result

/-- Run a single test, returning 1 on failure, 0 on success. -/
def check (name : String) (ok : Bool) : IO Nat := do
  if ok then
    IO.println s!"  PASS: {name}"
    return 0
  else
    IO.println s!"  FAIL: {name}"
    return 1

def main : IO UInt32 := do
  let mut failures : Nat := 0

  IO.println "=== Certificate Checker Unit Tests ==="

  -- decodeBase85Nat tests
  IO.println ""
  IO.println "--- decodeBase85Nat ---"

  failures := failures + (← check "decode 0" (decodeBase85Nat (encodeBase85 0) 0 == 0))
  failures := failures + (← check "decode 1" (decodeBase85Nat (encodeBase85 1) 0 == 1))
  failures := failures + (← check "decode 42" (decodeBase85Nat (encodeBase85 42) 0 == 42))
  failures := failures + (← check "decode 84" (decodeBase85Nat (encodeBase85 84) 0 == 84))
  failures := failures + (← check "decode 85" (decodeBase85Nat (encodeBase85 85) 0 == 85))

  -- decode at offset k=1
  let bytesOff := (encodeBase85 0).append (encodeBase85 42)
  failures := failures + (← check "decode at offset" (decodeBase85Nat bytesOff 1 == 42))

  -- roundtrip for several values
  let testValues := #[0, 1, 42, 84, 85, 7225, 100000, 1000000, 2147483647]
  let mut roundtripOk := true
  for u in testValues do
    let decoded := decodeBase85Nat (encodeBase85 u) 0
    if decoded != u then
      IO.println s!"  FAIL: roundtrip {u}, got {decoded}"
      roundtripOk := false
  if roundtripOk then IO.println s!"  PASS: roundtrip ({testValues.size} values)"
  else failures := failures + 1

  -- decodeBase85Int tests
  IO.println ""
  IO.println "--- decodeBase85Int ---"

  failures := failures + (← check "positive 42"
    (decodeBase85Int (encodeBase85 42) 0 == 42))
  failures := failures + (← check "negative -1"
    (decodeBase85Int (encodeBase85 4294967295) 0 == -1))
  failures := failures + (← check "negative -100"
    (decodeBase85Int (encodeBase85 4294967196) 0 == -100))
  failures := failures + (← check "max positive 2^31-1"
    (decodeBase85Int (encodeBase85 2147483647) 0 == 2147483647))
  failures := failures + (← check "min negative -2^31"
    (decodeBase85Int (encodeBase85 2147483648) 0 == -2147483648))

  -- checkInvolution tests
  IO.println ""
  IO.println "--- checkInvolution ---"

  -- 4-vertex, 2-regular graph (4-cycle: 0-1-2-3-0)
  let smallEntries : Array (Nat × Nat) := #[
    (1, 0), (3, 1), (0, 0), (2, 0),
    (1, 1), (3, 0), (2, 1), (0, 1)
  ]
  let smallRot := encodeRotMap smallEntries

  failures := failures + (← check "valid 4-cycle involution"
    (checkInvolution smallRot 4 2))
  failures := failures + (← check "wrong size rejected"
    (!checkInvolution ⟨#[33, 33]⟩ 4 2))

  -- Broken involution: corrupt first entry's vertex from 1 to 2
  let mut brokenRot := smallRot
  brokenRot := brokenRot.set! 0 (UInt8.ofNat (2 + 33))
  failures := failures + (← check "broken involution rejected"
    (!checkInvolution brokenRot 4 2))

  -- mulAdj tests
  IO.println ""
  IO.println "--- mulAdj ---"

  -- 4-cycle neighbors: v=0→{1,3}, v=1→{0,2}, v=2→{1,3}, v=3→{2,0}
  let z0 : Array ℤ := #[1, 0, 0, 0]
  let bz0 := mulAdj smallRot z0 4 2
  failures := failures + (← check "B·e₀ = [0,1,0,1]" (bz0 == #[0, 1, 0, 1]))

  let z1 : Array ℤ := #[1, 1, 1, 1]
  let bz1 := mulAdj smallRot z1 4 2
  failures := failures + (← check "B·1 = [2,2,2,2]" (bz1 == #[2, 2, 2, 2]))

  let z2 : Array ℤ := #[1, 0, 1, 0]
  let bz2 := mulAdj smallRot z2 4 2
  failures := failures + (← check "B·[1,0,1,0] = [0,2,0,2]" (bz2 == #[0, 2, 0, 2]))

  -- B²·1 = d²·1 for d-regular graph
  let b2one := mulAdj smallRot (mulAdj smallRot z1 4 2) 4 2
  failures := failures + (← check "B²·1 = [4,4,4,4]" (b2one == #[4, 4, 4, 4]))

  -- checkCertificateSlow end-to-end on n=16
  IO.println ""
  IO.println "--- checkCertificateSlow (n=16) ---"

  let rotData16 : String := bin_base85% "data/16/rot_map.bin"
  let certData16 : String := bin_base85% "data/16/cert_z.bin"

  failures := failures + (← check "n=16 certificate accepted"
    (checkCertificateSlow rotData16 certData16 16 4 216 9 1))
  failures := failures + (← check "n=16 involution valid"
    (checkInvolution rotData16.toUTF8 16 4))
  failures := failures + (← check "wrong coefficients rejected"
    (!checkCertificateSlow rotData16 certData16 16 4 1 1 1))

  -- Corrupted cert data: zero out many entries to break PSD
  let certBytes16 := certData16.toUTF8
  let mut corruptBytes := certBytes16
  -- Overwrite first 100 base-85 chars with '!' (zero entries)
  for i in [:100] do
    corruptBytes := corruptBytes.set! i 33
  let corruptCert := String.fromUTF8! corruptBytes
  failures := failures + (← check "corrupted certificate rejected"
    (!checkCertificateSlow rotData16 corruptCert 16 4 216 9 1))

  -- Wrong n/d (should fail size check)
  failures := failures + (← check "wrong n rejected"
    (!checkCertificateSlow rotData16 certData16 17 4 216 9 1))

  -- Summary
  IO.println ""
  if failures == 0 then
    IO.println "All tests passed!"
    return 0
  else
    IO.println s!"{failures} test(s) FAILED"
    return 1
