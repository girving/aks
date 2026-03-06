module
/-
  # Test mmap-based ASCII file reader

  Verifies `mmapReadAscii` against `IO.FS.readFile` for correctness, and tests
  all error conditions: missing files, permission denied, non-ASCII bytes,
  empty files, page-aligned sizes, and string usability with the certificate
  decoder.
-/

public import Random.Bridge.Read
public import Random.Cert
public import Batteries.Data.String.Matcher

@[expose] public section


/-! **Test infrastructure** -/

def green (s : String) : String := s!"\x1b[32m{s}\x1b[0m"
def red (s : String) : String := s!"\x1b[31m{s}\x1b[0m"

/-- Run a test, catching IO errors. Returns true on success. -/
def runTest (name : String) (action : IO Unit) : IO Bool := do
  IO.print s!"  {name} ... "
  try
    action
    IO.println (green "OK")
    return true
  catch e =>
    IO.println (red s!"FAIL: {e}")
    return false

/-- Assert that an IO action throws an error containing the given substring. -/
def expectError (action : IO Unit) (substr : String) : IO Unit := do
  try
    action
    throw (IO.userError "expected an error but action succeeded")
  catch e =>
    let msg := toString e
    unless msg.containsSubstr substr do
      throw (IO.userError s!"error message \"{msg}\" does not contain \"{substr}\"")

/-- Write a temporary file with the given bytes, returning its path. -/
def writeTempFile (name : String) (bytes : ByteArray) : IO String := do
  let dir := "/tmp/test_mmap"
  IO.FS.createDirAll dir
  let path := s!"{dir}/{name}"
  let h ← IO.FS.Handle.mk path .write
  h.write bytes
  return path

/-- Write a temporary file from a String. -/
def writeTempString (name : String) (content : String) : IO String := do
  let dir := "/tmp/test_mmap"
  IO.FS.createDirAll dir
  let path := s!"{dir}/{name}"
  IO.FS.writeFile ⟨path⟩ content
  return path

/-! **Happy path tests** -/

/-- Test that mmap matches readFile for a real certificate file. -/
def testMatchesReadFile (path : String) : IO Unit := do
  let s ← mmapReadAscii path
  let s2 ← IO.FS.readFile ⟨path⟩
  unless s == s2 do
    throw (IO.userError
      s!"mmap ({s.utf8ByteSize} bytes) differs from readFile ({s2.utf8ByteSize} bytes)")

/-- Test that mmap'd string has correct utf8ByteSize. -/
def testUtf8ByteSize : IO Unit := do
  let path ← writeTempString "size_test.txt" "hello"
  let s ← mmapReadAscii path
  unless s.utf8ByteSize == 5 do
    throw (IO.userError s!"expected utf8ByteSize=5, got {s.utf8ByteSize}")

/-- Test byte access on mmap'd string via strGet!. -/
def testByteAccess : IO Unit := do
  let path ← writeTempString "byte_access.txt" "ABCD"
  let s ← mmapReadAscii path
  let b0 := strGet! s 0  -- 'A' = 65
  let b1 := strGet! s 1  -- 'B' = 66
  let b3 := strGet! s 3  -- 'D' = 68
  unless b0 == 65 && b1 == 66 && b3 == 68 do
    throw (IO.userError s!"byte access failed: got {b0} {b1} {b3}, expected 65 66 68")

/-- Test that decodeBase85Nat works on mmap'd string. -/
def testBase85Decode : IO Unit := do
  let path := "data/16/rot_map.b85"
  let sMmap ← mmapReadAscii path
  let sFile ← IO.FS.readFile ⟨path⟩
  -- Decode first 10 base85 values from each and compare
  for k in [:10] do
    let v1 := decodeBase85Nat sMmap k
    let v2 := decodeBase85Nat sFile k
    unless v1 == v2 do
      throw (IO.userError s!"base85 decode mismatch at k={k}: mmap={v1} readFile={v2}")

/-- Test page-aligned file size (null terminator at page boundary). -/
def testPageAligned : IO Unit := do
  -- Create a file whose size is exactly 4096 bytes
  let content := String.ofList (List.replicate 4096 'A')
  let path ← writeTempString "page_aligned.txt" content
  let s ← mmapReadAscii path
  unless s.utf8ByteSize == 4096 do
    throw (IO.userError s!"expected 4096 bytes, got {s.utf8ByteSize}")
  unless s == content do
    throw (IO.userError "page-aligned content mismatch")

/-- Test file size = 1 byte. -/
def testOneByte : IO Unit := do
  let path ← writeTempString "one_byte.txt" "X"
  let s ← mmapReadAscii path
  unless s == "X" do
    throw (IO.userError s!"expected \"X\", got \"{s}\"")

/-- Test string equality and hashing work (exercises String.decEq). -/
def testEquality : IO Unit := do
  let path ← writeTempString "eq_test.txt" "hello world"
  let s1 ← mmapReadAscii path
  let s2 ← mmapReadAscii path
  unless s1 == s2 do
    throw (IO.userError "two mmap reads of same file are not equal")
  unless s1 == "hello world" do
    throw (IO.userError "mmap string does not equal literal")

/-! **Error condition tests** -/

/-- Test: file does not exist → IO error mentioning "open". -/
def testFileNotFound : IO Unit :=
  expectError (do let _ ← mmapReadAscii "/tmp/nonexistent_file_12345"; pure ()) "open"

/-- Test: path is a directory → IO error. -/
def testIsDirectory : IO Unit := do
  IO.FS.createDirAll "/tmp/test_mmap_dir"
  expectError (do let _ ← mmapReadAscii "/tmp/test_mmap_dir"; pure ()) "mmapReadAscii"

/-- Test: empty file → empty string (not an error). -/
def testEmptyFile : IO Unit := do
  let path ← writeTempString "empty.txt" ""
  let s ← mmapReadAscii path
  unless s == "" do
    throw (IO.userError s!"expected empty string, got {s.utf8ByteSize} bytes")

/-- Test: file with 0x80 byte at the start → error mentioning "non-ASCII". -/
def testNonAsciiStart : IO Unit := do
  let path ← writeTempFile "bad_start.bin" ⟨#[0x80, 0x41, 0x42]⟩
  expectError (do let _ ← mmapReadAscii path; pure ()) "non-ASCII"

/-- Test: file with 0xFF byte in the middle → error mentioning "non-ASCII". -/
def testNonAsciiMiddle : IO Unit := do
  let path ← writeTempFile "bad_middle.bin" ⟨#[0x41, 0x42, 0xFF, 0x43]⟩
  expectError (do let _ ← mmapReadAscii path; pure ()) "non-ASCII"

/-- Test: file with 0x80 byte at the very end → error mentioning "non-ASCII". -/
def testNonAsciiEnd : IO Unit := do
  let path ← writeTempFile "bad_end.bin" ⟨#[0x41, 0x42, 0x43, 0x80]⟩
  expectError (do let _ ← mmapReadAscii path; pure ()) "non-ASCII"

/-- Test: permission denied → IO error mentioning "open". -/
def testPermissionDenied : IO Unit := do
  let path ← writeTempString "no_read.txt" "secret"
  let ret ← IO.Process.output { cmd := "chmod", args := #["000", path] }
  unless ret.exitCode == 0 do
    throw (IO.userError "chmod failed")
  try
    expectError (do let _ ← mmapReadAscii path; pure ()) "open"
  finally
    -- Restore permissions for cleanup
    let _ ← IO.Process.output { cmd := "chmod", args := #["644", path] }

/-- Test: non-ASCII byte just past a 64KB buffer boundary.
    The streaming loop reads in 64KB chunks, so byte 65536 starts a new chunk. -/
def testNonAsciiBufBoundary : IO Unit := do
  -- 65536 valid bytes then one bad byte
  let good := ByteArray.mk (.replicate 65536 0x41)
  let bad := ByteArray.mk #[0x80]
  let path ← writeTempFile "buf_boundary.bin" (good ++ bad)
  expectError (do let _ ← mmapReadAscii path; pure ()) "non-ASCII"

/-- Test: file with all byte values 0-127 (every valid ASCII byte). -/
def testAllAsciiBytes : IO Unit := do
  let bytes := ByteArray.mk (Array.ofFn (fun (i : Fin 128) => i.val.toUInt8))
  let path ← writeTempFile "all_ascii.bin" bytes
  let s ← mmapReadAscii path
  unless s.utf8ByteSize == 128 do
    throw (IO.userError s!"expected 128 bytes, got {s.utf8ByteSize}")

/-! **Main** -/

def main : IO UInt32 := do
  IO.println "Testing mmapReadAscii..."
  let mut passed := 0
  let mut failed := 0
  let tests : List (String × IO Unit) := [
    -- Happy path
    ("match readFile (16/rot)",     testMatchesReadFile "data/16/rot_map.b85"),
    ("match readFile (16/cert)",    testMatchesReadFile "data/16/cert_z.b85"),
    ("match readFile (1728/rot)",   testMatchesReadFile "data/1728/rot_map.b85"),
    ("match readFile (1728/cert)",  testMatchesReadFile "data/1728/cert_z.b85"),
    ("utf8ByteSize",                testUtf8ByteSize),
    ("byte access (strGet!)",       testByteAccess),
    ("base85 decode",               testBase85Decode),
    ("page-aligned size",           testPageAligned),
    ("one byte file",               testOneByte),
    ("string equality",             testEquality),
    ("all ASCII bytes 0-127",       testAllAsciiBytes),
    -- Error conditions
    ("file not found",              testFileNotFound),
    ("is a directory",              testIsDirectory),
    ("empty file",                  testEmptyFile),
    ("non-ASCII at start",          testNonAsciiStart),
    ("non-ASCII in middle",         testNonAsciiMiddle),
    ("non-ASCII at end",            testNonAsciiEnd),
    ("non-ASCII at buf boundary",   testNonAsciiBufBoundary),
    ("permission denied",           testPermissionDenied)
  ]
  for (name, action) in tests do
    if ← runTest name action then
      passed := passed + 1
    else
      failed := failed + 1
  IO.println ""
  if failed == 0 then
    IO.println (green s!"All {passed} tests passed.")
    return 0
  else
    IO.println (red s!"{failed} of {passed + failed} tests failed.")
    return 1

end
