/-
  # Binary Data File Readers

  Pure Lean code to read binary data files into `Array Int`, plus a
  term elaborator `bin_array%` that loads data at elaboration time
  so the kernel sees the full array.

  Supports:
  - Raw binary i32 little-endian (`.bin` files from `compute-certificate`)
  - NumPy int64 little-endian (`.npy` files)
-/

import Lean


/-! **Raw binary i32 reader** -/

/-- Read a little-endian Int32 from 4 bytes in a ByteArray starting at offset. -/
def readInt32LE (data : ByteArray) (off : Nat) : Int :=
  let b0 := (data.get! off).toUInt32
  let b1 := (data.get! (off + 1)).toUInt32
  let b2 := (data.get! (off + 2)).toUInt32
  let b3 := (data.get! (off + 3)).toUInt32
  let u : UInt32 := b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
  -- Convert unsigned to signed: if high bit set, subtract 2^32
  if u.toNat < 2^31 then
    (u.toNat : Int)
  else
    (u.toNat : Int) - (2^32 : Int)

/-- Read a raw binary file of little-endian i32 values into `Array ℤ`. -/
def readBinI32File (path : System.FilePath) : IO (Array Int) := do
  let bytes ← IO.FS.readBinFile path
  let numEntries := bytes.size / 4
  let mut arr := Array.mkEmpty numEntries
  for i in [:numEntries] do
    arr := arr.push (readInt32LE bytes (4 * i))
  return arr


/-! **Elaboration-time binary loading** -/

-- Term elaborator that reads a binary i32 file and produces an `Array ℤ` value.
-- The kernel sees the full array data (no `@[implemented_by]` tricks).
-- Usage: `def myData : Array ℤ := bin_array% "path/to/file.bin"`
open Lean in open Elab.Term in
elab "bin_array% " path:str : term => do
  let pathStr := path.getString
  let arr ← (readBinI32File ⟨pathStr⟩ : IO (Array Int))
  return toExpr arr

-- Term elaborator that reads a binary i32 file and produces a base-85 encoded
-- `String`. Each i32 (as unsigned u32) is encoded as 5 ASCII chars (codepoints
-- 33–117). The kernel sees a single string literal — compact even for millions
-- of entries. Use `decodeBase85Entry` in `Certificate.lean` to decode.
-- Usage: `def myData : String := bin_base85% "path/to/file.bin"`
open Lean in open Elab.Term in
elab "bin_base85% " path:str : term => do
  let bytes ← IO.FS.readBinFile ⟨path.getString⟩
  let numEntries := bytes.size / 4
  let mut result : ByteArray := .empty
  for i in [:numEntries] do
    let off := 4 * i
    let b0 := (bytes.get! off).toNat
    let b1 := (bytes.get! (off + 1)).toNat
    let b2 := (bytes.get! (off + 2)).toNat
    let b3 := (bytes.get! (off + 3)).toNat
    let u := b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
    let mut v := u
    for _ in [:5] do
      result := result.push (UInt8.ofNat (v % 85 + 33))
      v := v / 85
  return Lean.mkStrLit (String.fromUTF8! result)


/-! **Byte-level parsing helpers** -/

/-- Read a little-endian UInt16 from two bytes. -/
def readUInt16LE (b0 b1 : UInt8) : UInt16 :=
  b0.toUInt16 ||| (b1.toUInt16 <<< 8)

/-- Read a little-endian Int64 from 8 bytes in a ByteArray starting at offset. -/
def readInt64LE (data : ByteArray) (off : Nat) : Int :=
  let b0 := (data.get! (off + 0)).toUInt64
  let b1 := (data.get! (off + 1)).toUInt64
  let b2 := (data.get! (off + 2)).toUInt64
  let b3 := (data.get! (off + 3)).toUInt64
  let b4 := (data.get! (off + 4)).toUInt64
  let b5 := (data.get! (off + 5)).toUInt64
  let b6 := (data.get! (off + 6)).toUInt64
  let b7 := (data.get! (off + 7)).toUInt64
  let u : UInt64 := b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) |||
                    (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)
  -- Convert unsigned to signed: if high bit set, subtract 2^64
  if u.toNat < 2^63 then
    (u.toNat : Int)
  else
    (u.toNat : Int) - (2^64 : Int)


/-! **Npy file reading** -/

/-- Read an int64 .npy file, returning (shape, data).
    Only supports: little-endian int64 (`<i8`), C-contiguous, no pickle. -/
def readNpyInt64 (path : System.FilePath) : IO (List Nat × Array Int) := do
  let bytes ← IO.FS.readBinFile path

  -- Check magic: \x93NUMPY
  if bytes.size < 10 then
    throw (IO.userError s!"npy file too small: {bytes.size} bytes")
  if bytes.get! 0 != 0x93 || bytes.get! 1 != 0x4E || bytes.get! 2 != 0x55 ||
     bytes.get! 3 != 0x4D || bytes.get! 4 != 0x50 || bytes.get! 5 != 0x59 then
    throw (IO.userError "not a .npy file (bad magic)")

  -- Version
  let _major := bytes.get! 6
  let _minor := bytes.get! 7

  -- Header length (version 1.0: 2 bytes LE; version 2.0: 4 bytes LE)
  let headerLen : Nat :=
    if _major == 1 then
      (readUInt16LE (bytes.get! 8) (bytes.get! 9)).toNat
    else
      -- Version 2.0+: 4-byte header length
      let b0 := (bytes.get! 8).toUInt32
      let b1 := (bytes.get! 9).toUInt32
      let b2 := (bytes.get! 10).toUInt32
      let b3 := (bytes.get! 11).toUInt32
      (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)).toNat

  let headerStart : Nat := if _major == 1 then 10 else 12
  let dataStart := headerStart + headerLen

  -- Parse header string (Python dict literal)
  let headerBytes := bytes.extract headerStart dataStart
  let headerStr := String.fromUTF8! headerBytes

  -- Verify dtype contains 'i8' (int64)
  let hasI8 := (headerStr.splitOn "i8").length > 1
  unless hasI8 do
    throw (IO.userError s!"expected int64 dtype, got header: {headerStr}")

  -- Parse shape from header: look for 'shape': (N,) or (N, M)
  -- Simple parsing: find content between '(' and ')'
  let afterParen := (headerStr.splitOn "(").getD 1 ""
  let shapeStr := (afterParen.splitOn ")").getD 0 ""

  -- Parse comma-separated integers
  let parts := (shapeStr.splitOn ",").map (·.trimAscii.toString) |>.filter (· != "")
  let shape := parts.filterMap (·.toNat?)

  -- Compute total elements
  let totalElems := shape.foldl (· * ·) 1

  -- Read data
  let expectedBytes := totalElems * 8
  if bytes.size < dataStart + expectedBytes then
    throw (IO.userError s!"npy file truncated: need {dataStart + expectedBytes} bytes, have {bytes.size}")

  let mut result := Array.mkEmpty totalElems
  for i in [:totalElems] do
    result := result.push (readInt64LE bytes (dataStart + i * 8))

  return (shape, result)

/-- Read a flat int64 .npy file, returning just the array. -/
def readNpyInt64Flat (path : System.FilePath) : IO (Array Int) := do
  let (_, data) ← readNpyInt64 path
  return data


/-! **Certificate data auto-generation** -/

/-- Ensure certificate data files exist for a given graph size.
    If `data/{n}/cert_z.bin` is missing, runs the Rust `compute-certificate` tool
    to generate them. This is called via `#eval` before `bin_base85%` macros so
    that data files are present at elaboration time. -/
def ensureCertificateData (n d : Nat) (seed : Nat := 42) (scaleExp : Nat := 30) : IO Unit := do
  let dir : System.FilePath := s!"data/{n}"
  let certFile : System.FilePath := dir / "cert_z.bin"
  if ← certFile.pathExists then return
  IO.eprintln s!"Certificate data missing for n={n}, generating..."
  -- Ensure output directory exists
  IO.FS.createDirAll dir
  let output ← IO.Process.output {
    cmd := "cargo"
    args := #["run", "--release",
              "--manifest-path", "rust/compute-certificate/Cargo.toml",
              "--", s!"{n}", s!"{d}", s!"{seed}", s!"{scaleExp}", dir.toString]
  }
  if output.exitCode != 0 then
    IO.eprintln output.stderr
    IO.eprintln output.stdout
    throw (IO.userError s!"compute-certificate failed for n={n} (exit code {output.exitCode})")
  -- Verify the file was actually created
  unless ← certFile.pathExists do
    throw (IO.userError s!"compute-certificate ran but {certFile} was not created")
