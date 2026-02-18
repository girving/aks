/-
  # Certificate Data Reading

  `bin_base85%` elaborator for embedding binary i32 data as base-85 encoded
  `String` literals, plus `ensureCertificateData` for auto-generating data files.
-/

import Lean


/-! **Base-85 binary encoding** -/

-- Term elaborator that reads a binary i32 file and produces a base-85 encoded
-- `String`. Each i32 (as unsigned u32) is encoded as 5 ASCII chars (codepoints
-- 33–117). The kernel sees a single string literal — compact even for millions
-- of entries. Use `decodeBase85Entry` in `CertCheck.lean` to decode.
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


/-! **Certificate data auto-generation** -/

/-- Ensure certificate data files exist for a given graph size.
    If `data/{n}/cert_z.bin` is missing, runs `rust/certificate.rs`
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
    args := #["+nightly", "-Zscript",
              "rust/certificate.rs",
              s!"{n}", s!"{d}", s!"{seed}", s!"{scaleExp}", dir.toString]
  }
  if output.exitCode != 0 then
    IO.eprintln output.stderr
    IO.eprintln output.stdout
    throw (IO.userError s!"rust/certificate.rs failed for n={n} (exit code {output.exitCode})")
  -- Verify the file was actually created
  unless ← certFile.pathExists do
    throw (IO.userError s!"rust/certificate.rs ran but {certFile} was not created")
