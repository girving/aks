import Lake
open Lake DSL

package «aks» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`weak.linter.style.multiGoal, true⟩
  ]

require "leanprover-community" / "mathlib" @ git "v4.27.0"

lean_lib «CertCheck» where
  precompileModules := true

@[default_target]
lean_lib «AKS» where

lean_lib «Bench» where

lean_exe «cert-bench» where
  root := `Bench.CertBench

lean_exe «cert-test» where
  root := `Bench.CertTest

lean_exe «cert-profile» where
  root := `Bench.CertProfile

/-- Generate certificate data for all graph sizes.
    Usage: `lake run gen-cert` -/
script «gen-cert» _args do
  let sizes : List (Nat × Nat) := [(16, 4), (1728, 12)]
  for (n, d) in sizes do
    let dir := s!"data/{n}"
    let certFile := s!"{dir}/cert_z.b85"
    if ← System.FilePath.pathExists certFile then
      IO.println s!"data/{n}/ already exists, skipping"
      continue
    IO.println s!"Generating certificate data for n={n}, d={d}..."
    let output ← IO.Process.output {
      cmd := "cargo"
      args := #["+nightly", "-Zscript",
                "rust/certificate.rs",
                s!"{n}", s!"{d}", "42", "30", dir]
    }
    if output.exitCode != 0 then
      IO.eprintln output.stderr
      IO.eprintln output.stdout
      IO.eprintln s!"Failed to generate data for n={n} (exit code {output.exitCode})"
      return 1
  return 0
