import Lake
open Lake DSL

package «aks» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`weak.linter.style.multiGoal, true⟩
  ]

require "leanprover-community" / "mathlib" @ git "v4.27.0"

lean_lib «CertChecker» where
  precompileModules := true

@[default_target]
lean_lib «AKS» where
  moreLeanArgs := #[s!"--load-dynlib=.lake/build/lib/libaks_CertChecker.so"]

lean_exe «cert-bench» where
  root := `AKS.CertificateBench

lean_exe «cert-test» where
  root := `AKS.CertificateTest

lean_exe «cert-profile» where
  root := `AKS.CertificateProfile

/-- Generate certificate data for all graph sizes.
    Usage: `lake run gen-cert` -/
script «gen-cert» _args do
  let sizes : List (Nat × Nat) := [(16, 4), (1728, 12)]
  for (n, d) in sizes do
    let dir := s!"data/{n}"
    let certFile := s!"{dir}/cert_z.bin"
    if ← System.FilePath.pathExists certFile then
      IO.println s!"data/{n}/ already exists, skipping"
      continue
    IO.println s!"Generating certificate data for n={n}, d={d}..."
    let output ← IO.Process.output {
      cmd := "cargo"
      args := #["run", "--release",
                "--manifest-path", "rust/compute-certificate/Cargo.toml",
                "--", s!"{n}", s!"{d}", "42", "30", dir]
    }
    if output.exitCode != 0 then
      IO.eprintln output.stderr
      IO.eprintln output.stdout
      IO.eprintln s!"Failed to generate data for n={n} (exit code {output.exitCode})"
      return 1
  return 0
