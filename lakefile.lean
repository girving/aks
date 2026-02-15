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

