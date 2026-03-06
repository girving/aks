import Lake
open Lake DSL

package «aks» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`weak.linter.style.multiGoal, true⟩
  ]

require "leanprover-community" / "mathlib" @ git "master"

@[default_target]
lean_lib «RandomCert» where
  roots := #[`Random.Cert]
  precompileModules := true

@[default_target]
lean_lib «RandomBridge» where
  globs := #[.submodules `Random.Bridge]

@[default_target]
lean_lib «RandomConcrete» where
  globs := #[.submodules `Random.Concrete]

@[default_target]
lean_lib «RandomMisc» where
  globs := #[.submodules `Random.Misc]

lean_lib «RandomBench» where
  globs := #[.submodules `Random.Bench]

extern_lib «mmap» pkg := do
  let srcJob ← inputBinFile (pkg.dir / "Random" / "Cert" / "mmap_string.c")
  let oJob ← buildO (pkg.buildDir / "Random" / "Cert" / "mmap_string.o") srcJob
    (weakArgs := #["-I", (← getLeanIncludeDir).toString, "-fPIC"])
  buildStaticLib (pkg.buildDir / "lib" / nameToStaticLib "mmap") #[oJob]

@[default_target]
lean_lib «AKS» where

lean_exe «cert-bench» where
  root := `Random.Bench.CertBench

lean_exe «cert-test» where
  root := `Random.Bench.CertTest

lean_exe «cert-profile» where
  root := `Random.Bench.CertProfile

lean_exe «test-mmap» where
  root := `Random.Bench.TestMmap

lean_exe «bench-decomp» where
  root := `Random.Bench.BenchDecomp
