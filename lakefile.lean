import Lake
open Lake DSL

package «aks» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`linter.style.multiGoal, true⟩
  ]

require "leanprover-community" / "mathlib" @ git "v4.27.0"

@[default_target]
lean_lib «AKS» where
