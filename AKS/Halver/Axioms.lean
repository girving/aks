/-
  # Halver Axiom Checks

  Compile-time assertions that the halver infrastructure is sorry-free.
  Not a `module` file because `#print axioms` is forbidden inside `module`.
-/

import AKS.Halver.General

/-- info: 'halvers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms halvers
