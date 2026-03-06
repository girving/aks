/-
  # Separator Axiom Checks

  Compile-time assertions that the separator infrastructure is sorry-free.
  Not a `module` file because `#print axioms` is forbidden inside `module`.
-/

import AKS.Separator.SepProof

/-- info: 'separators' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms separators
