/-
  # MGG Axiom Checks

  Compile-time assertions that the MGG spectral gap proof is sorry-free
  and does not use native_decide.
  Not a `module` file because `#print axioms` is forbidden inside `module`.
-/

import AKS.MGG.Spectral

/--
info: 'spectralGap_mgg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms spectralGap_mgg
