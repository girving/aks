/-
  # Axiom checks for Random data modules

  Non-module file hosting `#guard_msgs in #print axioms` checks.
  These can't go in the data modules themselves because `#print axioms`
  is forbidden inside `module` files.
-/

import Random.Concrete.Random16
import Random.Concrete.Random1728
import Random.Concrete.Random20736
import Random.Concrete.Random65536

/-- info: 'Random16.gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Random16.certificate_passes._native.native_decide.ax_1_1✝,
 Random16.involution_check._native.native_decide.ax_1_1✝] -/
#guard_msgs in #print axioms Random16.gap

/-- info: 'Random1728.gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Random1728.certificate_passes._native.native_decide.ax_1_1✝,
 Random1728.involution_check._native.native_decide.ax_1_1✝] -/
#guard_msgs in #print axioms Random1728.gap

/-- info: 'Random20736.gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Random20736.certificate_passes._native.native_decide.ax_1_1✝,
 Random20736.involution_check._native.native_decide.ax_1_1✝] -/
#guard_msgs in #print axioms Random20736.gap

/-- info: 'Random65536.gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Random65536.certificate_passes._native.native_decide.ax_1_1✝,
 Random65536.involution_check._native.native_decide.ax_1_1✝] -/
#guard_msgs in #print axioms Random65536.gap

