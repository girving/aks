/-
  # Bridge: `checkCertificateFast = checkCertificateSlow`

  Proves that the parallel certificate checker produces the same result as the
  sequential one. The proof is structural (not `native_decide`), so
  `native_decide` only runs the fast version at ~0.5s for n=1728, and the
  bridge provides `checkCertificateSlow ... = true` at zero runtime cost.

  **Key facts used:**
  1. `Task` is transparent in Lean 4: `Task.spawn fn = ⟨fn ()⟩`, so
     `(Task.spawn f).get = f ()` is definitional
  2. Both `checkPSDCertificate` and `checkPSDCertificatePar` use identical
     structure: `columnLists.map (fun cols => checkPSDColumns ...)` vs
     `(columnLists.map (fun cols => Task.spawn ... checkPSDColumns ...)).map Task.get`
  3. `Array.map_map` + Task transparency closes the gap
-/
import CertCheck

/-! **Task transparency** -/

/-- `Task.spawn fn prio := ⟨fn ()⟩` and `Task.get := Task.1`, so
    `(Task.spawn f prio).get = f ()` is definitional in the kernel. -/
private theorem task_spawn_get {α : Type} (f : Unit → α) (prio : Task.Priority) :
    (Task.spawn f prio).get = f () := rfl

/-! **Bridge theorem** -/

/-- The parallel PSD check equals the sequential PSD check.

    Both use the same structure:
    - Same guards (`certBytes.size` check, `allDiagPositive`)
    - Same `buildColumnLists n 64`
    - Same `checkPSDColumns` per chunk
    - Same `checkPSDThreshold` on merged results

    The only difference: `checkPSDCertificatePar` wraps each chunk in
    `Task.spawn` and collects with `.map Task.get`. Since `Task` is
    transparent (`Task.spawn fn = ⟨fn ()⟩`), this is a no-op to the kernel. -/
theorem checkPSDCertificatePar_eq (rotBytes certBytes : ByteArray)
    (n d : Nat) (c₁ c₂ c₃ : Int) :
    checkPSDCertificatePar rotBytes certBytes n d c₁ c₂ c₃ =
    checkPSDCertificate rotBytes certBytes n d c₁ c₂ c₃ := by
  unfold checkPSDCertificatePar checkPSDCertificate
  -- Both sides share guards and structure. The only difference is Task.spawn
  -- wrapping. Fuse the two maps and reduce Task.spawn/Task.get:
  simp only [Array.map_map, Function.comp_def, task_spawn_get]

/-- Top-level bridge: `checkCertificateFast = checkCertificateSlow`. -/
theorem checkCertificateFast_eq_slow :
    @checkCertificateFast = @checkCertificateSlow := by
  funext rotStr certStr n d c₁ c₂ c₃
  simp only [checkCertificateFast, checkCertificateSlow]
  congr 1
  congr 1
  exact checkPSDCertificatePar_eq _ _ _ _ _ _ _
