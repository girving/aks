/-
  # Bridge: `checkCertificateFast = checkCertificateSlow`

  Proves that the merged parallel certificate checker produces the same result
  as the sequential one. The proof is structural (not `native_decide`), so
  `native_decide` only runs the fast version at ~0.3s for n=1728, and the
  bridge provides `checkCertificateSlow ... = true` at zero runtime cost.

  **Key facts used:**
  1. `Task` is transparent in Lean 4: `Task.spawn fn = ⟨fn ()⟩`, so
     `(Task.spawn f).get = f ()` is definitional
  2. `Array.map_map` + Task transparency eliminates `Task.spawn`/`Task.get`
  3. The merged fast check computes PSD columns once and shares the result
     for both the Gershgorin threshold and column-norm bound; the slow check
     computes them independently in `checkPSDCertificate` and `checkColumnNormBound`
  4. Boolean case analysis on shared conditions (size, `allDiagPositive`,
     `merged.first`) proves equivalence
-/
import CertCheck

/-! **Task transparency** -/

/-- Spawning tasks and immediately collecting results is the identity.
    Uses `Array.map_map` to fuse the two maps, then Task transparency
    (`Task.spawn fn = ⟨fn ()⟩`) for definitional reduction. -/
private theorem map_task_spawn_get {α β : Type} (f : α → β) (arr : Array α)
    (prio : Task.Priority) :
    (arr.map (fun x => Task.spawn (prio := prio) fun () => f x)).map Task.get = arr.map f := by
  rw [Array.map_map]; congr 1

/-! **Bridge theorem** -/

set_option maxHeartbeats 400000 in
/-- Top-level bridge: `checkCertificateFast = checkCertificateSlow`.

    The fast version merges PSD + column-norm into a single pass with
    `Task.spawn` parallelism. After eliminating Task.spawn via
    `map_task_spawn_get`, both sides share the same `foldl`/`merge`
    computation. Case analysis on `checkInvolution`, size guard,
    `allDiagPositive`, and `merged.first` closes the Boolean algebra. -/
theorem checkCertificateFast_eq_slow :
    @checkCertificateFast = @checkCertificateSlow := by
  funext rotStr certStr n d c₁ c₂ c₃
  simp only [checkCertificateFast, checkCertificateSlow,
    map_task_spawn_get,
    checkPSDCertificate, checkPSDThreshold, checkColumnNormBound]
  cases checkInvolution (String.toUTF8 rotStr) n d <;> simp only [Bool.false_and, Bool.true_and]
  split
  · simp
  · cases allDiagPositive (String.toUTF8 certStr) n <;> simp only [Bool.false_and, Bool.true_and]
    generalize (Array.foldl PSDChunkResult.merge { epsMax := 0, minDiag := 0, first := true }
        (Array.map
          (fun cols => checkPSDColumns (decodeNeighbors (String.toUTF8 rotStr) n d)
            (String.toUTF8 certStr) n d c₁ c₂ c₃ cols)
          (buildColumnLists n 64))) = merged
    obtain ⟨epsMax, minDiag, first⟩ := merged
    cases first <;> simp
