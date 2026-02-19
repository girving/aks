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
  3. `fused_map_fst_eq`: mapping `.1` over fused results = unfused `checkPSDColumns`
  4. `prefixSumLoop_eq_checkPerRow`: inline prefix-sum loop = `checkPerRow`
  5. `fused_norm_lookup`: fused norm array entries = `zColNormPure`
  6. Boolean case splits fuse `checkPSDCertificate && checkColumnNormBound`
-/
import AKS.Cert.FusedBridge

/-! **Task transparency** -/

/-- Spawning tasks and immediately collecting results is the identity.
    Uses `Array.map_map` to fuse the two maps, then Task transparency
    (`Task.spawn fn = ⟨fn ()⟩`) for definitional reduction. -/
private theorem map_task_spawn_get {α β : Type} (f : α → β) (arr : Array α)
    (prio : Task.Priority) :
    (arr.map (fun x => Task.spawn (prio := prio) fun () => f x)).map Task.get = arr.map f := by
  rw [Array.map_map]; congr 1

/-! **Bridge theorem** -/

set_option maxHeartbeats 6400000 in
/-- Top-level bridge: `checkCertificateFast = checkCertificateSlow`.

    The fast version fuses PSD + column-norm computation into parallel tasks
    via `checkPSDColumnsFull`, then does an inline prefix-sum check using
    precomputed norms. The slow version runs `checkPSDCertificate` and
    `checkColumnNormBound` separately.

    **Proof strategy:** Unfold both sides, eliminate `Task.spawn`/`Task.get`,
    rewrite fused→unfused PSD results via `fused_map_fst_eq`, then case-split
    on each Boolean guard (`checkInvolution`, size check, `allDiagPositive`,
    `merged.first`). All but one case are trivially `false = false`. The
    non-trivial case reduces to `prefixSumLoop = checkPerRow` via
    `prefixSumLoop_eq_checkPerRow` with norms from `fused_norm_lookup`. -/
theorem checkCertificateFast_eq_slow :
    @checkCertificateFast = @checkCertificateSlow := by
  funext rotStr certStr n d c₁ c₂ c₃
  simp only [checkCertificateFast, checkCertificateSlow,
    map_task_spawn_get,
    checkPSDCertificate, checkColumnNormBound, checkPSDThreshold,
    fused_map_fst_eq, String.toUTF8]
  -- Case split on checkInvolution
  cases checkInvolution rotStr.toByteArray n d
  · simp
  · simp only [Bool.true_and]
    -- Case split on size check
    cases (certStr.toByteArray.size != n * (n + 1) / 2 * 5 : Bool)
    · -- Size OK: if (false = true) → else branch
      simp only [Bool.false_eq_true, ite_false]
      cases allDiagPositive certStr.toByteArray n
      · simp
      · simp only [Bool.true_and]
        -- Name the shared merged computation
        set merged := Array.foldl PSDChunkResult.merge { epsMax := 0, minDiag := 0, first := true }
          (Array.map
            (fun cols =>
              checkPSDColumns (decodeNeighbors rotStr.toByteArray n d)
                certStr.toByteArray n d c₁ c₂ c₃ cols)
            (buildColumnLists n 64))
        cases merged.first
        · -- merged.first = false: non-trivial case
          simp only [Bool.false_eq_true, ite_false]
          -- Goal: decide(threshold) && prefixSumLoop = decide(threshold) && checkPerRow
          congr 1
          -- Goal: prefixSumLoop using fused norms = checkPerRow
          exact prefixSumLoop_eq_checkPerRow certStr.toByteArray n merged.epsMax
            (merged.minDiag + merged.epsMax)
            (fun i => (Array.map
              (checkPSDColumnsFull (decodeNeighbors rotStr.toByteArray n d)
                certStr.toByteArray n d c₁ c₂ c₃)
              (buildColumnLists n 64))[i % 64]!.snd[i / 64]!)
            (fun i hi => fused_norm_lookup (decodeNeighbors rotStr.toByteArray n d)
              certStr.toByteArray n d c₁ c₂ c₃ i hi)
        · -- merged.first = true: both sides false
          simp
    · -- Size bad: both sides false
      simp
