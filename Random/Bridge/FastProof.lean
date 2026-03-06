module
/-
  # Bridge: `checkCertificateWith = checkCertificateSlowWith`

  Proves that the merged parallel certificate checker produces the same result
  as the sequential one, for any entry function. The proof is structural
  (not `native_decide`), so `native_decide` only runs the fast version at
  ~0.3s for n=1728, and the bridge provides `checkCertificateSlowWith ... = true`
  at zero runtime cost.

  **Key facts used:**
  1. `Task` is transparent in Lean 4: `Task.spawn fn = ⟨fn ()⟩`, so
     `(Task.spawn f).get = f ()` is definitional
  2. `Array.map_map` + Task transparency eliminates `Task.spawn`/`Task.get`
  3. `fused_map_fst_eq`: mapping `.1` over fused results = unfused `checkPSDColumns`
  4. `prefixSumLoop_eq_checkPerRow`: inline prefix-sum loop = `checkPerRow`
  5. `flattenNorms_eq_zColNormPure`: fused norm array entries = `zColNormPure`
  6. Boolean case splits fuse `checkPSDCertificate && checkColumnNormBound`
-/
public import Random.Bridge.FusedBridge

@[expose] public section


/-! **Task transparency** -/

/-- Spawning tasks and immediately collecting results is the identity.
    Uses `Array.map_map` to fuse the two maps, then Task transparency
    (`Task.spawn fn = ⟨fn ()⟩`) for definitional reduction. -/
private theorem map_task_spawn_get {α β : Type} (f : α → β) (arr : Array α)
    (prio : Task.Priority) :
    (arr.map (fun x => Task.spawn (prio := prio) fun () => f x)).map Task.get = arr.map f := by
  rw [Array.map_map]; congr 1

/-! **Generic bridge theorem** -/

set_option maxHeartbeats 6400000 in
/-- Generic bridge: `checkCertificateWith = checkCertificateSlowWith` for any entry function.

    The fast version fuses PSD + column-norm computation into parallel tasks
    via `checkPSDColumnsFull`, then does an inline prefix-sum check using
    precomputed norms from `flattenNorms`. The slow version runs
    `checkPSDCertificate` and `checkColumnNormBound` separately.

    **Proof strategy:** Unfold both sides, eliminate `Task.spawn`/`Task.get`,
    rewrite fused→unfused PSD results via `fused_map_fst_eq`, then case-split
    on each Boolean guard (`checkInvolution`, `allDiagPositive`,
    `merged.first`). All but one case are trivially `false = false`. The
    non-trivial case reduces to `prefixSumLoop = checkPerRow` via
    `prefixSumLoop_eq_checkPerRow` with norms from
    `flattenNorms_eq_zColNormPure` + `roundRobinPartition_valid`. -/
theorem checkCertificateWith_eq_slow (tasks : Nat := 64) (ht : 0 < tasks := by omega) :
    ∀ rotStr (entry : Nat → Nat → Int) n d c₁ c₂ c₃,
    checkCertificateWith rotStr entry n d c₁ c₂ c₃
      (partition := roundRobinPartition n tasks) =
    checkCertificateSlowWith rotStr entry n d c₁ c₂ c₃ (tasks := tasks) := by
  intro rotStr entry n d c₁ c₂ c₃
  simp only [checkCertificateWith, checkCertificateSlowWith,
    map_task_spawn_get,
    checkPSDCertificate, checkColumnNormBound, checkPSDThreshold]
  -- Case split on checkInvolution (must come first to derive NeighborSymm)
  cases hinv : checkInvolution rotStr n d
  · simp
  · -- checkInvolution = true → derive NeighborSymm for scatter = gather bridge
    have hsym := checkInvolution_implies_neighborSymm rotStr n d hinv
    simp only [Bool.true_and,
      fused_map_fst_eq _ _ _ _ _ _ _ (roundRobinPartition n tasks) hsym]
    cases allDiagPositive entry n
    · simp
    · simp only [Bool.true_and]
      -- Name the shared merged computation
      set merged := Array.foldl PSDChunkResult.merge { epsMax := 0, minDiag := 0, first := true }
        (Array.map
          (fun cols =>
            checkPSDColumns (decodeNeighbors rotStr n d)
              entry n d c₁ c₂ c₃ cols)
          (roundRobinPartition n tasks))
      cases merged.first
      · -- merged.first = false: non-trivial case
        simp only [Bool.false_eq_true, ite_false]
        -- Goal: decide(threshold) && prefixSumLoop = decide(threshold) && checkPerRow
        congr 1
        -- Goal: prefixSumLoop using flattenNorms = checkPerRow
        exact prefixSumLoop_eq_checkPerRow entry n merged.epsMax
          (merged.minDiag + merged.epsMax)
          (fun i => (flattenNorms (roundRobinPartition n tasks)
            ((roundRobinPartition n tasks).map fun cols =>
              checkPSDColumnsFull (decodeNeighbors rotStr n d)
                n d c₁ c₂ c₃ cols entry))[i]!)
          (fun i hi => flattenNorms_eq_zColNormPure
            (decodeNeighbors rotStr n d) entry d c₁ c₂ c₃
            (roundRobinPartition n tasks) (roundRobinPartition_valid n tasks ht)
            hsym i hi)
      · -- merged.first = true: both sides false
        simp

/-! **Specialized corollaries** -/

/-- `checkCertificate = checkCertificateSlow` (base-85 specialization). -/
theorem checkCertificate_eq_slow (tasks : Nat := 64) (ht : 0 < tasks := by omega) :
    ∀ rotStr certStr n d c₁ c₂ c₃,
    checkCertificate rotStr certStr n d c₁ c₂ c₃
      (partition := roundRobinPartition n tasks) =
    checkCertificateSlow rotStr certStr n d c₁ c₂ c₃ (tasks := tasks) := by
  intro rotStr certStr n d c₁ c₂ c₃
  exact checkCertificateWith_eq_slow tasks ht rotStr (b85entry certStr) n d c₁ c₂ c₃

/-- `checkCertificateB128 = checkCertificateSlowWith` (base-128 specialization). -/
theorem checkCertificateB128_eq_slow (tasks : Nat := 64) (ht : 0 < tasks := by omega) :
    ∀ rotStr certStr n d c₁ c₂ c₃ scale,
    checkCertificateB128 rotStr certStr n d c₁ c₂ c₃ scale
      (partition := roundRobinPartition n tasks) =
    checkCertificateSlowWith rotStr (b128entry scale certStr) n d c₁ c₂ c₃
      (tasks := tasks) := by
  intro rotStr certStr n d c₁ c₂ c₃ scale
  exact checkCertificateWith_eq_slow tasks ht rotStr (b128entry scale certStr) n d c₁ c₂ c₃

/-- `checkCertificateB128x5 = checkCertificateSlowWith` (5-byte base-128 specialization). -/
theorem checkCertificateB128x5_eq_slow (tasks : Nat := 64) (ht : 0 < tasks := by omega) :
    ∀ rotStr certStr n d c₁ c₂ c₃ scale,
    checkCertificateB128x5 rotStr certStr n d c₁ c₂ c₃ scale
      (partition := roundRobinPartition n tasks) =
    checkCertificateSlowWith rotStr (b128x5entry scale certStr) n d c₁ c₂ c₃
      (tasks := tasks) := by
  intro rotStr certStr n d c₁ c₂ c₃ scale
  exact checkCertificateWith_eq_slow tasks ht rotStr (b128x5entry scale certStr) n d c₁ c₂ c₃

end
