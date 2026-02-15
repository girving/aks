/-
  # Certificate Bridge Theorem

  Connects the decidable `checkCertificate` predicate to the spectral gap
  bound on `RegularGraph`. Decomposed into three layers:

  **Layer 1** (`SpectralMatrix.lean`): M PSD → walk bound (provable)
  **Layer 2** (`DiagDominant.lean`): K diag-dominant + Z invertible → M PSD (provable)
  **Layer 3** (this file): `checkCertificate = true` → spectral matrix PSD

  The bridge then chains:
  1. `checker_implies_spectralMatrix_psd` (Layer 3): certificate → M PSD
  2. `spectralMatrix_posSemidef_implies_walk_bound` (Layer 1): M PSD → walk bound
  3. `spectralGap_le_of_walk_bound` (in `WalkBound.lean`): walk bound → spectral gap
  4. `sqrt_coeff_le_frac` (in `WalkBound.lean`): coefficient arithmetic

  Layer 3 is decomposed into a structural proof (congruence, invertibility,
  Hermiticity, PSD assembly — all proved) and one narrow sorry
  (`kRowDominant_implies_diagDominant`: connecting integer checker computation
  to the formal real matrix via `hmatch`).
-/

import AKS.Certificate
import AKS.WalkBound
import AKS.SpectralMatrix
import AKS.DiagDominant
import Mathlib.LinearAlgebra.Matrix.Block

open Matrix BigOperators Finset


/-! **Certificate matrix definition** -/

/-- The certificate matrix `Z`, decoded from base-85 encoded bytes.
    Upper triangular: `Z[i,j] = 0` for `i > j`.
    Column `j` has entries at byte positions `j*(j+1)/2 + k` for `k = 0..j`. -/
noncomputable def certMatrixReal (certBytes : ByteArray) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j ↦
    if i.val ≤ j.val then
      (decodeBase85Int certBytes (j.val * (j.val + 1) / 2 + i.val) : ℝ)
    else 0


/-! **Diagonal positivity extraction** -/

/-- `allDiagPositive certBytes n = true` implies each diagonal entry is positive (as `ℤ`). -/
private theorem allDiagPositive_spec (certBytes : ByteArray) (n : ℕ)
    (h : allDiagPositive certBytes n = true) (j : ℕ) (hj : j < n) :
    0 < decodeBase85Int certBytes (j * (j + 1) / 2 + j) := by
  induction n with
  | zero => omega
  | succ k ih =>
    simp only [allDiagPositive, Bool.and_eq_true] at h
    by_cases hjk : j < k
    · exact ih h.1 hjk
    · have : j = k := by omega
      subst this; exact of_decide_eq_true h.2

/-- The certificate matrix has positive diagonal entries when the PSD checker passes.
    Proved by extracting `allDiagPositive` from the checker. -/
theorem certMatrix_posdiag (n : ℕ) (certBytes rotBytes : ByteArray)
    (d : ℕ) (c₁ c₂ c₃ : ℤ)
    (hcert : checkPSDCertificate rotBytes certBytes n d c₁ c₂ c₃ = true) :
    ∀ j : Fin n, 0 < certMatrixReal certBytes n j j := by
  -- Extract allDiagPositive from checkPSDCertificate
  have h_diag : allDiagPositive certBytes n = true := by
    unfold checkPSDCertificate at hcert
    split at hcert
    · simp at hcert
    · simp only [Bool.and_eq_true] at hcert; exact hcert.1
  intro j
  -- Get integer positivity from allDiagPositive
  have hj_pos := allDiagPositive_spec certBytes n h_diag j.val j.isLt
  -- Simplify certMatrixReal on the diagonal
  simp only [certMatrixReal, of_apply, le_refl, ite_true]
  exact Int.cast_pos.mpr hj_pos

/-- Bridge lemma: if `checkKRowDominant` passes and the rotation map matches,
    then K = star Z * M * Z is strictly row-diag-dominant.

    The proof requires connecting the checker's integer computation to the
    formal real matrix:
    1. `mulAdj` correctly computes B·z via the rotation map (needs `hmatch`)
    2. The checker's P computation matches formal `spectralMatrix * Z`
    3. The checker's K computation matches formal `star Z * spectralMatrix * Z`
    4. Integer diagonal dominance implies real diagonal dominance -/
theorem kRowDominant_implies_diagDominant
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (G : RegularGraph n d)
    (rotStr certStr : String) (c₁ c₂ c₃ : ℤ)
    (hcert : checkCertificate rotStr certStr n d c₁ c₂ c₃ = true)
    (hmatch : ∀ vp : Fin n × Fin d,
      G.rot vp = (⟨decodeBase85Nat rotStr.toUTF8 (2 * (vp.1.val * d + vp.2.val)) % n,
                    Nat.mod_lt _ hn⟩,
                  ⟨decodeBase85Nat rotStr.toUTF8 (2 * (vp.1.val * d + vp.2.val) + 1) % d,
                    Nat.mod_lt _ hd⟩))
    (hkdom : checkKRowDominant rotStr.toUTF8 certStr.toUTF8 n d c₁ c₂ c₃ = true) :
    let Z := certMatrixReal certStr.toUTF8 n
    let M := spectralMatrix G (↑c₁) (↑c₂) (↑c₃)
    ∀ i : Fin n,
      ∑ j ∈ Finset.univ.erase i, ‖(star Z * M * Z) i j‖ <
      (star Z * M * Z) i i := by
  sorry

/-- `K = Z* · M · Z` is strictly row-diag-dominant when the certificate checker passes.

    Proved by extracting `checkKRowDominant = true` from `checkCertificate` and
    applying `kRowDominant_implies_diagDominant`. -/
theorem congruence_diagDominant
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (G : RegularGraph n d)
    (rotStr certStr : String) (c₁ c₂ c₃ : ℤ)
    (hcert : checkCertificate rotStr certStr n d c₁ c₂ c₃ = true)
    (hmatch : ∀ vp : Fin n × Fin d,
      G.rot vp = (⟨decodeBase85Nat rotStr.toUTF8 (2 * (vp.1.val * d + vp.2.val)) % n,
                    Nat.mod_lt _ hn⟩,
                  ⟨decodeBase85Nat rotStr.toUTF8 (2 * (vp.1.val * d + vp.2.val) + 1) % d,
                    Nat.mod_lt _ hd⟩)) :
    let Z := certMatrixReal certStr.toUTF8 n
    let M := spectralMatrix G (↑c₁) (↑c₂) (↑c₃)
    ∀ i : Fin n,
      ∑ j ∈ Finset.univ.erase i, ‖(star Z * M * Z) i j‖ <
      (star Z * M * Z) i i := by
  -- Extract K diagonal dominance check from checkCertificate
  have hkdom : checkKRowDominant rotStr.toUTF8 certStr.toUTF8 n d c₁ c₂ c₃ = true := by
    simp only [checkCertificate, Bool.and_eq_true] at hcert; exact hcert.2
  exact kRowDominant_implies_diagDominant n d hn hd G rotStr certStr c₁ c₂ c₃ hcert hmatch hkdom


/-! **Layer 3: Certificate → spectral matrix PSD** -/

/-- If `checkCertificate` passes and the rotation map matches `G.rot`,
    then the spectral matrix `c₁I - c₂B² + c₃J` is positive semidefinite.

    **Proof structure:**
    1. Define `Z` = certificate matrix (upper triangular, from base-85 bytes)
    2. `Z` upper triangular → `det Z = ∏ Z[i,i]` → positive → `IsUnit Z`
    3. `K = Z* · M · Z` is Hermitian (from `M` Hermitian)
    4. `K` is strictly row-diag-dominant (via `congruence_diagDominant`)
    5. `K` is PSD (from Hermitian + diag-dominant)
    6. `M` is PSD (from `K` PSD + `Z` invertible, via congruence) -/
theorem checker_implies_spectralMatrix_psd
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (G : RegularGraph n d)
    (rotStr certStr : String) (c₁ c₂ c₃ : ℤ)
    (hcert : checkCertificate rotStr certStr n d c₁ c₂ c₃ = true)
    (hmatch : ∀ vp : Fin n × Fin d,
      G.rot vp = (⟨decodeBase85Nat rotStr.toUTF8 (2 * (vp.1.val * d + vp.2.val)) % n,
                    Nat.mod_lt _ hn⟩,
                  ⟨decodeBase85Nat rotStr.toUTF8 (2 * (vp.1.val * d + vp.2.val) + 1) % d,
                    Nat.mod_lt _ hd⟩)) :
    Matrix.PosSemidef (spectralMatrix G (↑c₁) (↑c₂) (↑c₃)) := by
  -- Extract PSD check from combined check
  have hpsd : checkPSDCertificate rotStr.toUTF8 certStr.toUTF8 n d c₁ c₂ c₃ = true := by
    simp only [checkCertificate, Bool.and_eq_true] at hcert; exact hcert.1.2
  -- Define Z and M
  set Z := certMatrixReal certStr.toUTF8 n with hZ_def
  set M := spectralMatrix G (↑c₁ : ℝ) (↑c₂) (↑c₃) with hM_def
  -- Step 1: Z is upper triangular
  have hZ_tri : Z.BlockTriangular id := by
    intro i j (hij : j < i)
    show certMatrixReal certStr.toUTF8 n i j = 0
    simp only [certMatrixReal, of_apply]
    exact if_neg (by omega)
  -- Step 2: Z has positive diagonal (sorry'd)
  have hZ_pos : ∀ j : Fin n, 0 < Z j j :=
    certMatrix_posdiag n certStr.toUTF8 rotStr.toUTF8 d c₁ c₂ c₃ hpsd
  -- Step 3: Z is invertible (det = ∏ diag > 0 → IsUnit)
  have hZ_det : Z.det = ∏ i : Fin n, Z i i := det_of_upperTriangular hZ_tri
  have hZ_det_pos : 0 < Z.det := hZ_det ▸ Finset.prod_pos (fun i _ ↦ hZ_pos i)
  have hZ_unit : IsUnit Z := by
    rw [isUnit_iff_isUnit_det]; exact IsUnit.mk0 _ (ne_of_gt hZ_det_pos)
  -- Step 4: K = star Z * M * Z is Hermitian
  have hK_herm : (star Z * M * Z).IsHermitian :=
    isHermitian_conjTranspose_mul_mul Z (spectralMatrix_isHermitian G ↑c₁ ↑c₂ ↑c₃)
  -- Step 5: K is strictly diag-dominant (sorry'd)
  have hK_dom : ∀ i : Fin n,
      ∑ j ∈ Finset.univ.erase i, ‖(star Z * M * Z) i j‖ <
      (star Z * M * Z) i i :=
    congruence_diagDominant n d hn hd G rotStr certStr c₁ c₂ c₃ hcert hmatch
  -- Step 6: K is PSD (Hermitian + diag-dominant → PSD)
  have hK_psd : (star Z * M * Z).PosSemidef := diagDominant_posSemidef hK_herm hK_dom
  -- Step 7: M is PSD via congruence (K PSD + Z invertible → M PSD)
  exact hZ_unit.posSemidef_star_left_conjugate_iff.mp hK_psd


/-! **Certificate → walk bound (proved from Layers 1 + 3)** -/

/-- If `checkCertificate` passes and the rotation map matches `G.rot`,
    then `c₂ · d² · ‖Wf‖² ≤ c₁ · ‖f‖²` for all mean-zero `f`.

    Proved by chaining Layer 3 (certificate → PSD) with Layer 1 (PSD → walk bound). -/
theorem certificate_implies_walk_bound
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (G : RegularGraph n d)
    (rotStr certStr : String) (c₁ c₂ c₃ : ℤ)
    (hcert : checkCertificate rotStr certStr n d c₁ c₂ c₃ = true)
    (hmatch : ∀ vp : Fin n × Fin d,
      G.rot vp = (⟨decodeBase85Nat rotStr.toUTF8 (2 * (vp.1.val * d + vp.2.val)) % n,
                    Nat.mod_lt _ hn⟩,
                  ⟨decodeBase85Nat rotStr.toUTF8 (2 * (vp.1.val * d + vp.2.val) + 1) % d,
                    Nat.mod_lt _ hd⟩))
    (f : EuclideanSpace ℝ (Fin n))
    (hf : meanCLM n f = 0) :
    (c₂ : ℝ) * (d : ℝ) ^ 2 * ‖G.walkCLM f‖ ^ 2 ≤ (c₁ : ℝ) * ‖f‖ ^ 2 :=
  spectralMatrix_posSemidef_implies_walk_bound hn hd G ↑c₁ ↑c₂ ↑c₃
    (checker_implies_spectralMatrix_psd n d hn hd G rotStr certStr c₁ c₂ c₃ hcert hmatch)
    f hf


/-! **Bridge: PSD certificate → spectral gap bound** -/

/-- If `checkCertificate` passes for a rotation map and certificate,
    then any `RegularGraph` whose rotation map agrees with `rotStr` has
    `spectralGap G ≤ βn / (βd · d)`, provided `c₁ · βd² ≤ c₂ · βn²`.

    The hypothesis `hmatch` connects the abstract `G.rot` to the concrete
    base-85 encoded rotation map. When `G` is defined directly from
    `rotStr`, this is `rfl`.

    Proved by chaining `spectralGap_le_of_walk_bound`,
    `certificate_implies_walk_bound`, and `sqrt_coeff_le_frac`. -/
theorem certificate_bridge (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (G : RegularGraph n d)
    (rotStr certStr : String) (c₁ c₂ c₃ : ℤ)
    (hcert : checkCertificate rotStr certStr n d c₁ c₂ c₃ = true)
    (βn βd : ℕ) (hβd : 0 < βd)
    (hβ : c₁ * (↑βd * ↑βd) ≤ c₂ * (↑βn * ↑βn))
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 < c₂)
    (hmatch : ∀ vp : Fin n × Fin d,
      G.rot vp = (⟨decodeBase85Nat rotStr.toUTF8 (2 * (vp.1.val * d + vp.2.val)) % n,
                    Nat.mod_lt _ hn⟩,
                  ⟨decodeBase85Nat rotStr.toUTF8 (2 * (vp.1.val * d + vp.2.val) + 1) % d,
                    Nat.mod_lt _ hd⟩)) :
    spectralGap G ≤ ↑βn / (↑βd * ↑d) :=
  (spectralGap_le_of_walk_bound hd G (by exact_mod_cast hc₁) (by exact_mod_cast hc₂)
    (fun f hf ↦ certificate_implies_walk_bound n d hn hd G
      rotStr certStr c₁ c₂ c₃ hcert hmatch f hf)).trans
  (sqrt_coeff_le_frac (by exact_mod_cast hc₂) hd hβd (by
    have h : ((c₁ * (↑βd * ↑βd) : ℤ) : ℝ) ≤ ((c₂ * (↑βn * ↑βn) : ℤ) : ℝ) :=
      Int.cast_le.mpr hβ
    push_cast at h; nlinarith))
