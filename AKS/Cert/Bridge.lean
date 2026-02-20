/-
  # Certificate Bridge Theorem

  Connects the decidable `checkCertificateSlow` predicate to the spectral gap
  bound on `RegularGraph`. Decomposed into three layers:

  **Layer 1** (`SpectralMatrix.lean`): M PSD → walk bound (provable)
  **Layer 2** (`DiagDominant.lean`): K diag-dominant + Z invertible → M PSD (provable)
  **Layer 3** (this file): `checkCertificateSlow = true` → spectral matrix PSD

  The bridge then chains:
  1. `checker_implies_spectralMatrix_psd` (Layer 3): certificate → M PSD
  2. `spectralMatrix_posSemidef_implies_walk_bound` (Layer 1): M PSD → walk bound
  3. `spectralGap_le_of_walk_bound` (in `WalkBound.lean`): walk bound → spectral gap
  4. `sqrt_coeff_le_frac` (in `WalkBound.lean`): coefficient arithmetic

  Layer 3 is fully proved: structural proof (congruence, invertibility,
  Hermiticity, PSD assembly) plus bridge lemmas connecting the integer checker
  computation to the formal real matrix via `hmatch`.
-/

import AKS.Cert.Defs
import AKS.Cert.FastProof
import AKS.Cert.ColumnNormBridge
import AKS.Cert.WalkBound
import AKS.Cert.SpectralMatrix
import AKS.Cert.DiagDominant
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

/-! **Bridge helper lemmas** -/

/-- `sumTo f n = ∑ k : Fin n, f k.val`. -/
private theorem sumTo_eq_sum (f : ℕ → ℤ) (n : ℕ) :
    sumTo f n = ∑ k : Fin n, f k.val := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    rw [sumTo, ih, Fin.sum_univ_castSucc]
    simp [Fin.val_castSucc, Fin.val_last]

/-- Certificate matrix entry correspondence. -/
private theorem certEntry_eq (certBytes : ByteArray) (n : ℕ) (i j : Fin n) :
    certMatrixReal certBytes n i j = ↑(certEntryInt certBytes i.val j.val) := by
  simp only [certMatrixReal, certEntryInt, of_apply]
  split_ifs <;> simp

/-- Adjacency-vector product correspondence: `adjMulPure` computes the
    unnormalized adjacency product `(d • adjMatrix G *ᵥ x) v`. -/
private theorem adjMul_eq {n d : ℕ} (G : RegularGraph n d)
    (rotBytes : ByteArray) (hn : 0 < n) (hd : 0 < d)
    (hmatch : ∀ vp : Fin n × Fin d,
      G.rot vp = (⟨decodeBase85Nat rotBytes (2 * (vp.1.val * d + vp.2.val)) % n,
                    Nat.mod_lt _ hn⟩,
                  ⟨decodeBase85Nat rotBytes (2 * (vp.1.val * d + vp.2.val) + 1) % d,
                    Nat.mod_lt _ hd⟩))
    (z_int : ℕ → ℤ) (x : Fin n → ℝ)
    (hzx : ∀ k : Fin n, x k = ↑(z_int k.val))
    (v : Fin n) :
    (((d : ℝ) • adjMatrix G) *ᵥ x) v =
    ↑(adjMulPure rotBytes z_int n d v.val) := by
  rw [unnorm_adj_mulVec G x v]
  simp only [adjMulPure, sumTo_eq_sum]
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro p _
  have hneighbor : G.neighbor v p =
      ⟨decodeBase85Nat rotBytes (2 * (v.val * d + p.val)) % n, Nat.mod_lt _ hn⟩ := by
    have h := hmatch (v, p)
    show (G.rot (v, p)).1 = _
    rw [h]
  rw [hneighbor, hzx]

/-- `pEntryPure` corresponds to `(spectralMatrix G c₁ c₂ c₃ * Z) k j`. -/
private theorem pEntry_eq {n d : ℕ} (G : RegularGraph n d)
    (rotBytes certBytes : ByteArray) (hn : 0 < n) (hd : 0 < d)
    (hmatch : ∀ vp : Fin n × Fin d,
      G.rot vp = (⟨decodeBase85Nat rotBytes (2 * (vp.1.val * d + vp.2.val)) % n,
                    Nat.mod_lt _ hn⟩,
                  ⟨decodeBase85Nat rotBytes (2 * (vp.1.val * d + vp.2.val) + 1) % d,
                    Nat.mod_lt _ hd⟩))
    (c₁ c₂ c₃ : ℤ) (k j : Fin n) :
    (spectralMatrix G (↑c₁) (↑c₂) (↑c₃) * certMatrixReal certBytes n) k j =
    ↑(pEntryPure rotBytes certBytes n d c₁ c₂ c₃ k.val j.val) := by
  set Z := certMatrixReal certBytes n
  set A := (↑d : ℝ) • adjMatrix G
  -- Expand matrix product
  simp only [mul_apply, spectralMatrix]
  simp only [add_apply, sub_apply, smul_apply, one_apply, Matrix.of_apply, smul_eq_mul]
  -- Distribute the sum
  simp_rw [add_mul, sub_mul]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- Simplify identity term: c₁ * Z k j
  have hI : ∑ l : Fin n, (↑c₁ * if k = l then 1 else 0) * Z l j = ↑c₁ * Z k j := by
    have : ∀ l, (↑c₁ * if k = l then (1 : ℝ) else 0) * Z l j =
      if k = l then ↑c₁ * Z l j else 0 := fun l ↦ by split_ifs <;> ring
    simp_rw [this, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Simplify J term: c₃ * ∑ Z l j
  have hJ : ∑ l : Fin n, ↑c₃ * 1 * Z l j = ↑c₃ * ∑ l : Fin n, Z l j := by
    simp_rw [mul_one]; rw [Finset.mul_sum]
  -- Set up integer function for z column
  set zj_int : ℕ → ℤ := fun i ↦ certEntryInt certBytes i j.val
  set zj_real : Fin n → ℝ := fun l ↦ Z l j
  have hzj : ∀ l : Fin n, zj_real l = ↑(zj_int l.val) := fun l ↦ certEntry_eq certBytes n l j
  -- Bz correspondence
  have hBz : ∀ v : Fin n, (A *ᵥ zj_real) v = ↑(adjMulPure rotBytes zj_int n d v.val) :=
    adjMul_eq G rotBytes hn hd hmatch zj_int zj_real hzj
  -- B²z correspondence
  set bz_int : ℕ → ℤ := fun v ↦ adjMulPure rotBytes zj_int n d v
  set bz_real : Fin n → ℝ := fun v ↦ (A *ᵥ zj_real) v
  have hbz : ∀ v : Fin n, bz_real v = ↑(bz_int v.val) := hBz
  have hB2z : ∀ v : Fin n, (A *ᵥ bz_real) v = ↑(adjMulPure rotBytes bz_int n d v.val) :=
    adjMul_eq G rotBytes hn hd hmatch bz_int bz_real hbz
  -- A² term
  have hAA : ∑ l : Fin n, ↑c₂ * (A * A) k l * Z l j =
      ↑c₂ * ↑(adjMulPure rotBytes bz_int n d k.val) := by
    show ∑ l, ↑c₂ * (A * A) k l * zj_real l = _
    rw [show ∑ l, ↑c₂ * (A * A) k l * zj_real l = ↑c₂ * ((A * A) *ᵥ zj_real) k from by
      simp only [mulVec, dotProduct, Finset.mul_sum]; congr 1; ext l; ring]
    rw [← mulVec_mulVec]; congr 1; exact hB2z k
  -- Column sum
  have hColSum : ∑ l : Fin n, Z l j = ↑(sumTo (fun l ↦ certEntryInt certBytes l j.val) n) := by
    simp_rw [show ∀ l : Fin n, Z l j = ↑(certEntryInt certBytes l.val j.val) from
      fun l ↦ certEntry_eq certBytes n l j]
    rw [sumTo_eq_sum, Int.cast_sum]
  -- Combine
  rw [hI, hAA, hJ, hColSum]
  simp only [pEntryPure]
  have hZkj : Z k j = ↑(certEntryInt certBytes k.val j.val) := certEntry_eq certBytes n k j
  rw [hZkj]; push_cast; ring

/-- `kEntryPure` corresponds to `(star Z * M * Z) i j`. -/
private theorem kEntry_eq {n d : ℕ} (G : RegularGraph n d)
    (rotBytes certBytes : ByteArray) (hn : 0 < n) (hd : 0 < d)
    (hmatch : ∀ vp : Fin n × Fin d,
      G.rot vp = (⟨decodeBase85Nat rotBytes (2 * (vp.1.val * d + vp.2.val)) % n,
                    Nat.mod_lt _ hn⟩,
                  ⟨decodeBase85Nat rotBytes (2 * (vp.1.val * d + vp.2.val) + 1) % d,
                    Nat.mod_lt _ hd⟩))
    (c₁ c₂ c₃ : ℤ) (i j : Fin n) :
    (star (certMatrixReal certBytes n) * spectralMatrix G (↑c₁) (↑c₂) (↑c₃) *
      certMatrixReal certBytes n) i j =
    ↑(kEntryPure rotBytes certBytes n d c₁ c₂ c₃ i.val j.val) := by
  set Z := certMatrixReal certBytes n
  set M := spectralMatrix G (↑c₁ : ℝ) (↑c₂) (↑c₃)
  rw [Matrix.mul_assoc, mul_apply]
  -- Goal: ∑ k, (star Z) i k * (M * Z) k j = ↑(kEntryPure ...)
  show ∑ k : Fin n, (star Z) i k * (M * Z) k j =
    ↑(sumTo (fun k ↦ certEntryInt certBytes k i.val *
      pEntryPure rotBytes certBytes n d c₁ c₂ c₃ k j.val) n)
  rw [sumTo_eq_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro k _
  -- (star Z) i k = Z k i for real matrices
  have hstar : (star Z) i k = Z k i := by
    change Zᴴ i k = Z k i
    rw [conjTranspose_apply, star_trivial]
  rw [hstar]
  show certMatrixReal certBytes n k i * (M * certMatrixReal certBytes n) k j =
    ↑(certEntryInt certBytes k.val i.val * pEntryPure rotBytes certBytes n d c₁ c₂ c₃ k.val j.val)
  rw [certEntry_eq certBytes n k i,
      pEntry_eq G rotBytes certBytes hn hd hmatch c₁ c₂ c₃ k j]
  push_cast; ring


/-! **Column-norm bound approach** -/

/-- `intAbs x = |x|` for integers. -/
private theorem intAbs_eq_abs (x : ℤ) : intAbs x = |x| := by
  unfold intAbs
  split_ifs with h
  · exact (abs_of_nonneg (by omega)).symm
  · exact (abs_of_neg (by omega)).symm

/-- `zColNormPure` expressed as a `Finset.sum`. -/
private theorem zColNormPure_eq_sum (certBytes : ByteArray) (n j : Nat) :
    zColNormPure certBytes n j = ∑ k : Fin n, |certEntryInt certBytes k.val j| := by
  simp only [zColNormPure, sumTo_eq_sum]
  congr 1; ext k; exact intAbs_eq_abs _

/-! **Bound lemmas for `epsMaxCol`, `epsMaxVal`, `minDiagVal`** -/

/-- The inlined P entry in `epsMaxCol` equals `pEntryPure` when `colSum = colSumZ`. -/
private lemma epsMaxCol_entry_eq (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (k j : Nat) :
    (let zj := fun i ↦ certEntryInt certBytes i j
     let b2zj_k := adjMulPure rotBytes (fun v ↦ adjMulPure rotBytes zj n d v) n d k
     c₁ * certEntryInt certBytes k j - c₂ * b2zj_k + c₃ * colSumZ certBytes n j) =
    pEntryPure rotBytes certBytes n d c₁ c₂ c₃ k j := by
  unfold pEntryPure colSumZ; rfl

private lemma epsMaxCol_nonneg (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (j : Nat) (colSum : Int) (m : Nat) :
    0 ≤ epsMaxCol rotBytes certBytes n d c₁ c₂ c₃ j colSum m := by
  induction m with
  | zero => unfold epsMaxCol; exact le_refl _
  | succ k ih => unfold epsMaxCol; exact le_max_of_le_left ih

private lemma epsMaxVal_nonneg (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (m : Nat) : 0 ≤ epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ m := by
  induction m with
  | zero => unfold epsMaxVal; exact le_refl _
  | succ j ih => unfold epsMaxVal; exact le_max_of_le_left ih

private lemma epsMaxCol_bound (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (j k bound : Nat) (hk : k < bound) :
    |pEntryPure rotBytes certBytes n d c₁ c₂ c₃ k j| ≤
    epsMaxCol rotBytes certBytes n d c₁ c₂ c₃ j (colSumZ certBytes n j) bound := by
  induction bound with
  | zero => omega
  | succ m ih =>
    unfold epsMaxCol
    by_cases hkm : k < m
    · exact le_max_of_le_left (ih hkm)
    · have : k = m := by omega
      subst this
      apply le_max_of_le_right
      rw [← epsMaxCol_entry_eq, intAbs_eq_abs]

private lemma epsMaxVal_bound (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (k j bound : Nat) (hkj : k < j) (hjb : j < bound) :
    |pEntryPure rotBytes certBytes n d c₁ c₂ c₃ k j| ≤
    epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ bound := by
  induction bound with
  | zero => omega
  | succ m ih =>
    unfold epsMaxVal
    by_cases hjm : j < m
    · exact le_max_of_le_left (ih hjm)
    · have : j = m := by omega
      subst this; exact le_max_of_le_right (epsMaxCol_bound _ _ _ _ _ _ _ _ _ _ hkj)

private lemma minDiagVal_bound (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (j m : Nat) (hj : j < m) (hm : 0 < m) :
    minDiagVal rotBytes certBytes n d c₁ c₂ c₃ m ≤
    pEntryPure rotBytes certBytes n d c₁ c₂ c₃ j j := by
  induction m with
  | zero => omega
  | succ m ih =>
    match m, hj with
    | 0, hj =>
      have hj0 : j = 0 := by omega
      subst hj0; exact le_refl _
    | m' + 1, hj =>
      simp only [minDiagVal]
      by_cases hjm : j < m' + 1
      · exact le_trans (min_le_left _ _) (ih hjm (by omega))
      · have : j = m' + 1 := by omega
        subst this; exact min_le_right _ _

/-! **`checkPerRow` specification** -/

/-- `checkPerRow` extracts per-row column-norm bounds. -/
private theorem checkPerRow_spec (certBytes : ByteArray) (n : Nat) (ε mdpe : Int)
    (remaining i : Nat) (prefSum : Int)
    (h : checkPerRow certBytes n ε mdpe remaining i prefSum = true)
    (hpre : prefSum = sumTo (fun j ↦ zColNormPure certBytes n j) i)
    (k : Nat) (hki : i ≤ k) (hk : k < i + remaining) :
    certEntryInt certBytes k k * mdpe >
    ε * (sumTo (fun j ↦ zColNormPure certBytes n j) k +
         (↑(n - k) : Int) * zColNormPure certBytes n k) := by
  induction remaining generalizing i prefSum k with
  | zero => omega
  | succ r ih =>
    unfold checkPerRow at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hrow, hrest⟩ := h
    by_cases hki_eq : k = i
    · subst hki_eq; rw [hpre] at hrow; exact of_decide_eq_true hrow
    · have hi_lt_k : i + 1 ≤ k := by omega
      exact ih (i + 1) (prefSum + zColNormPure certBytes n i) hrest
        (by rw [hpre]; rfl) k hi_lt_k (by omega)

/-- Specification of what `checkColumnNormBoundPure = true` guarantees.

    Uses the pure recursive `epsMaxVal`/`minDiagVal` which are trivially
    connected to `pEntryPure` via their recursive definitions, avoiding the
    imperative `checkPSDColumns` → `pEntryPure` bridge entirely. -/
private theorem checkColumnNormBoundPure_spec
    (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (hcnb : checkColumnNormBoundPure rotBytes certBytes n d c₁ c₂ c₃ = true) (hn : 0 < n) :
    ∃ epsMax minDiag : Int,
      (0 ≤ epsMax) ∧
      (∀ k j, k < j → j < n →
        |pEntryPure rotBytes certBytes n d c₁ c₂ c₃ k j| ≤ epsMax) ∧
      (∀ j, j < n → minDiag ≤ pEntryPure rotBytes certBytes n d c₁ c₂ c₃ j j) ∧
      (∀ i, i < n →
        certEntryInt certBytes i i * (minDiag + epsMax) >
        epsMax * (sumTo (fun j ↦ zColNormPure certBytes n j) i +
                  (↑(n - i) : Int) * zColNormPure certBytes n i)) := by
  -- Extract checkPerRow from the pure check
  unfold checkColumnNormBoundPure at hcnb
  rw [if_neg (by simp [beq_iff_eq]; omega)] at hcnb
  -- hcnb : checkPerRow certBytes n (epsMaxVal ...) (minDiagVal ... + epsMaxVal ...) n 0 0 = true
  -- Witness with epsMaxVal and minDiagVal
  set ε := epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ n
  set δ := minDiagVal rotBytes certBytes n d c₁ c₂ c₃ n
  refine ⟨ε, δ, epsMaxVal_nonneg _ _ _ _ _ _ _ _,
          fun k j hk hj ↦ epsMaxVal_bound _ _ _ _ _ _ _ _ _ _ hk hj,
          fun j hj ↦ minDiagVal_bound _ _ _ _ _ _ _ j n hj hn,
          fun i hi ↦ ?_⟩
  exact checkPerRow_spec certBytes n ε (δ + ε) n 0 0 hcnb rfl i (Nat.zero_le _) (by omega)

/-- `kEntryPure` is symmetric: `K[i,j] = K[j,i]` (from `K = Z*MZ` Hermitian). -/
private theorem kEntryPure_comm {n d : ℕ} (G : RegularGraph n d)
    (rotBytes certBytes : ByteArray) (hn : 0 < n) (hd : 0 < d)
    (hmatch : ∀ vp : Fin n × Fin d,
      G.rot vp = (⟨decodeBase85Nat rotBytes (2 * (vp.1.val * d + vp.2.val)) % n,
                    Nat.mod_lt _ hn⟩,
                  ⟨decodeBase85Nat rotBytes (2 * (vp.1.val * d + vp.2.val) + 1) % d,
                    Nat.mod_lt _ hd⟩))
    (c₁ c₂ c₃ : ℤ) (i j : Fin n) :
    kEntryPure rotBytes certBytes n d c₁ c₂ c₃ i.val j.val =
    kEntryPure rotBytes certBytes n d c₁ c₂ c₃ j.val i.val := by
  -- Both sides cast to K[i,j] and K[j,i] via kEntry_eq
  have h1 := kEntry_eq G rotBytes certBytes hn hd hmatch c₁ c₂ c₃ i j
  have h2 := kEntry_eq G rotBytes certBytes hn hd hmatch c₁ c₂ c₃ j i
  -- K is Hermitian, so K[i,j] = K[j,i] for real matrices
  have hK := isHermitian_conjTranspose_mul_mul (certMatrixReal certBytes n)
    (spectralMatrix_isHermitian G ↑c₁ ↑c₂ ↑c₃)
  have hsym : (star (certMatrixReal certBytes n) * spectralMatrix G ↑c₁ ↑c₂ ↑c₃ *
    certMatrixReal certBytes n) i j =
    (star (certMatrixReal certBytes n) * spectralMatrix G ↑c₁ ↑c₂ ↑c₃ *
    certMatrixReal certBytes n) j i := by
    have h := congr_fun (congr_fun hK i) j
    rw [conjTranspose_apply, star_trivial] at h
    exact h.symm
  rw [h1, h2] at hsym
  exact_mod_cast hsym

/-- Extraction: `checkAllRowsDomPure ... n = true` implies each row is checked. -/
private theorem checkAllRows_spec (rotBytes certBytes : ByteArray) (n d : ℕ)
    (c₁ c₂ c₃ : ℤ) (m : ℕ)
    (h : checkAllRowsDomPure rotBytes certBytes n d c₁ c₂ c₃ m = true)
    (i : ℕ) (hi : i < m) :
    checkRowDomPure rotBytes certBytes n d c₁ c₂ c₃ i = true := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [checkAllRowsDomPure, Bool.and_eq_true] at h
    by_cases him : i < m
    · exact ih h.1 him
    · have : i = m := by omega
      subst this; exact h.2

/-- Bridge lemma: if `checkAllRowsDomPure` passes and the rotation map matches,
    then K = star Z * M * Z is strictly row-diag-dominant.

    This theorem takes `checkAllRowsDomPure` directly (not via `checkCertificateSlow`)
    so it remains valid regardless of which checks `checkCertificateSlow` includes. -/
theorem kRowDominant_implies_diagDominant
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (G : RegularGraph n d)
    (rotStr certStr : String) (c₁ c₂ c₃ : ℤ)
    (hpure : checkAllRowsDomPure rotStr.toUTF8 certStr.toUTF8 n d c₁ c₂ c₃ n = true)
    (hmatch : ∀ vp : Fin n × Fin d,
      G.rot vp = (⟨decodeBase85Nat rotStr.toUTF8 (2 * (vp.1.val * d + vp.2.val)) % n,
                    Nat.mod_lt _ hn⟩,
                  ⟨decodeBase85Nat rotStr.toUTF8 (2 * (vp.1.val * d + vp.2.val) + 1) % d,
                    Nat.mod_lt _ hd⟩))
    : let Z := certMatrixReal certStr.toUTF8 n
    let M := spectralMatrix G (↑c₁) (↑c₂) (↑c₃)
    ∀ i : Fin n,
      ∑ j ∈ Finset.univ.erase i, ‖(star Z * M * Z) i j‖ <
      (star Z * M * Z) i i := by
  -- Introduce let bindings and universally quantified variable
  intro _ _ i
  -- Get row-level check for this i
  have hrow := checkAllRows_spec rotStr.toUTF8 certStr.toUTF8 n d c₁ c₂ c₃ n hpure i.val i.isLt
  -- Extract integer inequality from checkRowDomPure
  simp only [checkRowDomPure] at hrow
  have hint := of_decide_eq_true hrow
  -- Abbreviate
  set rotBytes := rotStr.toUTF8
  set certBytes := certStr.toUTF8
  -- Show each matrix entry equals the integer cast
  have hentry : ∀ a b : Fin n,
      (star (certMatrixReal certBytes n) * spectralMatrix G ↑c₁ ↑c₂ ↑c₃ *
        certMatrixReal certBytes n) a b =
      ↑(kEntryPure rotBytes certBytes n d c₁ c₂ c₃ a.val b.val) :=
    fun a b ↦ kEntry_eq G rotBytes certBytes hn hd hmatch c₁ c₂ c₃ a b
  -- Rewrite diagonal
  rw [hentry i i]
  -- Rewrite off-diagonal sum
  conv_lhs => arg 2; ext j; rw [hentry i j, Real.norm_eq_abs, ← Int.cast_abs]
  rw [← Int.cast_sum]
  -- Now need: ↑(∑ |K_ij|) < ↑(K_ii)
  exact_mod_cast show ∑ j ∈ Finset.univ.erase i,
      |kEntryPure rotBytes certBytes n d c₁ c₂ c₃ i.val j.val| <
      kEntryPure rotBytes certBytes n d c₁ c₂ c₃ i.val i.val from by
    -- Connect Finset.sum erase to sumTo with if-skip
    have herase_eq : ∑ j ∈ Finset.univ.erase i,
        |kEntryPure rotBytes certBytes n d c₁ c₂ c₃ i.val j.val| =
        ∑ j : Fin n, if j = i then 0
          else |kEntryPure rotBytes certBytes n d c₁ c₂ c₃ i.val j.val| := by
      have h := Finset.add_sum_erase Finset.univ
        (fun j : Fin n ↦ if j = i then (0 : ℤ)
          else |kEntryPure rotBytes certBytes n d c₁ c₂ c₃ i.val j.val|)
        (Finset.mem_univ i)
      simp only [ite_true, zero_add] at h
      rw [← h]
      apply Finset.sum_congr rfl
      intro j hj; rw [if_neg (Finset.ne_of_mem_erase hj)]
    rw [herase_eq]
    -- Connect ∑ Fin n to sumTo
    rw [show ∑ j : Fin n, (if j = i then (0 : ℤ)
        else |kEntryPure rotBytes certBytes n d c₁ c₂ c₃ i.val j.val|) =
        sumTo (fun j ↦ if j == i.val then 0
          else let v := kEntryPure rotBytes certBytes n d c₁ c₂ c₃ i.val j
               if v ≥ 0 then v else -v) n from by
      rw [sumTo_eq_sum]
      apply Finset.sum_congr rfl; intro j _
      simp only [beq_iff_eq, Fin.val_eq_val]
      split_ifs with h
      · rfl
      · exact abs_of_nonneg (by omega)
      · exact abs_of_neg (by omega)]
    exact hint

/-- Sum of `S(min(i, j))` over `j : Fin n` splits as
    `∑_{j<i} S(j) + (n-i)·S(i) = sumTo S i + (n-i)·S(i)`. -/
private lemma sum_min_split (S : ℕ → ℤ) : ∀ (n i : ℕ), i < n →
    ∑ j : Fin n, S (min i j.val) = sumTo S i + ↑(n - i) * S i := by
  intro n; induction n with
  | zero => intro i hi; omega
  | succ m ih =>
    intro i hi
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    by_cases hin : i < m
    · rw [ih i hin, Nat.min_eq_left (Nat.le_of_lt hin)]
      have hcast : (↑(m + 1 - i) : ℤ) = ↑(m - i) + 1 := by
        rw [Nat.succ_sub (Nat.le_of_lt hin)]; push_cast; ring
      rw [hcast]; ring
    · -- i = m: all terms in ∑_{j<m} have min(i,j) = j, last term is S(i)
      have hi_eq : i = m := Nat.le_antisymm (Nat.lt_succ_iff.mp hi) (Nat.not_lt.mp hin)
      have hterms : ∀ j : Fin m, S (min i j.val) = S j.val := by
        intro j; rw [hi_eq, Nat.min_eq_right (Nat.le_of_lt j.isLt)]
      simp_rw [hterms, ← sumTo_eq_sum, hi_eq, Nat.min_self]
      have : (↑(m + 1 - m) : ℤ) = 1 := by omega
      rw [this]; ring

/-- `K = Z* · M · Z` is strictly row-diag-dominant when the certificate checker passes.

    The proof uses `checkColumnNormBoundPure` (pure recursive column-norm check) together
    with the PSD check bounds (minDiag, epsMax) to establish diagonal dominance
    mathematically via the upper-triangular structure of Z:
    - Off-diagonal: `|K[i,j]| ≤ epsMax · S_{min(i,j)}` where `S_j = ∑_{k≤j} |Z[k,j]|`
    - Diagonal: `K[i,i] ≥ Z[i,i] · minDiag - (S_i - Z[i,i]) · epsMax`
    - Column-norm bound checks: `Z[i,i] · (minDiag + epsMax) > epsMax · T_i` -/
theorem congruence_diagDominant
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (G : RegularGraph n d)
    (rotStr certStr : String) (c₁ c₂ c₃ : ℤ)
    (hcert : checkCertificateSlow rotStr certStr n d c₁ c₂ c₃ = true)
    (hcnbp : checkColumnNormBoundPure rotStr.toUTF8 certStr.toUTF8 n d c₁ c₂ c₃ = true)
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
  intro _ _ i
  set rotBytes := rotStr.toUTF8
  set certBytes := certStr.toUTF8
  -- Extract PSD sub-check from checkCertificateSlow
  have hpsd : checkPSDCertificate rotBytes certBytes n d c₁ c₂ c₃ = true := by
    simp only [checkCertificateSlow, Bool.and_eq_true] at hcert; exact hcert.1.2
  -- Get Z[i,i] > 0 from PSD check (reuse certMatrix_posdiag)
  have hZii_pos : 0 < certEntryInt certBytes i.val i.val := by
    have h := certMatrix_posdiag n certBytes rotBytes d c₁ c₂ c₃ hpsd i
    rw [certEntry_eq] at h; exact_mod_cast h
  -- Get epsMax, minDiag, and their properties from pure column-norm check
  obtain ⟨ε, δ, hε_nn, hP_bound, hP_diag, hrow_check⟩ :=
    checkColumnNormBoundPure_spec rotBytes certBytes n d c₁ c₂ c₃ hcnbp hn
  -- Abbreviate column norm
  set S := zColNormPure certBytes n
  -- K entry correspondence
  have hentry : ∀ a b : Fin n,
      (star (certMatrixReal certBytes n) * spectralMatrix G ↑c₁ ↑c₂ ↑c₃ *
        certMatrixReal certBytes n) a b =
      ↑(kEntryPure rotBytes certBytes n d c₁ c₂ c₃ a.val b.val) :=
    fun a b ↦ kEntry_eq G rotBytes certBytes hn hd hmatch c₁ c₂ c₃ a b
  -- Rewrite goal in terms of kEntryPure
  rw [hentry i i]
  conv_lhs => arg 2; ext j; rw [hentry i j, Real.norm_eq_abs, ← Int.cast_abs]
  rw [← Int.cast_sum]
  -- Reduce to integer inequality
  exact_mod_cast show ∑ j ∈ Finset.univ.erase i,
      |kEntryPure rotBytes certBytes n d c₁ c₂ c₃ i.val j.val| <
      kEntryPure rotBytes certBytes n d c₁ c₂ c₃ i.val i.val from by
    -- Helper: certEntryInt(k,col) = 0 when k > col (upper triangular)
    have hcert_zero : ∀ k col : ℕ, ¬(k ≤ col) →
        certEntryInt certBytes k col = 0 := by
      intro k col hk; unfold certEntryInt; exact if_neg hk
    -- Bound |∑_k Z[k,col]*P[k,row]| ≤ ε * S(col) when col < row
    have habs_bound : ∀ col row : ℕ, col < n → row < n → col < row →
        |∑ k : Fin n, certEntryInt certBytes k.val col *
          pEntryPure rotBytes certBytes n d c₁ c₂ c₃ k.val row| ≤
        ε * S col := by
      intro col row hcol hrow hlt
      calc |∑ k : Fin n, certEntryInt certBytes k.val col *
            pEntryPure rotBytes certBytes n d c₁ c₂ c₃ k.val row|
          ≤ ∑ k : Fin n, |certEntryInt certBytes k.val col| *
            |pEntryPure rotBytes certBytes n d c₁ c₂ c₃ k.val row| := by
            calc _ ≤ ∑ k : Fin n, |certEntryInt certBytes k.val col *
                  pEntryPure rotBytes certBytes n d c₁ c₂ c₃ k.val row| :=
                  Finset.abs_sum_le_sum_abs _ _
              _ = _ := by apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
        _ ≤ ∑ k : Fin n, |certEntryInt certBytes k.val col| * ε := by
            apply Finset.sum_le_sum; intro k _
            by_cases hk : k.val ≤ col
            · exact mul_le_mul_of_nonneg_left (hP_bound k.val row (by omega) hrow) (abs_nonneg _)
            · simp [hcert_zero k.val col hk]
        _ = ε * S col := by
            rw [← Finset.sum_mul, ← zColNormPure_eq_sum]; ring
    -- Key: |K[i,j]| ≤ ε * S(min(i,j)) for j ≠ i
    have hK_bound : ∀ j : Fin n, j ≠ i →
        |kEntryPure rotBytes certBytes n d c₁ c₂ c₃ i.val j.val| ≤
        ε * S (min i.val j.val) := by
      intro j hne
      by_cases hij : i.val < j.val
      · -- Case j > i: col=i, row=j
        rw [Nat.min_eq_left (le_of_lt hij)]
        unfold kEntryPure; rw [sumTo_eq_sum]
        exact habs_bound i.val j.val i.isLt j.isLt hij
      · -- Case j < i: use K symmetry to swap, then col=j, row=i
        have hji : j.val < i.val := by omega
        rw [Nat.min_eq_right (le_of_lt hji),
            kEntryPure_comm G rotBytes certBytes hn hd hmatch c₁ c₂ c₃ i j]
        unfold kEntryPure; rw [sumTo_eq_sum]
        exact habs_bound j.val i.val j.isLt i.isLt hji
    -- Off-diagonal sum bound: ∑|K[i,j]| + ε*S(i) ≤ ε*(sumTo S i + (n-i)*S(i))
    have hoff : ∑ j ∈ Finset.univ.erase i,
        |kEntryPure rotBytes certBytes n d c₁ c₂ c₃ i.val j.val| + ε * S i.val ≤
        ε * (sumTo (fun j ↦ S j) i.val + ↑(n - i.val) * S i.val) := by
      -- Step 1: bound each |K[i,j]| by ε * S(min(i,j))
      have h1 : ∑ j ∈ Finset.univ.erase i,
          |kEntryPure rotBytes certBytes n d c₁ c₂ c₃ i.val j.val| ≤
          ε * ∑ j ∈ Finset.univ.erase i, S (min i.val j.val) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun j hj ↦ hK_bound j (Finset.ne_of_mem_erase hj))
      -- Step 2: add back the i-th term to recover full sum
      have h2 : ε * ∑ j ∈ Finset.univ.erase i, S (min i.val j.val) + ε * S i.val =
          ε * ∑ j : Fin n, S (min i.val j.val) := by
        rw [← mul_add, add_comm]
        congr 1
        have h := Finset.add_sum_erase Finset.univ
          (fun j : Fin n ↦ S (min i.val j.val)) (Finset.mem_univ i)
        simp only [Nat.min_self] at h
        exact h
      -- Step 3: sum identity
      have h3 : ∑ j : Fin n, S (min i.val j.val) =
          sumTo (fun j ↦ S j) i.val + ↑(n - i.val) * S i.val :=
        sum_min_split S n i.val i.isLt
      have h4 : ε * ∑ j : Fin n, S (min i.val j.val) =
          ε * (sumTo (fun j ↦ S j) i.val + ↑(n - i.val) * S i.val) := by rw [h3]
      linarith
    -- Diagonal lower bound: K[i,i] ≥ Z[i,i]*(δ+ε) - S_i*ε
    have hdiag : kEntryPure rotBytes certBytes n d c₁ c₂ c₃ i.val i.val ≥
        certEntryInt certBytes i.val i.val * (δ + ε) - S i.val * ε := by
      -- Express K[i,i] as sum, split at k = i
      have hsplit := Finset.add_sum_erase Finset.univ
        (fun k : Fin n ↦ certEntryInt certBytes k.val i.val *
          pEntryPure rotBytes certBytes n d c₁ c₂ c₃ k.val i.val)
        (Finset.mem_univ i)
      unfold kEntryPure; rw [sumTo_eq_sum, ← hsplit]
      -- Bound the i-th term: Z[i,i]*P[i,i] ≥ Z[i,i]*δ
      have hdiag_term : certEntryInt certBytes i.val i.val *
          pEntryPure rotBytes certBytes n d c₁ c₂ c₃ i.val i.val ≥
          certEntryInt certBytes i.val i.val * δ :=
        mul_le_mul_of_nonneg_left (hP_diag i.val i.isLt) (le_of_lt hZii_pos)
      -- Bound off-diagonal terms: -∑_{k≠i} ≤ ε*(S_i - Z[i,i])
      have hoff_abs : |∑ k ∈ Finset.univ.erase i,
          certEntryInt certBytes k.val i.val *
            pEntryPure rotBytes certBytes n d c₁ c₂ c₃ k.val i.val| ≤
          ε * (S i.val - certEntryInt certBytes i.val i.val) := by
        calc |∑ k ∈ Finset.univ.erase i, certEntryInt certBytes k.val i.val *
              pEntryPure rotBytes certBytes n d c₁ c₂ c₃ k.val i.val|
            ≤ ∑ k ∈ Finset.univ.erase i, |certEntryInt certBytes k.val i.val| *
              |pEntryPure rotBytes certBytes n d c₁ c₂ c₃ k.val i.val| := by
              calc _ ≤ ∑ k ∈ Finset.univ.erase i,
                    |certEntryInt certBytes k.val i.val *
                      pEntryPure rotBytes certBytes n d c₁ c₂ c₃ k.val i.val| :=
                    Finset.abs_sum_le_sum_abs _ _
                _ = _ := by apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
          _ ≤ ∑ k ∈ Finset.univ.erase i, |certEntryInt certBytes k.val i.val| * ε := by
              apply Finset.sum_le_sum; intro k hk
              have hne := Finset.ne_of_mem_erase hk
              by_cases hk_lt : k.val < i.val
              · exact mul_le_mul_of_nonneg_left (hP_bound k.val i.val hk_lt i.isLt) (abs_nonneg _)
              · have hgt : ¬(k.val ≤ i.val) := by
                  intro hle; exact hne (Fin.ext (Nat.le_antisymm hle (by omega)))
                simp [hcert_zero k.val i.val hgt]
          _ = ε * (S i.val - certEntryInt certBytes i.val i.val) := by
              rw [← Finset.sum_mul, mul_comm]; congr 1
              have herase := Finset.add_sum_erase Finset.univ
                (fun k : Fin n ↦ |certEntryInt certBytes k.val i.val|)
                (Finset.mem_univ i)
              rw [← zColNormPure_eq_sum] at herase
              have : |certEntryInt certBytes i.val i.val| =
                  certEntryInt certBytes i.val i.val := abs_of_pos hZii_pos
              linarith
      -- From |X| ≤ B, get -X ≤ B, so X ≥ -B
      have hoff_neg := neg_abs_le (∑ k ∈ Finset.univ.erase i,
          certEntryInt certBytes k.val i.val *
            pEntryPure rotBytes certBytes n d c₁ c₂ c₃ k.val i.val)
      -- Combine: f(i) + ∑_{k≠i} ≥ Z[i,i]*δ - ε*(S_i - Z[i,i]) = Z[i,i]*(δ+ε) - S_i*ε
      linarith
    -- Per-row check
    have hrow := hrow_check i.val i.isLt
    -- Combine: K[i,i] ≥ Z[i,i]*(δ+ε) - S_i*ε > ε*T_i - S_i*ε ≥ off-diag sum
    -- The key: ε*T_i - S_i*ε = ε*(sumTo S i + (n-i)*S_i) - ε*S_i
    --                         = ε*(sumTo S i + (n-i)*S_i - S_i) ≥ off-diag sum (by hoff)
    linarith [hoff, hdiag, hrow]


/-! **Involution bridge** -/

private theorem checkInvBelow_all {rotBytes : ByteArray} {n d m : Nat}
    (h : checkInvBelow rotBytes n d m = true) :
    ∀ k, k < m → checkInvAt rotBytes n d k = true := by
  induction m with
  | zero => intro k hk; omega
  | succ m ih =>
    intro k hk
    unfold checkInvBelow at h
    rw [Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.1 hk) with rfl | hlt
    · exact h.1
    · exact ih h.2 k hlt

private theorem mul_add_lt {n d a b : Nat} (ha : a < n) (hb : b < d) :
    a * d + b < n * d := by
  nlinarith

private theorem mul_add_inj {d : Nat} (hd : 0 < d) {a b c e : Nat}
    (hb : b < d) (he : e < d) (h : a * d + b = c * d + e) :
    a = c ∧ b = e := by
  have ha : a = c := by
    have h1 : (a * d + b) / d = a := by
      rw [show a * d + b = d * a + b from by ring]
      rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hb, Nat.add_zero]
    have h2 : (c * d + e) / d = c := by
      rw [show c * d + e = d * c + e from by ring]
      rw [Nat.mul_add_div hd, Nat.div_eq_of_lt he, Nat.add_zero]
    calc a = (a * d + b) / d := h1.symm
      _ = (c * d + e) / d := by rw [h]
      _ = c := h2
  exact ⟨ha, by subst ha; omega⟩

/-- If the pure recursive involution check passes, then `rotFun` is an involution. -/
theorem checkInvolutionSpec_implies_rotFun_involution (rotStr : String) (n d : Nat)
    (hn : 0 < n) (hd : 0 < d)
    (h : checkInvolutionSpec (rotStr.toUTF8) n d = true) :
    ∀ vp, rotFun rotStr n d hn hd (rotFun rotStr n d hn hd vp) = vp := by
  unfold checkInvolutionSpec at h
  rw [Bool.and_eq_true] at h
  intro ⟨v, p⟩
  -- Extract properties at index k = v*d + p
  have hk := checkInvBelow_all h.2 _ (mul_add_lt v.isLt p.isLt)
  unfold checkInvAt at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  obtain ⟨⟨hw, hq⟩, hrt⟩ := hk
  -- Extract properties at index k2 = w*d + q (the image)
  have hk2 := checkInvBelow_all h.2 _ (mul_add_lt hw hq)
  unfold checkInvAt at hk2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk2
  obtain ⟨⟨hv2, hp2⟩, _⟩ := hk2
  -- By uniqueness of mixed-radix representation: v2 = v.val, p2 = p.val
  have ⟨hveq, hpeq⟩ := mul_add_inj hd hp2 p.isLt hrt
  -- Conclude by simplifying mod operations (all values in-bounds → mod is identity)
  apply Prod.ext <;> apply Fin.ext <;>
    simp only [rotFun, Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hq,
               Nat.mod_eq_of_lt hv2, Nat.mod_eq_of_lt hp2]
  · exact hveq
  · exact hpeq

/-- If the involution spec check passes, all decoded neighbor indices are in-bounds. -/
theorem checkInvolutionSpec_neighbor_lt (rotStr : String) (n d : Nat)
    (h : checkInvolutionSpec (rotStr.toUTF8) n d = true) :
    ∀ k, k < n * d → decodeBase85Nat rotStr.toUTF8 (2 * k) < n := by
  unfold checkInvolutionSpec at h
  rw [Bool.and_eq_true] at h
  intro k hk
  have hka := checkInvBelow_all h.2 k hk
  unfold checkInvAt at hka
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hka
  exact hka.1.1


/-! **Layer 3: Certificate → spectral matrix PSD** -/

/-- If `checkCertificateSlow` passes and the rotation map matches `G.rot`,
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
    (hcert : checkCertificateSlow rotStr certStr n d c₁ c₂ c₃ = true)
    (hcnbp : checkColumnNormBoundPure rotStr.toUTF8 certStr.toUTF8 n d c₁ c₂ c₃ = true)
    (hmatch : ∀ vp : Fin n × Fin d,
      G.rot vp = (⟨decodeBase85Nat rotStr.toUTF8 (2 * (vp.1.val * d + vp.2.val)) % n,
                    Nat.mod_lt _ hn⟩,
                  ⟨decodeBase85Nat rotStr.toUTF8 (2 * (vp.1.val * d + vp.2.val) + 1) % d,
                    Nat.mod_lt _ hd⟩)) :
    Matrix.PosSemidef (spectralMatrix G (↑c₁) (↑c₂) (↑c₃)) := by
  -- Extract PSD check from combined check
  have hpsd : checkPSDCertificate rotStr.toUTF8 certStr.toUTF8 n d c₁ c₂ c₃ = true := by
    simp only [checkCertificateSlow, Bool.and_eq_true] at hcert; exact hcert.1.2
  -- Define Z and M
  set Z := certMatrixReal certStr.toUTF8 n with hZ_def
  set M := spectralMatrix G (↑c₁ : ℝ) (↑c₂) (↑c₃) with hM_def
  -- Step 1: Z is upper triangular
  have hZ_tri : Z.BlockTriangular id := by
    intro i j (hij : j < i)
    show certMatrixReal certStr.toUTF8 n i j = 0
    simp only [certMatrixReal, of_apply]
    exact if_neg (by omega)
  -- Step 2: Z has positive diagonal
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
  -- Step 5: K is strictly diag-dominant
  have hK_dom : ∀ i : Fin n,
      ∑ j ∈ Finset.univ.erase i, ‖(star Z * M * Z) i j‖ <
      (star Z * M * Z) i i :=
    congruence_diagDominant n d hn hd G rotStr certStr c₁ c₂ c₃ hcert hcnbp hmatch
  -- Step 6: K is PSD (Hermitian + diag-dominant → PSD)
  have hK_psd : (star Z * M * Z).PosSemidef := diagDominant_posSemidef hK_herm hK_dom
  -- Step 7: M is PSD via congruence (K PSD + Z invertible → M PSD)
  exact hZ_unit.posSemidef_star_left_conjugate_iff.mp hK_psd


/-! **Certificate → walk bound (proved from Layers 1 + 3)** -/

/-- If `checkCertificateSlow` passes and the rotation map matches `G.rot`,
    then `c₂ · d² · ‖Wf‖² ≤ c₁ · ‖f‖²` for all mean-zero `f`.

    Proved by chaining Layer 3 (certificate → PSD) with Layer 1 (PSD → walk bound). -/
theorem certificate_implies_walk_bound
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (G : RegularGraph n d)
    (rotStr certStr : String) (c₁ c₂ c₃ : ℤ)
    (hcert : checkCertificateSlow rotStr certStr n d c₁ c₂ c₃ = true)
    (hcnbp : checkColumnNormBoundPure rotStr.toUTF8 certStr.toUTF8 n d c₁ c₂ c₃ = true)
    (hmatch : ∀ vp : Fin n × Fin d,
      G.rot vp = (⟨decodeBase85Nat rotStr.toUTF8 (2 * (vp.1.val * d + vp.2.val)) % n,
                    Nat.mod_lt _ hn⟩,
                  ⟨decodeBase85Nat rotStr.toUTF8 (2 * (vp.1.val * d + vp.2.val) + 1) % d,
                    Nat.mod_lt _ hd⟩))
    (f : EuclideanSpace ℝ (Fin n))
    (hf : meanCLM n f = 0) :
    (c₂ : ℝ) * (d : ℝ) ^ 2 * ‖G.walkCLM f‖ ^ 2 ≤ (c₁ : ℝ) * ‖f‖ ^ 2 :=
  spectralMatrix_posSemidef_implies_walk_bound hn hd G ↑c₁ ↑c₂ ↑c₃
    (checker_implies_spectralMatrix_psd n d hn hd G rotStr certStr c₁ c₂ c₃ hcert hcnbp hmatch)
    f hf


/-! **Bridge: PSD certificate → spectral gap bound** -/

/-- If `checkCertificateSlow` passes for a rotation map and certificate,
    then any `RegularGraph` whose rotation map agrees with `rotStr` has
    `spectralGap G ≤ βn / (βd · d)`, provided `c₁ · βd² ≤ c₂ · βn²`.

    The hypothesis `hmatch` connects the abstract `G.rot` to the concrete
    base-85 encoded rotation map. When `G` is defined directly from
    `rotStr`, this is `rfl`.

    The `checkColumnNormBoundPure` result is derived structurally from
    `checkCertificateSlow` + `checkInvolutionSpec` via the bridge in
    `ColumnNormBridge.lean`, avoiding any slow `native_decide` on the
    pure checker.

    Proved by chaining `spectralGap_le_of_walk_bound`,
    `certificate_implies_walk_bound`, and `sqrt_coeff_le_frac`. -/
theorem certificate_bridge (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (G : RegularGraph n d)
    (rotStr certStr : String) (c₁ c₂ c₃ : ℤ)
    (hcert : checkCertificateSlow rotStr certStr n d c₁ c₂ c₃ = true)
    (hinvSpec : checkInvolutionSpec rotStr.toUTF8 n d = true)
    (βn βd : ℕ) (hβd : 0 < βd)
    (hβ : c₁ * (↑βd * ↑βd) ≤ c₂ * (↑βn * ↑βn))
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 < c₂)
    (hmatch : ∀ vp : Fin n × Fin d,
      G.rot vp = (⟨decodeBase85Nat rotStr.toUTF8 (2 * (vp.1.val * d + vp.2.val)) % n,
                    Nat.mod_lt _ hn⟩,
                  ⟨decodeBase85Nat rotStr.toUTF8 (2 * (vp.1.val * d + vp.2.val) + 1) % d,
                    Nat.mod_lt _ hd⟩)) :
    spectralGap G ≤ ↑βn / (↑βd * ↑d) := by
  -- Derive checkColumnNormBoundPure structurally (no native_decide)
  have hcnb : checkColumnNormBound rotStr.toUTF8 certStr.toUTF8 n d c₁ c₂ c₃ = true := by
    simp only [checkCertificateSlow, Bool.and_eq_true] at hcert; exact hcert.2
  have hcnbp : checkColumnNormBoundPure rotStr.toUTF8 certStr.toUTF8 n d c₁ c₂ c₃ = true :=
    checkColumnNormBound_implies_pure _ _ n d c₁ c₂ c₃ hcnb
      (checkInvolutionSpec_neighbor_lt rotStr n d hinvSpec) hn
  exact (spectralGap_le_of_walk_bound hd G (by exact_mod_cast hc₁) (by exact_mod_cast hc₂)
      (fun f hf ↦ certificate_implies_walk_bound n d hn hd G
        rotStr certStr c₁ c₂ c₃ hcert hcnbp hmatch f hf)).trans
    (sqrt_coeff_le_frac (by exact_mod_cast hc₂) hd hβd (by
      have h : ((c₁ * (↑βd * ↑βd) : ℤ) : ℝ) ≤ ((c₂ * (↑βn * ↑βn) : ℤ) : ℝ) :=
        Int.cast_le.mpr hβ
      push_cast at h; nlinarith))
