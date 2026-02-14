/-
  # Certificate Bridge Theorem

  Connects the decidable `checkCertificate` predicate to the spectral gap
  bound on `RegularGraph`. Decomposed into three lemmas:

  1. `certificate_implies_walk_bound` (sorry'd): certificate check →
     quadratic walk bound on mean-zero vectors. Encapsulates all the hard
     work (Gershgorin analysis, Z invertibility, PSD congruence).
  2. `spectralGap_le_of_walk_bound` (proved, in `WalkBound.lean`):
     walk bound → `spectralGap ≤ √(c₁/(c₂·d²))`
  3. `sqrt_coeff_le_frac` (proved, in `WalkBound.lean`):
     `√(c₁/(c₂·d²)) ≤ βn/(βd·d)` from coefficient arithmetic
-/

import AKS.Certificate
import AKS.WalkBound


/-! **Certificate → walk bound (sorry'd)** -/

/-- If `checkCertificate` passes and the rotation map matches `G.rot`,
    then `c₂ · d² · ‖Wf‖² ≤ c₁ · ‖f‖²` for all mean-zero `f`.

    This is the only sorry in the certificate pipeline. The informal proof:
    certificate → `M = c₁I − c₂B² + c₃J` positive definite (Gershgorin on
    the triangular factor) → `c₁ − c₂λ² > 0` for non-trivial eigenvalues →
    walk bound on mean-zero vectors. -/
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
    (c₂ : ℝ) * (d : ℝ) ^ 2 * ‖G.walkCLM f‖ ^ 2 ≤ (c₁ : ℝ) * ‖f‖ ^ 2 := by
  sorry


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
