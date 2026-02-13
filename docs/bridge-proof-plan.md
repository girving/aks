# Bridge Theorem Proof Plan

Detailed plan for proving `certificate_bridge` in `AKS/CertificateBridge.lean`.

## Goal

```lean
theorem certificate_bridge (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (G : RegularGraph n d)
    (rotStr certStr : String) (c₁ c₂ c₃ : ℤ)
    (hcert : checkCertificate rotStr certStr n d c₁ c₂ c₃ = true)
    (βn βd : ℕ) (hβd : 0 < βd)
    (hβ : c₁ * (↑βd * ↑βd) ≤ c₂ * (↑βn * ↑βn))
    (hmatch : ∀ vp : Fin n × Fin d, G.rot vp = ...) :
    spectralGap G ≤ ↑βn / (↑βd * ↑d)
```

## Architecture: Three Lemmas

Factor the bridge into three composable pieces:

```
certificate_bridge = Lemma 1 (sorry'd)  →  Lemma 2 (provable)  →  Lemma 3 (provable)
                     certificate check       walk bound → gap       coefficient arithmetic
                     → walk bound             bound via opNorm       via sqrt monotonicity
```

## Key Mathematical Insight

Avoid eigenvalue decomposition entirely. Work with quadratic forms and operator norms:

- On `1⊥` (mean-zero vectors), `J` vanishes, so `M = c₁I - c₂B²` restricted to `1⊥`
- `M ≻ 0` on `1⊥` gives `c₁‖g‖² > c₂‖Bg‖² = c₂d²‖Wg‖²` for nonzero `g ⊥ 1`
- `(W-P)f = Wg` where `g = f - Pf ⊥ 1`, so `spectralGap = sup ‖Wg‖/‖f‖`
- Direct bound: `‖Wg‖ ≤ √(c₁/(c₂d²)) · ‖g‖ ≤ √(c₁/(c₂d²)) · ‖f‖`

No spectral theorem, no eigenvector basis. Just `opNorm_le_bound` + algebra.

## Lemma 1: `certificate_implies_walk_bound` (sorry'd)

**Statement:** If `checkCertificate` passes, then for all mean-zero `f`:

```
(c₂ : ℝ) · d² · ‖W f‖² ≤ (c₁ : ℝ) · ‖f‖²
```

**Why sorry'd:** Requires connecting the imperative integer certificate checker to
real linear algebra. The proof chain would be:

1. Interpret certificate data as upper-triangular integer matrix `Z`
2. The checker verifies properties of `P = MZ` (small upper triangle, large diagonal)
3. Gershgorin on `K = ZᵀP = ZᵀMZ` shows `K` is diagonally dominant → `K ≻ 0`
4. `Z` invertible + `K ≻ 0` → `M ≻ 0` (Mathlib: `IsUnit.posDef_star_left_conjugate_iff`)
5. `M ≻ 0` → quadratic form bound on `1⊥`

**Blocker:** The current checker verifies `min_diag > ε_max · n(n+1)/2` but doesn't
verify properties of `Z` itself (positive diagonal, bounded off-diagonal). For a
formal proof, the checker needs augmentation — either verify `Z[j,j] > 0` or compute
per-column Gershgorin bounds that account for `Z` structure.

```lean
theorem certificate_implies_walk_bound
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (G : RegularGraph n d)
    (rotStr certStr : String) (c₁ c₂ c₃ : ℤ)
    (hcert : checkCertificate rotStr certStr n d c₁ c₂ c₃ = true)
    (hmatch : ∀ vp, G.rot vp = ...)
    (f : EuclideanSpace ℝ (Fin n))
    (hf : meanCLM n f = 0) :
    (c₂ : ℝ) * (d : ℝ) ^ 2 * ‖G.walkCLM f‖ ^ 2 ≤ (c₁ : ℝ) * ‖f‖ ^ 2 := by
  sorry
```

## Lemma 2: `spectralGap_le_of_walk_bound` (provable)

**Statement:** If `0 < d`, `0 < c₂`, and for all mean-zero `g`:

```
c₂ · d² · ‖W g‖² ≤ c₁ · ‖g‖²
```

then `spectralGap G ≤ √(c₁ / (c₂ · d²))`.

```lean
theorem spectralGap_le_of_walk_bound
    {n d : ℕ} (hd : 0 < d) (G : RegularGraph n d)
    {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 < c₂)
    (hbound : ∀ f : EuclideanSpace ℝ (Fin n),
      meanCLM n f = 0 →
      c₂ * (d : ℝ) ^ 2 * ‖G.walkCLM f‖ ^ 2 ≤ c₁ * ‖f‖ ^ 2) :
    spectralGap G ≤ Real.sqrt (c₁ / (c₂ * (d : ℝ) ^ 2))
```

### Proof

1. Unfold `spectralGap` to `‖G.walkCLM - meanCLM n‖`.
2. Apply `ContinuousLinearMap.opNorm_le_bound` with bound `C = √(c₁/(c₂·d²))`.
   - `0 ≤ C` from `Real.sqrt_nonneg`.
3. For any `f`, set `g := f - meanCLM n f`.
4. Show `(W - P) f = W g`:
   - `(W - P) f = W f - P f = W f - W(P f) = W(f - P f) = W g`
   - Uses `walkCLM_comp_meanCLM G hd f` (already proved, RegularGraph.lean:301).
5. Show `meanCLM n g = 0`:
   - `P g = P(f - P f) = P f - P(P f) = P f - P f = 0`
   - Uses `meanCLM_idempotent` (already proved, Square.lean:151).
6. Apply hypothesis to `g`: `c₂ · d² · ‖W g‖² ≤ c₁ · ‖g‖²`.
7. Rearrange: `‖W g‖² ≤ (c₁/(c₂·d²)) · ‖g‖²`.
   Take square root: `‖W g‖ ≤ C · ‖g‖`.
8. `‖g‖ = ‖f - P f‖ ≤ ‖f‖` from `norm_sub_meanCLM_le` (RegularGraph.lean:273).
9. Chain: `‖(W-P) f‖ = ‖W g‖ ≤ C · ‖g‖ ≤ C · ‖f‖`. ∎

### Existing infrastructure used

| Lemma | File:Line | Role |
|-------|-----------|------|
| `walkCLM_comp_meanCLM` | RegularGraph.lean:301 | `W(Pf) = Pf` → `(W-P)f = Wg` |
| `meanCLM_idempotent` | Square.lean:151 | `P² = P` → `Pg = 0` |
| `norm_sub_meanCLM_le` | RegularGraph.lean:273 | `‖f - Pf‖ ≤ ‖f‖` |
| `opNorm_le_bound` | Mathlib | Bound op norm from pointwise bound |

### Tricky step: norm rearrangement (step 7)

From `c₂ * d² * ‖Wg‖² ≤ c₁ * ‖g‖²` with `c₂ * d² > 0`, derive `‖Wg‖ ≤ C * ‖g‖`.

```
‖Wg‖² ≤ (c₁ / (c₂ * d²)) * ‖g‖²          -- divide by c₂*d²
‖Wg‖² ≤ C² * ‖g‖²                          -- since C² = c₁/(c₂*d²)
‖Wg‖ ≤ C * ‖g‖                              -- sqrt both sides (all non-negative)
```

In Lean: use `Real.sqrt_le_sqrt` on `‖Wg‖² ≤ C² * ‖g‖²`, then
`Real.sqrt_sq (norm_nonneg _)` and `Real.sqrt_mul (sq_nonneg C) ‖g‖²`.

## Lemma 3: `sqrt_coeff_le_frac` (provable)

**Statement:** If `0 < c₂`, `0 < βd`, `0 < d`, and `c₁ · βd² ≤ c₂ · βn²`, then:

```
√(c₁ / (c₂ · d²)) ≤ βn / (βd · d)
```

```lean
theorem sqrt_coeff_le_frac
    {c₁ c₂ : ℝ} {d βn βd : ℕ}
    (hc₂ : 0 < c₂) (hd : 0 < d) (hβd : 0 < βd)
    (hβ : c₁ * (βd : ℝ) ^ 2 ≤ c₂ * (βn : ℝ) ^ 2) :
    Real.sqrt (c₁ / (c₂ * (d : ℝ) ^ 2)) ≤ ↑βn / (↑βd * ↑d)
```

### Proof

```
c₁ · βd² ≤ c₂ · βn²                           -- hypothesis
c₁ / c₂ ≤ βn² / βd²                            -- divide by c₂·βd² (both > 0)
c₁ / (c₂ · d²) ≤ βn² / (βd² · d²)             -- divide by d² (> 0)
              = (βn / (βd · d))²
√(c₁ / (c₂·d²)) ≤ √((βn/(βd·d))²)            -- sqrt monotone
                 = βn / (βd · d)                 -- sqrt_sq, RHS ≥ 0
```

Uses `Real.sqrt_le_sqrt`, `Real.sqrt_sq`, `div_le_div`, `field_simp`, `positivity`.

## Assembly

```lean
theorem certificate_bridge ... :=
  (spectralGap_le_of_walk_bound hd G
    (by positivity)  -- 0 ≤ c₁ (or handle c₁ < 0 case)
    (by exact_mod_cast ...)  -- 0 < c₂
    (fun f hf => certificate_implies_walk_bound ... f hf)).trans
  (sqrt_coeff_le_frac
    (by exact_mod_cast ...)  -- 0 < c₂ in ℝ
    hd hβd
    (by exact_mod_cast hβ))  -- cast ℤ inequality to ℝ
```

The `exact_mod_cast` calls handle ℤ → ℝ coercions.

## Risk Assessment

| Lemma | Risk | Time estimate | Notes |
|-------|------|---------------|-------|
| Lemma 1 (sorry'd) | N/A | Deferred | Needs checker augmentation for Z-bounds |
| Lemma 2 | LOW | 1-2 days | Mirrors `spectralGap_square` proof pattern |
| Lemma 3 | LOW | Hours | Pure arithmetic with `field_simp`/`positivity` |
| Assembly | LOW | Hours | Cast management with `exact_mod_cast` |

## Future: Eliminating Lemma 1's Sorry

To formalize Lemma 1, two changes needed:

### 1. Augment the certificate checker

Add to `checkPSDCertificate`:
- Verify `Z[j,j] > 0` for all `j` (positive diagonal → invertible)
- Optionally compute column-sum bounds for tighter Gershgorin

### 2. Formal proof chain

1. Checker output → properties of `P = MZ` (small upper triangle, large diagonal)
2. `Z` upper triangular with positive diagonal → `Z` invertible
3. Gershgorin on `K = ZᵀMZ = ZᵀP` → `K` diagonally dominant → `K ≻ 0`
4. Mathlib `Matrix.IsUnit.posDef_star_left_conjugate_iff`: `Z` invertible + `K ≻ 0` → `M ≻ 0`
5. `M ≻ 0` + `Jg = 0` for `g ⊥ 1` → `c₁‖g‖² > c₂d²‖Wg‖²`

Mathlib tools available:
- `Matrix.PosDef` / `Matrix.PosSemidef` with eigenvalue characterizations
- `eigenvalue_mem_ball` (Gershgorin circle theorem)
- `Matrix.IsUnit.posDef_star_left_conjugate_iff` (congruence)
- `det_ne_zero_of_sum_row_lt_diag` (diagonal dominance → invertibility)
