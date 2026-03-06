# MGG Expander: Architecture and Spectral Gap Proof

## Overview

The Margulis-Gabber-Galil (MGG) expander is a direct 8-regular graph on `(Z/nZ)²` for any `n`.
Alternative to zig-zag: simpler, better constants, no base expander certificate needed.

### Primary Sources

- **Gabber & Galil (1981)**, "Explicit constructions of linear-sized superconcentrators,"
  *J. Comput. System Sci.* 22(3), 407–420.
  Original construction + spectral analysis via continuous torus.
- **Jimbo & Maruoka (1987)**, "Expanders obtained from affine transformations,"
  *Combinatorica* 7, 343–355. [doi:10.1007/BF02579322](https://link.springer.com/article/10.1007/BF02579322).
  Discrete Fourier analysis giving adjacency eigenvalue `≤ 5√2`.
  Proof simplified by Boppana; exposition in Linial–Wigderson lecture notes Chapter 7.
- **Linial & Wigderson**, "Expander Graphs and their Applications" (lecture notes),
  Chapter 7: "The Margulis Construction." Local copy: `docs/hlw-expander-notes.pdf`.
  Contains the Boppana-simplified proof of Theorem 7.2: `λ₂(G) ≤ 5√2 < 8`.
  **This is the primary reference for the formalization.**
- **Hoory, Linial & Wigderson (2006)**, "Expander graphs and their applications,"
  *Bull. Amer. Math. Soc.* 43, 439–561.
  Survey with related exposition (§8).
- **Trevisan (2016)**, CS294 Lecture 18: Margulis-Gabber-Galil Expanders.
  [Blog](https://lucatrevisan.wordpress.com/2016/04/20/cs294-lecture-18-margulis-gabber-galil-expanders/).
  Note: analyzes the simpler `S(x,y)=(x,x+y)` variant, NOT the factor-2 shear variant.

### Important: Variant Matters

The `5√2/8` bound applies specifically to the **factor-2 shear** variant (our construction).
The simpler variant `S(x,y)=(x,x+y), T(x,y)=(x+y,y)` with unit shifts (as in
Trevisan's lectures) has spectral gap -> 1 as n -> infinity, violating the bound for large n.
Verified numerically: at n=100, the simple variant gives lambda_2 = 0.961 > 5*sqrt(2)/8 = 0.884.

## Current Status

### File Layout

```
AKS/MGG/
├── Defs.lean            -- Graph definition, involution (fully proved)
├── DFT.lean             -- 2D DFT, Parseval, correlation pairs (fully proved)
├── WalkExpansion.lean   -- Walk operator expansion 4⟨f,Wf⟩ = C₁+C₂ (fully proved)
├── Young.lean           -- Young's inequality pointwise condition (fully proved)
└── Spectral.lean        -- Rayleigh quotient assembly (fully proved)
```

### Proof Status

**Zero `sorry`s in all MGG files. All files compile without errors.**

The spectral gap bound `spectralGap (mgg n) ≤ 5 * √2 / 8` is fully proved for `n ≥ 3`.

### Fully Proved Files

| File | Lines | Key Results |
|------|-------|-------------|
| `Defs.lean` | ~300 | `mgg n : RegularGraph (n*n) 8`, `mgg_rot_involution` |
| `DFT.lean` | 775 | `dft2d`, `parseval_2d`, `corr_pair1`/`corr_pair2`, `ω_isPrimitiveRoot`, `char_ortho_1d`/`2d`, `abs_one_add_ω` |
| `WalkExpansion.lean` | 161 | `mgg_walkCLM_inner_eq_corr`: `4⟨f,Wf⟩ = C₁+C₂` via port pairing and involution |
| `Young.lean` | 1817 | `pointwiseCondition_forall`, `young_assembly`, all diamond case analysis, shear bijectivity |
| `Spectral.lean` | ~475 | `mgg_rayleigh_bound`, `spectralGap_mgg`, `mgg_spectralGap_of_rayleigh_bound` (all fully proved) |

### Numerical Verification

| n   | lambda_2 (power iteration) | 5*sqrt(2)/8 ~ 0.884 |
|-----|---------------------------|----------------------|
| 3   | 0.576                     | yes                  |
| 7   | 0.722                     | yes                  |
| 23  | 0.777                     | yes                  |
| 100 | 0.809                     | yes                  |

Eigenvalues approach ~0.82 from below as n -> infinity, well below the bound.

## Proof Architecture: Boppana-Simplified Jimbo-Maruoka

The proof uses the **full 2D DFT** on `(Z/nZ)^2` and works entirely in Fourier space.
No L_1/L_2 decomposition, no fiber projections, no Rayleigh quotient per-operator bounds.

### Why NOT Fiber Decomposition

An earlier plan decomposed the walk operator as `W = (L_1 + L_2)/2` where
`L_1` averages the y-preserving shears and `L_2` averages the x-preserving shears,
then tried to bound each `<f, L_i f>` via partial DFT and fiber analysis.

**This approach fails** because:
1. `L_1` preserves a-fibers (functions `f(x,y) = omega^{ax} g(y)`), but `L_2` does NOT
   preserve a-fibers — it mixes x-frequencies.
2. The individual fiber bounds give `spectralGap <= (1 + cos(pi/n))/2 -> 1`, too weak.
3. Getting the tight `5*sqrt(2)/8` constant requires understanding the L_1/L_2 interaction,
   which the fiber decomposition cannot capture.

### Proof Chain

```
8⟨f, Wf⟩ = ∑_v f(v) ∑_i f(T_i v)                    [unfold walkCLM]
         = 2(C₁ + C₂)                                  [pair inverses via mgg_sum_invol]
C₁ = (1/n²) Re(∑_α f̂(α)·conj(f̂(S₂α))·(1+ω⁻ᵅ¹))    [corr_pair1 in DFT.lean]
C₂ = (1/n²) Re(∑_α f̂(α)·conj(f̂(S₁α))·(1+ω⁻ᵅ²))    [corr_pair2 in DFT.lean]
|C₁+C₂| ≤ (2/n²) ∑_α G(α)·[G(S₂α)·|cos(πα₁/n)|     [triangle ineq, |1+ω|=2|cos|]
                             + G(S₁α)·|cos(πα₂/n)|]
         ≤ (2/n²)·(5√2/4)·∑ G(α)²                     [young_assembly: Young + pointwise]
         = (2/n²)·(5√2/4)·n²·‖f‖²                      [parseval_2d]
         = 5√2/2
|⟨f, Wf⟩| = |C₁+C₂|/4 ≤ 5√2/8  ✓
```

### Key Mathematical Facts

**Characters are NOT eigenvectors.** Fourier characters `chi_{a,b}(x,y) = omega^{ax+by}`
are NOT eigenvectors of W. The shear maps act as **frequency shifts**:
`T_1*` maps `(a,b) -> (a, 2a+b)`. Verified numerically at n=7.

**DFT shift property.** If `g(v) = f(Mv + b)`, then
`g_hat(alpha) = omega^{<(M^-1)^T alpha, b>} . f_hat((M^-1)^T alpha)`.

**Key identity:** `|1 + omega^a| = 2|cos(pi*a/n)|` (`abs_one_add_ω` in `DFT.lean`).

**Fourier-domain shears (dual of spatial shears):**
- `S₁ = M_1^{-T} = [[1,0],[-2,1]]`: preserves `α₂`, shifts `α₁` by `-2α₂`
- `S₂ = M_2^{-T} = [[1,-2],[0,1]]`: preserves `α₁`, shifts `α₂` by `-2α₁`

**Diamond partial order:** `a(x) = min(x, n-x)` (`zmodDist` in code) gives distance to 0 in `Z/nZ`.
Diamond = `{α : a(α₁) + a(α₂) ≤ n/2}`.
Partial order: `α > β` iff `a(α₁) ≥ a(β₁)` and `a(α₂) ≥ a(β₂)` with at least one strict.

**Where `5√2` comes from:** With `ψ = √2`, inside the diamond,
the tight case has 3 neighbors farther from origin and 1 closer, giving
`ψ` sum = `3·(1/√2) + √2 = 3√2/2 + √2 = 5√2/2`. This is exactly tight.

## Lemma Status

| Lemma | Status | File |
|-------|--------|------|
| `mgg n : RegularGraph` | ✅ | `Defs.lean` |
| `mgg_rot_involution` | ✅ | `Defs.lean` |
| `ω_isPrimitiveRoot` | ✅ | `DFT.lean` |
| `char_ortho_1d` / `char_ortho_2d` | ✅ | `DFT.lean` |
| `parseval_2d` | ✅ | `DFT.lean` |
| `corr_pair1` / `corr_pair2` | ✅ | `DFT.lean` |
| `abs_one_add_ω` | ✅ | `DFT.lean` |
| `dft2d_zero` | ✅ | `DFT.lean` |
| `sum_reindex_xy` | ✅ | `WalkExpansion.lean` |
| `mgg_sum_invol` | ✅ | `WalkExpansion.lean` |
| `mgg_walkCLM_inner_eq_corr` | ✅ | `WalkExpansion.lean` |
| `shearS1Fin_bijective` / `shearS2Fin_bijective` | ✅ | `Young.lean` |
| `pointwiseCondition_forall` | ✅ | `Young.lean` |
| `young_assembly` | ✅ | `Young.lean` |
| `diamond_no_both_S2_closer` / `S1` | ✅ | `Young.lean` |
| `diamond_psi_bound` | ✅ | `Young.lean` |
| `outside_diamond_psi_bound` | ✅ | `Young.lean` |
| `strict_diamond_closer_*` (6 variants) | ✅ | `Young.lean` |
| `strict_diamond_*_both_eq_implies_*` (2 variants) | ✅ | `Young.lean` |
| `mgg_spectralGap_of_rayleigh_bound` | ✅ | `Spectral.lean` |
| `mgg_dft_bridge` | ✅ | `Spectral.lean` |
| `mgg_rayleigh_bound` | ✅ | `Spectral.lean` |
| `spectralGap_mgg` | ✅ | `Spectral.lean` |

**All lemmas fully proved. No `sorry`s, no errors.**

## Performance Notes

`Young.lean` was optimized to compile at default heartbeats (200K) with no
`set_option maxHeartbeats` overrides. Key technique: per-quadrant base-min resolution
via `Nat.min_eq_left`/`Nat.min_eq_right` before `Nat.min_def`, preventing exponential
`if`-branch blowup in `split_ifs`. Multi-hypothesis theorems use cascaded
`split_ifs` with `(try omega)` for early branch pruning.

## Mathlib Dependencies (all in v4.27.0)

- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` — `Real.cos`, trig identities
- `Mathlib.Analysis.InnerProductSpace.Basic` — Cauchy-Schwarz, inner products
- `Mathlib.Analysis.CStarAlgebra.Matrix` — `toEuclideanCLM`
- `Mathlib.RingTheory.RootsOfUnity.Basic` — `IsPrimitiveRoot`
- `Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar` — `Complex.isPrimitiveRoot_exp`
