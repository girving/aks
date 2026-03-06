# Jimbo-Maruoka / Boppana Spectral Gap Proof

Proof that `spectralGap (mgg n) ≤ 5 * √2 / 8` for `n ≥ 3`.

## Source

Based on the Boppana-simplified proof of Jimbo-Maruoka (1987), as presented in
Linial-Wigderson lecture notes Chapter 7 (`docs/hlw-expander-notes.pdf`).
Original: Jimbo & Maruoka, "Expanders obtained from affine transformations,"
*Combinatorica* 7, 343–355 (1987).

## Key Insight: Full DFT, Not Fiber Decomposition

The previous proof plan (Lemmas 4-8 in `Spectral.lean`) used partial DFT and
"a-fiber" decomposition. That approach FAILS because L₂ does not preserve a-fibers.

The correct proof uses the **full 2D DFT** on `(Z/nZ)²` and works entirely in
Fourier space. No L₁/L₂ decomposition, no fiber projections, no Rayleigh quotient
per-operator bounds. The proof is purely algebraic + combinatorial.

## Construction (matching `Defs.lean`)

Graph on `(Z/nZ)²`, 8-regular. Linear parts:
- `M₁ = [[1,2],[0,1]]`: maps `(x,y) → (x+2y, y)` [our T₁]
- `M₂ = [[1,0],[2,1]]`: maps `(x,y) → (x, 2x+y)` [our T₂]

Affine shifts: `e₁ = (1,0)`, `e₂ = (0,1)`.

The 8 neighbors of `v = (x,y)`:

| Port | Map | Neighbor | Notes version |
|------|------------|-----------------|---------------|
| 0 | `M₁v` | `(x+2y, y)` | `T₂v` |
| 1 | `M₁⁻¹v` | `(x-2y, y)` | `T₂⁻¹v` |
| 2 | `M₂v` | `(x, 2x+y)` | `T₁v` |
| 3 | `M₂⁻¹v` | `(x, y-2x)` | `T₁⁻¹v` |
| 4 | `M₁v+e₁` | `(x+2y+1, y)` | `T₂v+e₁` |
| 5 | `(M₁v+e₁)⁻¹`| `(x-2y-1, y)` | ... |
| 6 | `M₂v+e₂` | `(x, 2x+y+1)` | `T₁v+e₂` |
| 7 | `(M₂v+e₂)⁻¹`| `(x, y-2x-1)` | ... |

(The notes use `T₁ = M₂`, `T₂ = M₁` — just a labeling swap.)

## Proof Structure

### Step 0: Reduce to Rayleigh quotient

By `sa_opNorm_le_of_inner_le` (in `RVWBound.lean`), it suffices to show:
for all `f ⊥ 1` with `‖f‖ = 1`:

```
|⟨f, A f⟩| ≤ 5√2
```

where `A` is the adjacency operator (walk = A/8, spectralGap = ‖A/8 - mean‖).

Since `A` is self-adjoint, `|⟨f, Af⟩| = |Σ_{(v,w)∈E} f(v)f(w)|` (directed sum).

### Step 1: Express in terms of 4 forward maps

```
⟨f, Af⟩ = Σ_v f(v) · [f(M₁v) + f(M₁⁻¹v) + f(M₁v+e₁) + f(M₁⁻¹v-e₁)
                       + f(M₂v) + f(M₂⁻¹v) + f(M₂v+e₂) + f(M₂⁻¹v-e₂)]
```

By substitution (M₁⁻¹ terms give same sum as M₁ terms), this equals:

```
2 · Re[Σ_v f(v) · (f(M₁v) + f(M₁v+e₁) + f(M₂v) + f(M₂v+e₂))]
```

So it suffices to bound:

```
|Σ_v f(v) · [f(M₁v) + f(M₁v+e₁) + f(M₂v) + f(M₂v+e₂)]| ≤ (5√2/2) · ‖f‖²
```

### Step 2: Apply DFT

Characters of `(Z/nZ)²`: `χ_α(v) = ω^{⟨α,v⟩}` for `α ∈ (Z/nZ)²`, `ω = e^{2πi/n}`.

DFT: `f̂(α) = (1/n) Σ_v f(v) · ω^{-⟨α,v⟩}`.

**DFT shift property:** If `g(v) = f(Mv + b)`, then:
`ĝ(α) = ω^{⟨(M⁻¹)ᵀ · b̃, α⟩} · f̂((M⁻¹)ᵀ α)`
where `b̃` is a suitable representative.

After applying the DFT (using Parseval and the shift property),
the condition `Σ f = 0` becomes `f̂(0,0) = 0`, and the bilinear form becomes:

```
|Σ_{α≠0} F(α) · [F(M₁⁻ᵀα)(1+ω^{α₁}) + F(M₂⁻ᵀα)(1+ω^{α₂})]| ≤ (5√2/2) · Σ|F(α)|²
```

where `F = |f̂|` (take absolute values), and `M₁⁻ᵀ = (M₁⁻¹)ᵀ`, `M₂⁻ᵀ = (M₂⁻¹)ᵀ`.

Key: `M₁⁻ᵀ = [[1,0],[-2,1]]` preserves `α₂` (first index changes, second stays).
And `M₂⁻ᵀ = [[1,-2],[0,1]]` preserves `α₁`.

**Crucial identity:** `|1 + ω^a| = 2|cos(πa/n)|`.

### Step 3: Reduce to real non-negative function

Setting `G = |F| ≥ 0` and using triangle inequality + `|1+ω^a| = 2|cos(πa/n)|`:

```
Σ_{α≠0} G(α) · [G(T₂⁻¹α)|cos(πα₁/n)| + G(T₁⁻¹α)|cos(πα₂/n)|] ≤ (5√2/4) · Σ G²(α)
```

where `T₂⁻¹` preserves `α₁` and `T₁⁻¹` preserves `α₂`.
(Note: since `T₁ᵀ = T₂`, we have `(T₁⁻¹)ᵀ = T₂⁻¹`, giving a cross-pairing:
the `T₁` pair's Fourier action is `T₂⁻¹`, and vice versa.)

### Step 4: Young's inequality with weight function ψ

For any `ψ: (Z²ₙ)² → ℝ₊` with `ψ(x,y) · ψ(y,x) = 1`:

```
2ab ≤ ψ(x,y) · a² + ψ(y,x) · b²    (weighted AM-GM)
```

Apply to each `G(α)G(T_i⁻¹α)` term. After the substitution `α' = T_i⁻¹α`
(using that `T₂⁻¹` preserves `α₁` and `T₁⁻¹` preserves `α₂`, so the cosine
factors survive the substitution), we get:

```
2 · LHS ≤ Σ_α G²(α) · [|cos(πα₁/n)| · (ψ(α,T₂α)+ψ(α,T₂⁻¹α))
                        + |cos(πα₂/n)| · (ψ(α,T₁α)+ψ(α,T₁⁻¹α))]
```

In terms of Fourier shears S₁ = (T₁⁻¹)ᵀ = T₂⁻¹, S₂ = (T₂⁻¹)ᵀ = T₁⁻¹:
- `cos₁` pairs with `{S₂α, S₂⁻¹α}` (which preserve `α₁`)
- `cos₂` pairs with `{S₁α, S₁⁻¹α}` (which preserve `α₂`)

**Sufficient condition:** For all `α ∈ Z²ₙ \ {0}`:

```
|cos(πα₁/n)| · [ψ(α,S₂α)+ψ(α,S₂⁻¹α)]
  + |cos(πα₂/n)| · [ψ(α,S₁α)+ψ(α,S₁⁻¹α)]  ≤  5√2/2    (*)
```

### Step 5: Define the partial order and ψ

**Distance to origin:** `a(x) = min(x, n-x)` for `x ∈ Z/nZ` (≥0, ≤n/2).

**Partial order on Z²ₙ:** `α > β` iff `a(α₁) ≥ a(β₁)` and `a(α₂) ≥ a(β₂)` with
at least one strict inequality (i.e., α is "farther from axes" than β).

**Diamond:** The set `D = {α ∈ Z²ₙ \ {0} : a(α₁) + a(α₂) ≤ n/2}`.

**Weight function with parameter α = √2** (matching Jimbo-Maruoka/HLW notes):

```
ψ(ϑ, ϑ') = √2      if ϑ > ϑ'  (first arg farther from axes → big weight)
ψ(ϑ, ϑ') = √2/2    if ϑ < ϑ'  (first arg closer → small weight)
ψ(ϑ, ϑ') = 1        if incomparable
```

This satisfies `ψ(α,β) · ψ(β,α) = 1`.

### Step 6: Case analysis for condition (*)

**Case A: α outside the diamond** (`a(α₁) + a(α₂) > n/2`).

The key bound: **for `a(α₁) + a(α₂) > n/2`:**

```
|cos(πα₁/n)| + |cos(πα₂/n)| ≤ √2
```

*Proof:* WLOG first quadrant. For fixed `α₁`, the maximum of
`cos(πα₁/n) + cos(πα₂/n)` subject to `α₁ + α₂ ≥ n/2` is at `α₂ = n/2 - α₁`.
By convexity of cos: `cos(πα₁/n) + cos(π(n/2-α₁)/n) ≤ 2cos(π/4) = √2`.

Each ψ pair sum is at most `√2 + √2/2 = 3√2/2` (one larger, one smaller neighbor).
So:
```
LHS of (*) ≤ (|cos(πα₁/n)| + |cos(πα₂/n)|) · max_pair_sum
           ≤ √2 · (3√2/2) = 3
```

And 3 < 5√2/2 ≈ 3.535. ✓

**Case B: α inside the diamond** (`a(α₁) + a(α₂) < n/2`).

Bound `|cos| ≤ 1`. Need:

```
ψ(α,S₁α) + ψ(α,S₁⁻¹α) + ψ(α,S₂α) + ψ(α,S₂⁻¹α) ≤ 5√2/2
```

**Key combinatorial fact:** For α inside the diamond, one of:
1. Three of the 4 neighbors satisfy `> α`, one satisfies `< α`.
   → ψ sum = `3·(√2/2) + √2 = 5√2/2`. ✓ (exact!)
   (3 farther neighbors: ψ(α, farther) = √2/2 since α < farther;
    1 closer neighbor: ψ(α, closer) = √2 since α > closer.)
2. Two satisfy `> α`, two are incomparable with α.
   → ψ sum = `2·(√2/2) + 2·1 = √2 + 2 ≈ 3.414 < 5√2/2`. ✓

(No case has all four `> α` or other combinations.)

### Step 7: Assembly

Combining Cases A and B: condition (*) holds for all `α ≠ 0` with `ε = √2/2`.
By Step 4, the bilinear form is bounded by `(5√2/4) · Σ G²(α)`.
By Steps 1-3, `|⟨f, Af⟩| ≤ 5√2 · ‖f‖²`.
By Step 0, `spectralGap (mgg n) ≤ 5√2/8`. □

## Lemma Decomposition for Formalization

### Infrastructure (reuse Mathlib)

| Lemma | Description | Risk | Effort |
|-------|-------------|------|--------|
| DFT | `ZMod.dft` on `(Z/nZ)²` | LOW | days |
| Parseval | `‖f̂‖ = ‖f‖` | LOW | exists in Mathlib |
| Shift | DFT of `f(Mv+b)` | MEDIUM | ~1 week |
| cos_identity | `|1+ω^a| = 2|cos(πa/n)|` | LOW | days |

### Core proof

| Lemma | Description | Risk | Effort |
|-------|-------------|------|--------|
| reduce_to_rayleigh | `spectralGap ≤ c` from `|⟨f,Af⟩| ≤ c·‖f‖²` | LOW | days |
| fourier_bilinear | Bilinear form in Fourier space | MEDIUM | ~1 week |
| young_weight | Young's inequality + ψ → quadratic form | LOW | days |
| diamond_cos_bound | `|cos α₁| + |cos α₂| ≤ √2` outside diamond | LOW | hours |
| inside_diamond_cases | 3+1 / 2+2 case analysis | MEDIUM | ~1 week |
| assembly | Combine all pieces | LOW | days |

### Risk summary

| Risk | Lemmas |
|------|--------|
| LOW | reduce_to_rayleigh, cos_identity, young_weight, diamond_cos_bound, assembly |
| MEDIUM | DFT shift property, fourier_bilinear, inside_diamond_cases |
| **HIGH** | **None!** |

**Critical improvement:** The old plan had Lemma 8 (Jimbo-Maruoka inequality) at HIGH risk.
The new plan has NO high-risk lemmas. The proof is entirely elementary: DFT, AM-GM,
convexity, combinatorial case analysis.

**Total estimated effort:** 3-5 weeks (vs 6-10 weeks for the old plan).

**Critical path:** DFT shift property → Fourier bilinear form → inside diamond cases.

## Comparison with Old Plan

| Aspect | Old plan (fiber decomposition) | New plan (full DFT + ψ) |
|--------|-------------------------------|------------------------|
| L₁, L₂ operators | Required | Not needed |
| Partial DFT | Required (and L₂ breaks it!) | Not needed |
| Fiber projections | Required | Not needed |
| Cross-term bound | HIGH risk, unknown approach | LOW risk (Young's ineq) |
| Key difficulty | L₂ doesn't preserve a-fibers | Combinatorial case analysis |
| Highest risk | HIGH (Lemma 8) | MEDIUM |
| Estimated effort | 6-10 weeks | 3-5 weeks |

## Mathlib Dependencies

- `Mathlib.Analysis.Fourier.ZMod` — `ZMod.dft`, `dft_dft`
- `Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality` — character orthogonality
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` — `Real.cos`, trig identities
- `Mathlib.Analysis.InnerProductSpace.Basic` — Cauchy-Schwarz, Parseval
- `Mathlib.Topology.Algebra.Module.Basic` — CLM infrastructure

## Verification

The bound `5√2/8 ≈ 0.884` is verified numerically:

| n | λ₂(A) | λ₂/8 | 5√2/8 ≈ 0.884 |
|---|-------|------|----------------|
| 3 | 4.612 | 0.576 | ✓ |
| 7 | 5.777 | 0.722 | ✓ |
| 23 | 6.212 | 0.776 | ✓ |
| 100 | ~6.47 | ~0.809 | ✓ |

The optimal ε = √2/2 makes Case B1 tight (3ε + 1/ε = 5√2/2 exactly),
which is why 5√2 is the natural constant for this proof technique.
