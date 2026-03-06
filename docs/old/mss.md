> **OBSOLETE:** MSS interlacing families approach was rejected; zig-zag products remain the practical route.

# MSS Interlacing Families: Feasibility Analysis

Why the Marcus-Spielman-Srivastava (2013/2015) interlacing families method for
constructing Ramanujan graphs is not a practical alternative to zig-zag products
for this formalization.

## Background

MSS proved existence of bipartite Ramanujan graphs of every degree ≥ 3, achieving
optimal spectral gap (eigenvalues bounded by 2√(d−1)). The zig-zag product used
in this project gives only a constant spectral gap — but AKS sorting networks
need only a constant, so optimality is irrelevant here.

### How MSS works

1. Decompose a base graph's adjacency matrix as a sum of permutation matrices.
2. Consider all 2^m signings (±1 choices) of these matrices.
3. Define the "mixed characteristic polynomial" as the expected characteristic
   polynomial over a random signing.
4. Show this expected polynomial is real-rooted with largest root ≤ 2√(d−1)
   (via properties of real-stable polynomials and the barrier function method).
5. By the interlacing property, at least one signing achieves the bound.

### Is the construction computable?

Yes — the proof can be derandomized into a deterministic poly-time algorithm.
At each step there are finitely many choices, and you can greedily select the one
that keeps the conditional expected polynomial's largest root bounded. This
requires computing characteristic polynomials symbolically and bounding polynomial
roots, both feasible over algebraic numbers.

So MSS gives a computable expander construction, not just an existence proof.
The question is whether it's *formalizable*.

## Why it's intractable for this project

### 1. Computable algebraic numbers don't exist in Mathlib

Mathlib (v4.27.0) has `IsAlgebraic R x : Prop` — a predicate with no
computational content, erased at runtime. The `AlgebraicClosure k` type is in a
`noncomputable section` using `Classical.choose`. There is no `DecidableEq`
instance, no computable arithmetic, no executable representation.

A computable algebraic number type (minimal polynomial + Sturm-chain root
isolation) would need to be built from scratch and proved to form an ordered
field. This is a substantial project on its own.

### 2. Real-rooted polynomial theory is entirely absent from Mathlib

A thorough search of Mathlib v4.27.0 found zero results for:

| Concept | Mathlib status |
|---|---|
| Real-rootedness predicate | absent |
| Polynomial interlacing | absent (0 files match `interlac`) |
| Real-stable polynomials | absent |
| Hyperbolic polynomials | absent |
| Common interlacing | absent |
| Mixed characteristic polynomials | absent |
| Barrier / potential functions | absent |
| Log-concavity of polynomials | absent |

What Mathlib *does* have as building blocks:
- `Polynomial.roots` (multiset of roots, noncomputable)
- `Polynomial.Splits` (splits over a field)
- `Polynomial.RuleOfSigns` (Descartes' rule, proved)
- `GaussLucas` (roots of derivative in convex hull of roots, proved 2025)
- `Polynomial.cauchyBound` (norm bound on roots)
- Full spectral theorem for Hermitian matrices

The gap isn't a few missing lemmas — it's an entire subfield that would need to
be developed: definitions, closure properties (convex combinations, derivatives,
rank-1 perturbations), the interlacing partial order, and the barrier function
argument.

### 3. The barrier function argument needs real analysis

The core of MSS is showing the expected characteristic polynomial has bounded
roots. This uses a "barrier function" (sum of 1/(λ − rᵢ) over roots rᵢ) and
argues about its poles and monotonicity. Formalizing this requires:

- Meromorphic function theory on ℝ (poles, residues)
- Careful limits around singularities
- The connection between barrier function zeros and polynomial root bounds

Mathlib has some real analysis infrastructure, but the specific barrier function
argument would be novel formalization work.

### 4. Total formalization cost estimate

| Component | Estimated effort | Mathlib coverage |
|---|---|---|
| Computable algebraic numbers | 6–12 months | none |
| Real-rooted polynomial theory | 3–6 months | none |
| Interlacing relations + closure | 2–4 months | none |
| Barrier function argument | 2–4 months | partial (real analysis exists) |
| Mixed characteristic polynomial | 1–2 months | none |
| Derandomized algorithm correctness | 2–4 months | none |
| **Total** | **~16–32 months** | |

Compare with the zig-zag product approach: the spectral analysis is fully proved,
the base expander is certified, and the remaining work is assembling existing
components. Zig-zag required ~6 months of spectral infrastructure that is now
done.

### 5. The certificate workaround doesn't help much

One might try: run the MSS greedy algorithm externally, output the explicit graph,
verify its spectral gap in Lean via eigenvalue certification (like the `CertCheck`
pipeline). But MSS is needed at *every* level of the iterated construction, not
just the base — you'd need certificates for graphs at every size the sorting
network requires. The zig-zag product avoids this by being compositional: prove
the spectral bound once, apply it inductively.

## Comparison with zig-zag

| Aspect | Zig-zag (this project) | MSS interlacing |
|---|---|---|
| Spectral gap quality | constant (sufficient) | optimal Ramanujan |
| Construction type | combinatorial | algebraic |
| Key infrastructure | operator norms, C*-algebra | real-rooted polynomials |
| Compositionality | inductive (square → zig-zag) | per-level greedy search |
| Mathlib readiness | high (spectral theorem, CLMs) | very low |
| Formalization status here | spectral bound proved | not attempted |

## Conclusion

MSS is a beautiful result that gives stronger expanders than zig-zag. But for
formalization of AKS sorting networks, it would require building ~2 years of
foundational infrastructure (computable algebraic numbers, real-rooted polynomial
theory, interlacing, barrier functions) to gain an improvement (optimal vs.
constant spectral gap) that the application doesn't need. The zig-zag approach
was chosen precisely because it avoids heavy algebraic machinery — this was the
original insight of Reingold-Vadhan-Wigderson (2002).

## References

- Marcus, Spielman, Srivastava. "Interlacing Families I: Bipartite Ramanujan
  Graphs of All Degrees." *Annals of Mathematics* 182(1), 2015.
- Marcus, Spielman, Srivastava. "Interlacing Families II: Mixed Characteristic
  Polynomials and the Kadison-Singer Problem." *Annals of Mathematics* 182(1), 2015.
- Reingold, Vadhan, Wigderson. "Entropy Waves, the Zig-Zag Graph Product, and
  New Constant-Degree Expanders." *Annals of Mathematics* 155(1), 2002.
