# References

This formalization is based on the following sources:

## Primary Source

**Ajtai, M., Komlós, J., and Szemerédi, E.** (1983). "An O(n log n) sorting network."
*Proceedings of the fifteenth annual ACM symposium on Theory of computing (STOC '83)*, pp. 1-9.
- [ACM Digital Library](https://dl.acm.org/doi/10.1145/800061.808726)
- [Semantic Scholar](https://www.semanticscholar.org/paper/An-0(n-log-n)-sorting-network-Ajtai-Komlos/a3c49750cb342fffc26d1bf95235ac6c64ca0cc0)
- [ResearchGate PDF](https://www.researchgate.net/publication/221590321_An_On_log_n_Sorting_Network)

**Key Contribution:** First construction of an O(n log n) size, O(log n) depth sorting network, using ε-halvers built from expander graphs.

## Expander Graph Construction

**Reingold, O., Vadhan, S., and Wigderson, A.** (2002). "Entropy waves, the zig-zag product, and new constant-degree expanders."
*Annals of Mathematics*, 155(1), 157-187.
- [Annals of Mathematics](https://annals.math.princeton.edu/2002/155-1/p05)
- [arXiv:math/0406038](https://arxiv.org/abs/math/0406038) (PDF: https://arxiv.org/pdf/math/0406038)
- [McGill PDF](https://www.math.mcgill.ca/goren/667.2010/Reingold.Vadhan.Wigderson.pdf)

**Key Contribution:** Zig-zag product for constructing expander graphs, providing an explicit construction route that avoids heavy algebraic machinery (Margulis/LPS).

**Spectral Gap Theorem:** If G₁ is an (n, d, λ₁)-graph and G₂ is a (d, d, λ₂)-graph, then the zig-zag product G₁ ⊗z G₂ is an (nd, d², φ(λ₁, λ₂))-graph where:

```
φ(λ₁, λ₂) = (1-λ₂²)λ₁/2 + √((1-λ₂²)²λ₁²/4 + λ₂²)
```

This is the `rvwBound` function in `AKS/RVWBound.lean`. The bound is tight (achieved by tensor products of complete graphs).

## Educational Resources

These lecture notes provide accessible explanations of the AKS construction:

1. **Chvátal, V.** "Lecture Notes on the AKS Sorting Network." Concordia University.
   [PDF](https://users.encs.concordia.ca/~chvatal/notes/aks.pdf)

2. **Cambridge Advanced Algorithms Course.** "A Glimpse at the AKS Network."
   [PDF](https://www.cl.cam.ac.uk/teaching/1415/AdvAlgo/lec2_ann.pdf)

3. **Buss, S.** "Math 262A Lecture Notes - Sorting Networks." UCSD.
   [PDF](https://mathweb.ucsd.edu/~sbuss/CourseWeb/Math262A_2013F/Scribe15.pdf)

## Related Work

**Goodrich, M. T.** (2014). "Zig-zag Sort: A Simple Deterministic Data-Oblivious Sorting Algorithm Running in O(n log n) Time."
*arXiv:1403.2777*
- [arXiv](https://arxiv.org/abs/1403.2777)

**Key Contribution:** Simplified AKS-style sorting with much better constant factors, making the approach more practical.

---

## Proof Architecture

Our formalization follows this structure:

1. **Comparator networks and 0-1 principle** (`AKS/Basic.lean`)
   - Based on standard results from Knuth TAOCP Vol. 3

2. **Expander graphs via zig-zag product** (`AKS/ZigZag/Expanders.lean`, `AKS/ZigZagOperators.lean`, `AKS/ZigZagSpectral.lean`)
   - Following Reingold–Vadhan–Wigderson (2002)

3. **ε-halvers from expanders** (`AKS/Halver.lean`)
   - Following AKS (1983)
   - **Definition:** An ε-halver is a comparator network that, for any 0-1 input, ensures the excess of 1s in the top half (beyond fair share) is at most ε·(n/2)

4. **Halver composition** (`AKS/Halver.lean` - `halver_composition` theorem)
   - **Status:** Proof structure in place, final gap remains
   - **Gap:** Connecting halver property (ones distribution) to displacement bound
   - **Need:** Access to original AKS proof or educational resource that explains this step

5. **Recursive AKS construction** (`AKS/Basic.lean`)
   - Following AKS (1983)

---

## AKS (1983) Proof Technique — Detailed Analysis

### Key Definitions from Original Paper

**ε-nearsorted** (AKS Section 4, p.5): A permutation π of (1,...,m) is ε-nearsorted if for all initial segments S = (1,...,k) and endsegments S = (k,...,m):
- |S - πS^ε| < ε|S|

Where **S^ε is the "blown-up set"**:
- S^ε = {j ∈ [m] | |j-i| ≤ εm for some i ∈ S}

**Critical difference**: Their definition allows elements to be *within εm distance* of where they should be, not just counting displaced positions.

**ε-halved** (AKS Section 3, p.4): A permutation π is ε-halved if:
- For any initial segment S = (1,...,k), k ≤ m/2: at most ε|S| elements have πᵢ > m/2
- For any endsegment S = (k,...,m), k > m/2: at most ε|S| elements have πᵢ ≤ m/2
- "The two halves have very few errors and they are mostly concentrated in the middle"

### Construction of ε-nearsort (NOT single ε-halver)

**AKS Section 4, p.5-6:** ε-nearsort is constructed by:
1. Apply ε₁-halver to entire set (where ε₁ < ε/log⁴ — much smaller!)
2. Recursively apply ε₁-halvers to top/bottom halves
3. Continue to quarters, eighths, sixteenths...
4. Stop when pieces have size w < εm

**Key insight**: "This will enable us to obtain, by repeated applications of ε-nearsort, an **exponential decay of errors**."

### The Actual Proof (Section 8, p.7-9)

**Tree-based wrongness measure** Δᵣ(J):
- For interval J at some tree node, Δᵣ(J) = proportion of elements in J that belong at tree-distance ≥ r
- More precisely: find all sections L(K) or U(K) at distance ≥ r from J, count |R(J) ∩ L(K)| or |R(J) ∩ U(K)|, divide by |J|

**Main Theorem** (p.7): After every completed cycle:
1. Δᵣ < α^(3r+40), r ≥ 1
2. δ < α^30 (where δ = |R(J) - J|/|J|, simple displacement)

**Proof via 4 Lemmas**:

**Lemma 1** (register reassignment): Δ'ᵣ < 6AΔᵣ₋₄, δ' < 6A(δ+ε)
- Bookkeeping step increases wrongness as intervals split

**Lemma 2** (single Zig or Zag): Δ'ᵣ < 8A(Δᵣ + εΔᵣ₋₂), δ' < 4A(δ+ε)
- **Key mechanism** (p.8): "Most elements belonging to L will be forced to the left... The number of exceptional elements cannot exceed ε proportion"
- ε-nearsort forces elements toward correct side, exceptions bounded by ε

**Lemma 3** (ZigZag combined): Δ'ᵣ < 64A²(Δᵣ₊₁ + 3εΔᵣ₋₄), δ' < 16A²(δ+2ε)
- **Crucial observation** (p.8): "If an interval J was closest to L in the Zig step, then it will not be a nearest one in the Zag step. Thus... errors will strictly decrease."
- Alternation ensures elements don't get stuck

**Lemma 4** (displacement from wrongness): δ < 10(Δε + Σᵣ>₁(4A)ʳΔᵣ) < α^30
- **Equation (4), p.8-9**: Connects displacement to sum over all wrongness levels:
  - x₃ < |J|(Δ₁ + Σᵣ≥₁ 2^(2r+1)ΔᵣΔ'ᵣ)
- Elements from wrong levels accumulate at fringes, get pushed up tree

### Why Geometric Decrease Works

1. **Fringes concentrate errors**: ε-nearsort pushes misplaced elements to edges (≤ ε fraction)
2. **Tree structure**: Elements at wrong level move **up** to parent node in next cycle
3. **Alternating Zig-Zag**: Prevents elements from getting stuck at distance 1
4. **Wrongness decreases**: Δᵣ₊₁ contributes to Δ'ᵣ with coefficient 3ε (small!), so geometric decay

### Implications for Our Formalization

**Critical finding**: AKS doesn't prove "single ε-halver improves sortedness." Instead:
- They use **ε-nearsort** (recursive structure with many ε₁-halvers, ε₁ << ε)
- Geometric decrease requires the **tree structure** and **alternating steps**
- Their ε-sorted definition (blown-up sets) differs from ours (displacement count)

**Our `halver_composition` theorem** may need:
1. Different proof approach (not direct single-halver application), OR
2. Reformulation to use ε-nearsort instead of ε-halver, OR
3. Bridge lemma connecting their blown-up-set definition to our displacement definition

---

## TODO

- [ ] Add citation comments to relevant theorems in the codebase
- [ ] Verify `IsEpsilonSorted` definition matches AKS (1983)
- [ ] Document the halver composition proof technique once identified
- [ ] Add links to this file from main code files
