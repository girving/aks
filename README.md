# AKS sorting network — Lean formalisation

A formal verification of the Ajtai–Komlós–Szemerédi (1983) `O(n log n)` sorting network
construction in [Lean 4](https://lean-lang.org/) with
[Mathlib](https://github.com/leanprover-community/mathlib4), using the Seiferas (2009)
separator-based correctness proof and the Margulis–Gabber–Galil (1973/1981) expander.
All code and proofs were written by Claude Code + Claude Opus 4.6, with extensive human
hand-holding throughout.

The toplevel results in [`AKS/Seiferas.lean`](AKS/Seiferas.lean) are:

```lean4
/-- Seiferas's network for large `n`, bitonic sort for small `n` -/
def network (n : ℕ) : ComparatorNetwork n :=
  ...  -- Here be dragons 🐉

/-- We correctly sort all inputs -/
theorem network_sorts (n : ℕ) : (network n).Sorts

/-- Our network has `O(log n)` depth -/
theorem network_depth_le (n : ℕ) :
    (network n).depth ≤ 141 * 10 ^ 62 * Nat.clog 2 n

/-- Our network has `O(n log n)` size -/
theorem network_size_le (n : ℕ) :
    (network n).size ≤ 705 * 10 ^ 61 * n * Nat.clog 2 n
```

The sorting network is a computable `def`, and the gate structure is computable in polylog parallel
depth ([NC](https://en.wikipedia.org/wiki/NC_(complexity))), though we do not yet prove this.

## Proof outline

The construction follows three papers:

1. **Ajtai, Komlós, Szemerédi** (1983): the original construction showing that
   expander-based ε-halvers yield `O(log n)`-depth sorting networks.

2. **Seiferas** (2009): replaces the AKS tree-distance wrongness argument with
   (γ,ε)-separators and a single potential function (stranger counting in a bag tree),
   giving a cleaner correctness proof.

3. **Margulis** (1973) / **Gabber–Galil** (1981): an explicit 8-regular expander on
   (ℤ/nℤ)² with spectral gap ≤ 5√2/8. We use this as the base expander, avoiding both
   the zig-zag product's base certificate requirements and the heavy algebraic machinery
   of Margulis/LPS Ramanujan graphs.

The key proof path is:

```
MGG expander → repeated squaring → ε-halvers (via Tanner bound + expander mixing lemma)
    → (γ,ε)-separators (prefix-doubling) → bag-tree sorting → O(log n) depth
```

Batcher's bitonic sort ([`Bitonic/`](AKS/Bitonic/)) handles inputs smaller than 1024,
and is used as a finish-up step after bag-tree sorting.

## Depth constants

The depth bound is `(network n).depth ≤ C · ⌈log₂ n⌉` where C is a computable constant.
The current value is astronomically large:

1. **6 March 2026**: C ≈ 1.41 × 10⁶⁴ (initial proof, unoptimised MGG path)

The large constant comes from **repeated graph squaring**: the MGG expander has spectral
gap ≤ 5√2/8 ≈ 0.884, which is too weak for direct use as a halver. We square the graph
6 times to bring the gap below the ε threshold, producing a graph of degree
8^(2⁶) = 8⁶⁴ ≈ 6.3 × 10⁵⁷. The halver depth scales with this degree.
Better base expanders or tighter spectral bounds would dramatically reduce C.

## Contributions welcome

There are several paths to improving the constant:

- Better spectral gap bound for MGG (the 5√2/8 bound is loose)
- Fewer squarings via a tighter Tanner bound or better ε parameters
- Optimising the Seiferas parameters (γ, ε, ν, A)
- Paterson's (1990) construction achieves depth < 6100 log n; Seiferas claims ~49 log n

Other extensions:

- Proving the construction is in [NC](https://en.wikipedia.org/wiki/NC_(complexity)) (polylog parallel depth, polynomial work)

## Directory structure

```
AKS/                    Main formalisation (68 Lean files)
  Seiferas.lean         Top-level assembly: network, network_sorts, network_depth_le
  Sort/                 Comparator networks, 0-1 principle, monotonicity
  Bitonic/              Batcher's bitonic sort (small inputs)
  Graph/                Regular graphs, spectral gap, squaring, contraction
  MGG/                  Margulis–Gabber–Galil 8-regular expander
  Halver/               ε-halvers: Tanner bound, expander mixing, MGG→halver bridge
  Separator/            (γ,ε)-separators: prefix-doubling construction from halvers
  Bags/                 Bag-tree sorting: network, sizes, stranger bounds, depth
  ZigZag/               Zig-zag product, RVW inequality (not used in main path)
  Konig/                König's theorem (matching for scatter embedding)
  Misc/                 Fin arithmetic helpers
Random/                 Base expander certificates (optional, not needed for main proof)
docs/                   Papers, design docs, proof visualisation
scripts/                Build helpers, sorry audit, visualisation updater
rust/                   Empirical testing of theorem statements
```

## Alternative path: zig-zag product with certified base expander

The codebase also contains a fully proved **zig-zag product** construction
([`ZigZag/`](AKS/ZigZag/)) following Reingold–Vadhan–Wigderson (2002), with:

- Zig-zag graph product and walk operators ([`ZigZag/Operators.lean`](AKS/ZigZag/Operators.lean))
- RVW spectral bound: fully proved quadratic inequality ([`ZigZag/RVWInequality.lean`](AKS/ZigZag/RVWInequality.lean),
  [`ZigZag/RVWBound.lean`](AKS/ZigZag/RVWBound.lean))
- Iterated zig-zag families with spectral gap bounds ([`ZigZag/Expanders.lean`](AKS/ZigZag/Expanders.lean))

This path requires a **certified base expander** — a specific small graph with a verified
spectral gap. The [`Random/`](Random/) library implements this using
[davidad's triangular-inverse method](https://x.com/davidad/status/2022316806094913669)
for certifying spectral gaps of concrete graphs. The certificate is generated by an
`O(n³)` dense BLAS computation in [Rust](rust/certificate.rs), and the certificate check is `O(n²)` in Lean
via `native_decide` (~100M arithmetic operations for the 65536-vertex, 12-regular graph).

We chose **not** to use this path for the main proof because:

1. **`native_decide` extends the trust boundary.** It introduces the `Lean.ofReduceBool`
   and `Lean.trustCompiler` axioms, trusting Lean's native code generator to correctly
   implement Lean semantics. The MGG path avoids this entirely.
2. **Large certificate data.** The base expander certificate is ~8 GB, requiring C FFI
   (`mmap`) to load efficiently. This is engineering complexity outside the proof.
3. **The MGG expander is simpler.** The MGG construction is a clean mathematical
   definition with a fully formal spectral bound — no external data or native
   evaluation needed.

The certificate infrastructure ([`Random/Cert/`](Random/Cert/), [`Random/Bridge/`](Random/Bridge/), [`Random/Concrete/`](Random/Concrete/))
is fully proved.

## References

- **Ajtai, Komlós, Szemerédi** (1983). "An O(n log n) sorting network."
  *STOC '83*, pp. 1–9.
  [ACM DL](https://dl.acm.org/doi/10.1145/800061.808726)

- **Seiferas** (2009). "A simpler proof that an O(n log n) sorting network sorts in
  O(n log n) time."
  [ACM DL](https://dl.acm.org/doi/10.5555/3118778.3119194)

- **Paterson** (1990). "Improved sorting networks with O(log N) depth."
  *Algorithmica* 5(1), 75–92.
  [Springer](https://doi.org/10.1007/BF01840378)

- **Reingold, Vadhan, Wigderson** (2002). "Entropy waves, the zig-zag product, and new
  constant-degree expanders." *Annals of Mathematics* 155(1), 157–187.
  [arXiv:math/0406038](https://arxiv.org/abs/math/0406038)

- **Margulis** (1973). "Explicit constructions of expanders."
  *Problemy Peredači Informacii* 9(4), 71–80.

- **Gabber, Galil** (1981). "Explicit constructions of linear-sized superconcentrators."
  *JCSS* 22(3), 407–420.
  [ScienceDirect](https://doi.org/10.1016/0022-0000(81)90040-4)

- **Tanner** (1984). "Explicit concentrators from generalized N-gons."
  *SIAM J. Algebraic Discrete Methods* 5(3), 287–293.
  [SIAM](https://doi.org/10.1137/0605030)

- **Batcher** (1968). "Sorting networks and their applications."
  *AFIPS '68*, pp. 307–314.
  [ACM DL](https://doi.org/10.1145/1468075.1468121)

- **Goodrich** (2014). "Zig-zag sort: A simple deterministic data-oblivious sorting
  algorithm running in O(n log n) time."
  [arXiv:1403.2777](https://arxiv.org/abs/1403.2777)

- **Lean 4** — de Moura, Ullrich (2021). "The Lean 4 theorem prover and programming
  language." *CADE-28*.
  [GitHub](https://github.com/leanprover/lean4)

- **Mathlib** — The Mathlib community (2020). "The Lean mathematical library."
  *CPP '20*.
  [GitHub](https://github.com/leanprover-community/mathlib4)

## Setup

Requires [elan](https://github.com/leanprover/elan) (Lean version manager).

```bash
# Linux
curl https://elan.dev/install.sh -sSf | sh

# macOS
brew install elan-init
```

## Building

```bash
lake exe cache get    # Download prebuilt Mathlib oleans (required after clone/clean)
lake build AKS        # Build the core proof
```

**Warning:** `lake build` (without arguments) also builds the `Random` library, which
downloads multi-gigabyte certificates and takes significantly longer. Use
`lake build AKS` to check just the core proof.

```bash
lake build            # Builds AKS + Random (downloads ~8 GB certificate data)
lake build AKS Random # Same as above, explicit
```

## Trusted codebase

The core proof ([`AKS/`](AKS/)) depends only on Lean's standard axioms,
as checked by `#guard_msgs in #print axioms` in [`AKS/Seiferas.lean`](AKS/Seiferas.lean).

[`Challenge.lean`](Challenge.lean) and [`challenge.json`](challenge.json) can be used to
check the proof using [comparator](https://github.com/leanprover/comparator), which
(successfully) reruns the generated proof terms through the Lean checker:

```bash
lake env ~/comparator/.lake/build/bin/comparator challenge.json
```

Alas, the independent verifier [nanoda](https://github.com/ammkrn/nanoda_lib) hits an
error, which I have to trace down (`invalid digit found in string`).

The optional [`Random/`](Random/) library (base expander certificates) additionally uses
`native_decide` and C FFI for loading large certificate data. See
[`docs/trust.md`](docs/trust.md) for the complete trust analysis.

## Resources

- **[Proof dependency graph](https://girving.github.io/aks/)** — Interactive visualisation (not carefully checked)
- **[CLAUDE.md](CLAUDE.md)** — Development guide and accumulated proof tactics
- **[LICENSE](LICENSE)** — Apache 2.0
