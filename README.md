# AKS Sorting Network — Lean Formalization (work in progress)

An attempt to formally verify the Ajtai--Komlos--Szemeredi (1983) `O(n log n)` sorting network construction in Lean. The proof is incomplete: many theorems have `sorry` placeholders. The codebase is a structural skeleton demonstrating the proof architecture, not a finished formalization.

## Resources

- **[Proof dependency graph](https://girving.github.io/aks/)** — Interactive visualization (green = proved, orange = sorry'd)
- **[References](REFERENCES.md)** — Papers and educational materials
- **[CLAUDE.md](CLAUDE.md)** — Development guide for Claude Code

## Status

The top-level goal is to prove:

- `AKS.size_nlogn` : The network has size `O(n log n)` — **sorry'd**
- `AKS.sorts` : The network correctly sorts all inputs — **sorry'd**

These depend on substantial unfinished work, including the tree-based sorting correctness argument (`TreeSorting.lean`) and the AKS construction itself (`AKSNetwork.lean`).

### What is proved

- **Expander mixing lemma** (`Mixing.lean`) — fully proved
- **Zig-zag graph product** (`ZigZagOperators.lean`, `ZigZagSpectral.lean`) — operator definitions and algebraic identities (0 `sorry`'s)
- **Spectral gap composition** (`ZigZag.lean`) — `zigzag_spectral_bound` assembled from sublemmas
- **Graph squaring** (`Square.lean`) — `spectralGap_square`: `λ(G²) = λ(G)²`
- **Complete graph spectral gap** (`CompleteGraph.lean`) — `spectralGap_complete`: `λ(K_{n+1}) = 1/n`
- **Expander-to-halver bridge** (`Halver.lean`) — `expander_gives_halver` fully proved
- **0-1 principle** (`ComparatorNetwork.lean`) — `zero_one_principle` fully proved

### What is not proved

- **RVW operator bound** (`RVWBound.lean`) — 2 `sorry`'s in the core quadratic inequality
- **Base expander certificate** (`CertificateBridge.lean`) — sorry'd bridge from checker to spectral gap
- **Tree-based AKS correctness** (`TreeSorting.lean`) — 4 `sorry`'s remaining; 2 correctly stated (`halvers_give_bounded_nearsort`, `aks_tree_sorting`), 2 need reformulation (see [`docs/treesorting-audit.md`](docs/treesorting-audit.md))
- **AKS construction and size bound** (`AKSNetwork.lean`) — sorry'd

## Setup

Requires [elan](https://github.com/leanprover/elan) (Lean), [rustup](https://rustup.rs/) (Rust), and optionally [uv](https://github.com/astral-sh/uv) (Python scripts).

**Linux (Ubuntu/Debian):**
```bash
curl https://elan.dev/install.sh -sSf | sh
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh  # system cargo is too old
curl -LsSf https://astral.sh/uv/install.sh | sh  # optional
```

**macOS:**
```bash
brew install elan-init rust uv
```

Restart your shell after installing.

## Proof Architecture

1. **Comparator networks and 0-1 principle** (`ComparatorNetwork.lean`)
2. **Regular graphs, spectral gap, squaring** (`RegularGraph.lean`, `Square.lean`, `CompleteGraph.lean`)
3. **Zig-zag product and spectral analysis** (`ZigZagOperators.lean`, `ZigZagSpectral.lean`, `RVWBound.lean`)
4. **Expander families** (`ZigZag.lean`, `Random.lean`)
5. **Expander mixing lemma** (`Mixing.lean`)
6. **`ε`-halvers from expanders** (`Halver.lean`)
7. **Tree-based sorting correctness** (`TreeSorting.lean`)
8. **AKS construction** (`AKSNetwork.lean`)

See [REFERENCES.md](REFERENCES.md) for detailed citations and proof strategy documentation.
