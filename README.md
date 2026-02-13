# AKS Sorting Network — Lean 4 Formalization

Formal verification of the Ajtai–Komlós–Szemerédi (1983) O(n log n) sorting network construction.

## Resources

- **[Proof dependency graph](https://girving.github.io/aks/)** — Interactive visualization
- **[References](REFERENCES.md)** — Papers and educational materials
- **[CLAUDE.md](CLAUDE.md)** — Development guide for Claude Code

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

## Main Results

- `AKS.size_nlogn` : The network has size O(n log n)
- `AKS.sorts` : The network correctly sorts all inputs

## Proof Architecture

1. **Comparator networks and 0-1 principle** (`AKS/Basic.lean`)
2. **Expander graphs via zig-zag product** (`AKS/ZigZag.lean`)
3. **ε-halvers from expanders** (`AKS/Halver.lean`)
4. **Recursive AKS construction** (`AKS/Basic.lean`)

See [REFERENCES.md](REFERENCES.md) for detailed citations and proof strategy documentation.
