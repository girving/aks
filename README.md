# AKS Sorting Network — Lean 4 Formalization

Formal verification of the Ajtai–Komlós–Szemerédi (1983) O(n log n) sorting network construction.

## Resources

- **[Proof dependency graph](https://girving.github.io/aks/)** — Interactive visualization
- **[References](REFERENCES.md)** — Papers and educational materials
- **[CLAUDE.md](CLAUDE.md)** — Development guide for Claude Code

## Main Results

- `AKS.size_nlogn` : The network has size O(n log n)
- `AKS.sorts` : The network correctly sorts all inputs

## Proof Architecture

1. **Comparator networks and 0-1 principle** (`AKS/Basic.lean`)
2. **Expander graphs via zig-zag product** (`AKS/ZigZag.lean`)
3. **ε-halvers from expanders** (`AKS/Halver.lean`)
4. **Recursive AKS construction** (`AKS/Basic.lean`)

See [REFERENCES.md](REFERENCES.md) for detailed citations and proof strategy documentation.
# Test comment
