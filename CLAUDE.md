# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Lean 4 formalization of the Ajtai–Komlós–Szemerédi (1983) O(n log n) sorting network construction. The project formalizes the proof architecture using the zig-zag product (Reingold–Vadhan–Wigderson 2002) as the route to explicit expander families, avoiding the heavy algebraic machinery (Margulis/LPS) that would require years of formalization effort.

Most theorems have `sorry` placeholders — this is intentional. The codebase is a structural skeleton demonstrating the complete proof architecture.

## Build Commands

```bash
lake build          # Build the project (first build downloads mathlib, takes a long time)
lake env printPaths # Show build paths
lake clean          # Clean build artifacts
```

There are no tests or linter configurations. Correctness is verified through Lean's type checker — if `lake build` succeeds, all type-checked proofs are valid.

## Architecture

**Entry point:** `AKS.lean` — imports both modules and states the top-level theorem `zigzag_implies_aks_network` connecting expander existence to sorting networks.

**Two modules with a bottom-up dependency:**

### `AKS/Basic.lean` — Sorting Network Theory
Sections build on each other sequentially:
1. **Comparator networks** — `Comparator`, `ComparatorNetwork` (flat list of comparators), execution model
2. **0-1 principle** — reduces sorting correctness to Boolean inputs
3. **Expander graphs** — `BipartiteExpander`, spectral gap, existence
4. **ε-halvers** — approximate sorting via expanders (`IsEpsilonHalver`)
5. **AKS construction** — recursive build: split → recurse → merge with halvers
6. **Complexity analysis** — `IsBigO` notation, O(n log n) size
7. **Correctness** — `halver_composition` (geometric decrease), `AKS.sorts`

### `AKS/ZigZag.lean` — Explicit Expander Construction
1. **Regular graphs** — `RegularGraph` with rotation maps (port-based representation)
2. **Spectral gap** — second-largest eigenvalue of normalized adjacency matrix
3. **Graph squaring** — `G.square`, spectral gap squares: λ(G²) = λ(G)²
4. **Zig-zag product** — `G₁.zigzag G₂`, the three-step walk (zig-step-zag)
5. **Spectral composition theorem** — λ(G₁ ⓩ G₂) ≤ 1 - (1-λ₂)²(1-λ₁)/2
6. **Base case** — concrete small expander (axiomatized: `baseExpander`)
7. **Iterated construction** — `zigzagFamily`: square → zig-zag → repeat
8. **Main result** — `explicit_expanders_exist_zigzag`

### Data flow
```
ZigZag.lean: explicit_expanders_exist_zigzag
    ↓ (provides expander families)
AKS.lean: zigzag_implies_aks_network
    ↑ (uses sorting network machinery)
Basic.lean: AKS construction + correctness
```

## Style

- Use `↦` (not `=>`) for lambda arrows: `fun x ↦ ...`

## Key Lean/Mathlib Conventions

- `autoImplicit` is **disabled** (`lakefile.lean`) — all variables must be explicitly declared
- Depends on **Mathlib v4.27.0** — when updating, check import paths as they frequently change between versions (this has caused build breaks before)
- Lean toolchain: **v4.27.0** (pinned in `lean-toolchain`)

## Proof Status by Difficulty

**Done:** `zero_one_principle` (via `exec_comp_monotone` + threshold function contrapositive)

**Achievable (weeks):** `spectralGap_nonneg/le_one`, `spectralGap_complete`, `spectralGap_square`, `halver_convergence`

**Substantial (months):** `zigzag_spectral_bound` (core lemma — operator norm bound via orthogonal decomposition), `expander_mixing_lemma`, `halver_composition`, `expander_gives_halver`, rotation map involution proofs

**Engineering (weeks, fiddly):** replacing `baseExpander` axiom with a concrete verified graph, all-sizes interpolation in `explicit_expanders_exist_zigzag`
