# Separator-Based Sorting Network Proof (Paterson/Seiferas Path)

Plan for implementing the Paterson (1990) / Seiferas (2009) separator-based
approach to the AKS sorting network correctness proof. This is an alternative
to the ε-nearsort-based tree argument currently in `TreeSorting.lean`.

## Motivation

The current AKS tree-based proof (Sections 5–8) uses ε-nearsorts and a
complex four-lemma induction with tree-distance-based wrongness measures.
The Paterson/Seiferas reformulation replaces ε-nearsorts with
**(λ, ε)-separators** — a cleaner abstraction that:

1. **Decouples halving from sorting**: separators split input into "definitely
   small" (FL), "probably small" (CL), "probably large" (CR), "definitely
   large" (FR) parts, with explicit error bounds on each.
2. **Simplifies the tree argument**: the outsider/stranger tracking uses
   separator error bounds directly, avoiding the indirect position-displacement
   reasoning that makes the AKS original proof hard to formalize.
3. **Has concrete depth bounds**: Paterson achieves depth < 6100 log n;
   Seiferas tightens to ≤ ~49 log n.

Both approaches share the same ε-halver definition (our `IsEpsilonHalver` in
`Halver.lean`) and the same expander → halver bridge. The difference is
everything downstream of halvers.

## Primary References

- **`docs/paterson.pdf`** — Paterson (1990), "Improved sorting networks with
  O(log N) depth", Algorithmica 5(1). Sections 3–7.
- **`docs/seiferas.pdf`** — Seiferas (2009), "Sorting networks of logarithmic
  depth, further simplified", Algorithmica 53(4). Sections 5–7.

Page references below are to Paterson unless noted.

## Key Definitions

### 1. (λ, ε)-Separator (Paterson Section 3, Definition 3.1)

A comparator network on m wires is a **(λ, ε)-separator** if for every
permutation input, the output has the following four-part partition:

```
  FL          CL          CR          FR
[λm/2]   [(1-λ)m/2]  [(1-λ)m/2]   [λm/2]
```

Where (using rank-based definitions, as in our `IsEpsilonHalver`):
- **FL** ("far left") = first λm/2 positions
- **CL** ("center left") = next (1−λ)m/2 positions
- **CR** ("center right") = next (1−λ)m/2 positions
- **FR** ("far right") = last λm/2 positions

The error bounds (for every k):
- **(S1) Fringe accuracy**: For each k ≤ λm/2, at most εk of the k
  smallest (largest) elements are NOT in FL (FR).
- **(S2) Center accuracy**: For each k ≤ (1−λ)m/2, at most εk of the k
  smallest (largest) elements not in FL (FR) are NOT in FL∪CL (FR∪CR).

In other words:
- FL captures the smallest elements with error ε
- FR captures the largest elements with error ε
- CL∪FL captures the smaller half with error ε
- CR∪FR captures the larger half with error ε

**Relationship to ε-halvers**: An ε-halver is essentially a (1, ε)-separator
(λ = 1 means FL∪FR is the whole array, CL and CR are empty). Separators with
λ < 1 have non-trivial center regions.

### 2. ε-Approximate λ-Separation (Seiferas Section 6)

Seiferas uses a slightly different but equivalent formulation:

A network provides **ε-approximate λ-separation** if for each λ' ≤ λ,
at most ελ'n of the ⌊λ'n⌋ smallest (largest) elements are NOT among the
first (last) ⌊λn⌋ positions.

This is a single-parameter family indexed by λ. The ε-halver property is
the special case λ = 1/2.

### 3. Outsiders/Strangers (Paterson Section 5)

In the tree argument, each node v at depth d is responsible for a contiguous
block of m/2^d wires. An element is an **outsider** (Paterson) or **stranger**
(Seiferas) at node v if it is currently at a position within v's block but
does NOT belong there in the sorted output.

The tree argument tracks how outsiders are eliminated level by level.

## Construction: Separator from Halvers (Paterson Section 4)

Given an ε-halver H, construct a (λ, O(ε))-separator:

1. Apply H to split into top/bottom halves
2. Recursively apply H to each half, building a binary tree of depth
   ⌈log₂(1/λ)⌉
3. The leaves of this tree are the FL, CL, CR, FR regions

**Key lemma (Paterson Lemma 4.1)**: If H is an ε-halver and we iterate
⌈log₂(1/λ)⌉ times, the result is a (λ, cε)-separator for some constant c
depending on ε and the iteration depth.

This is the bridge between our existing `IsEpsilonHalver` and the new
separator notion.

## Tree Argument (Paterson Sections 5–7, Seiferas Sections 5–7)

### Structure

The sorting network is a balanced binary tree of depth T = O(log n):
- Each internal node applies a separator to its input block
- FL/FR outputs go to the parent (they're "probably correct")
- CL/CR outputs go to the children (they need further sorting)
- Leaves handle base-case sorting

### Key Invariant (Outsider Count)

For each node v at depth d, let O(v) = number of outsiders at v.
After each round of separator applications:

- **Outsiders decrease geometrically**: O(v) after round ≤ ε · O(v) before
  round, plus contributions from parent/children's outsiders.
- **Total outsider count**: Σ_v O(v) · weight(v) decreases by a constant
  factor each round.

### Seiferas's Simplification (Section 7)

Seiferas simplifies the outsider tracking by:
1. Using a single potential function Φ = Σ over all nodes of
   (outsider count) × (geometric weight based on depth)
2. Showing Φ decreases by a constant factor per round
3. After O(log n) rounds, Φ < 1, meaning zero outsiders everywhere

This avoids the case-by-case analysis in the original AKS proof.

## Implementation Plan for `AKS/Separator/`

### Phase 1: Core Definitions (`AKS/Separator/Defs.lean`)

```lean
/-- A (λ, ε)-separator: four-part partition with error bounds.
    Permutation-based (like IsEpsilonHalver), using rank. -/
def IsSeparator {n : ℕ} (net : ComparatorNetwork n) (λ ε : ℝ) : Prop :=
  ∀ (v : Equiv.Perm (Fin n)),
    SeparatorProperty (net.exec v) n λ ε

/-- The separator property for a single permutation output. -/
def SeparatorProperty {n : ℕ} (w : Fin n → Fin n) (m : ℕ) (λ ε : ℝ) : Prop :=
  -- (S1) Fringe accuracy: for k ≤ λm/2, at most εk of k smallest not in FL
  (∀ k, k ≤ ⌊λ * m / 2⌋₊ →
    ((Finset.univ.filter (fun pos ↦
        rank (w pos) < k ∧ ¬(rank pos < ⌊λ * m / 2⌋₊))).card : ℝ) ≤ ε * k) ∧
  -- (S1') Dual: k largest not in FR
  (∀ k, k ≤ ⌊λ * m / 2⌋₊ →
    ((Finset.univ.filter (fun pos ↦
        rank (w pos) ≥ m - k ∧ ¬(rank pos ≥ m - ⌊λ * m / 2⌋₊))).card : ℝ) ≤ ε * k) ∧
  -- (S2) Center accuracy: for k ≤ (1-λ)m/2, at most εk of k smallest
  -- (excluding those in FL) not in FL∪CL
  (∀ k, k ≤ ⌊(1 - λ) * m / 2⌋₊ →
    ((Finset.univ.filter (fun pos ↦
        rank (w pos) < ⌊λ * m / 2⌋₊ + k ∧
        ¬(rank pos < ⌊λ * m / 2⌋₊ + ⌊(1 - λ) * m / 2⌋₊))).card : ℝ) ≤ ε * k) ∧
  -- (S2') Dual for end segments
  (∀ k, k ≤ ⌊(1 - λ) * m / 2⌋₊ →
    ((Finset.univ.filter (fun pos ↦
        rank (w pos) ≥ m - ⌊λ * m / 2⌋₊ - k ∧
        ¬(rank pos ≥ m - ⌊λ * m / 2⌋₊ - ⌊(1 - λ) * m / 2⌋₊))).card : ℝ) ≤ ε * k)
```

**Note**: The exact Lean definition will need refinement — the above is a
sketch. The key design choice is permutation-based (matching `IsEpsilonHalver`)
rather than Boolean-based.

**Alternative (Seiferas-style)**: Define `IsApproxSeparation` as a
single-parameter family. This may be cleaner for the induction.

### Phase 2: Halver → Separator (`AKS/Separator/FromHalver.lean`)

```lean
/-- Iterated halving yields a separator (Paterson Lemma 4.1). -/
theorem halver_gives_separator {n : ℕ} (net : ComparatorNetwork n) (ε λ : ℝ)
    (hε : 0 < ε) (hλ : 0 < λ) (hλ1 : λ ≤ 1)
    (hnet : IsEpsilonHalver net ε) :
    ∃ (sep_net : ComparatorNetwork n),
      IsSeparator sep_net λ (c * ε) ∧
      sep_net.comparators.length ≤ ⌈Real.log (1/λ) / Real.log 2⌉₊ * net.comparators.length
```

Key sublemmas:
- One halving step preserves separator property with degraded ε
- Iterated halving builds up λ geometrically
- Error accumulation is bounded

### Phase 3: Outsider Definitions (`AKS/Separator/Outsider.lean`)

```lean
/-- Block assignment: node v at depth d owns positions [v·m/2^d, (v+1)·m/2^d). -/
def nodeBlock (n d v : ℕ) : Finset (Fin n) := ...

/-- An element at position i is an outsider at node v if i ∈ nodeBlock(v)
    but the element's sorted position is not in nodeBlock(v). -/
def isOutsider (n d : ℕ) (w : Equiv.Perm (Fin n)) (v : ℕ) (i : Fin n) : Prop :=
  i ∈ nodeBlock n d v ∧ w i ∉ nodeBlock n d v

/-- Count of outsiders at node v. -/
def outsiderCount (n d : ℕ) (w : Equiv.Perm (Fin n)) (v : ℕ) : ℕ :=
  (nodeBlock n d v |>.filter (isOutsider n d w v)).card
```

### Phase 4: Potential Function (`AKS/Separator/Potential.lean`)

Following Seiferas Section 7:

```lean
/-- Seiferas potential function: weighted sum of outsider counts. -/
noncomputable def potential (n T : ℕ) (w : Equiv.Perm (Fin n)) (α : ℝ) : ℝ :=
  ∑ d in Finset.range (T + 1),
    ∑ v in Finset.range (2^d),
      α ^ d * outsiderCount n d w v
```

Key theorem:
```lean
/-- One round of separator applications decreases potential by factor β < 1. -/
theorem potential_decrease (net : ...) (hnet : IsSeparator net λ ε) ... :
    potential n T w' α ≤ β * potential n T w α
```

### Phase 5: Assembly (`AKS/Separator/TreeSort.lean`)

```lean
/-- After O(log n) rounds of separator-based sorting, the sequence is sorted. -/
theorem separator_tree_sorting {n : ℕ} (halver : ComparatorNetwork n)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1/2)
    (hnet : IsEpsilonHalver halver ε) :
    ∃ (net : ComparatorNetwork n),
      (∀ v : Fin n → Bool, Monotone (net.exec v)) ∧
      net.comparators.length ≤ C * n * Nat.log 2 n
```

## Relationship to Existing Code

### What stays the same
- `Halver.lean`: `IsEpsilonHalver`, `EpsilonHalved`, etc. — shared by both paths
- `RegularGraph.lean`, `ZigZag.lean`, etc. — expander infrastructure
- `Mixing.lean`: expander mixing lemma
- `ComparatorNetwork.lean`: basic network theory, 0-1 principle

### What's parallel (not replaced)
- `Nearsort.lean`: ε-nearsort definitions (AKS Section 4) — used only by
  `TreeSorting.lean` path
- `TreeSorting.lean`: AKS Sections 5–8 tree argument — the original approach
- `TreeDamageStability.lean`, `TreeDamageImprovement.lean`: Lemmas 2a, 2b

### What's new
- `AKS/Separator/Defs.lean`: separator definitions
- `AKS/Separator/FromHalver.lean`: halver → separator construction
- `AKS/Separator/Outsider.lean`: outsider/stranger definitions
- `AKS/Separator/Potential.lean`: Seiferas potential function
- `AKS/Separator/TreeSort.lean`: tree argument and assembly

### Data flow (new path)
```
Halver.lean ──→ Separator/Defs.lean
                    ↓
              Separator/FromHalver.lean
                    ↓
              Separator/Outsider.lean
                    ↓
              Separator/Potential.lean
                    ↓
              Separator/TreeSort.lean ──→ AKSNetwork.lean (aks_tree_sorting)
```

## Risk Assessment

| Phase | Risk | Notes |
|-------|------|-------|
| 1. Definitions | LOW | Straightforward translation from paper |
| 2. Halver → Separator | MEDIUM | Iterated halving + error accumulation |
| 3. Outsider defs | LOW | Simple counting definitions |
| 4. Potential function | MEDIUM | Core of the proof; need careful constant tracking |
| 5. Assembly | MEDIUM | Connecting all pieces; constant optimization |

**Critical bottleneck**: Phase 4 (potential decrease). If the constants don't
work out cleanly, this is where we'll get stuck. Paterson's constants are
concrete (depth < 6100 log n), so the proof exists — the question is whether
the Lean formalization is manageable.

**Fallback**: If the full potential function proof is too hard, we can
axiomatize the potential decrease lemma and prove everything else. This still
validates the proof architecture.

## Comparison: Which Path to Complete?

| Aspect | AKS Original (TreeSorting) | Paterson/Seiferas (Separator) |
|--------|---------------------------|-------------------------------|
| Definitions | ε-nearsort, tree wrongness | (λ,ε)-separator, outsiders |
| Key difficulty | Bool↔permutation bridge, tree wrongness algebra | Potential function decrease |
| Sorry count | ~5 (Lemmas 2a, 2b, bridges) | Not started |
| Infrastructure | Extensive (2600+ lines) | None yet |
| Conceptual clarity | Complex (position displacement + tree distance) | Cleaner (outsider counting) |
| Concrete bounds | Not tracked | depth < 6100 log n (Paterson) |

**Recommendation**: Develop both paths in parallel. The separator path may turn
out simpler to complete because:
1. The outsider counting argument is more direct than tree-distance wrongness
2. Seiferas's single potential function avoids the four-lemma case analysis
3. The separator notion cleanly separates halving from sorting

However, the existing TreeSorting infrastructure is substantial and may be
closer to completion. The Bool↔permutation bridge (shared obstacle) would
benefit both paths.

## Getting Started

1. Read Paterson Sections 3–4 (separator definition and construction)
2. Read Seiferas Sections 5–7 (simplified tree argument)
3. Create `AKS/Separator/Defs.lean` with the separator definition
4. Add the new files to `lakefile.lean`
5. Prove `halver_is_trivial_separator` (an ε-halver is a (1, ε)-separator)
   as a sanity check on the definition
