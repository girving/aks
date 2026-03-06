# Lesson Plan: Seiferas Bag-Tree Algorithm & Invariant

## Part 1: The Tree of Bags (Seiferas Sections 2-3)

### Lesson 1.1: Bags, natives, and strangers

- Paper: Section 2 — binary tree of bags, native items, j-strangers
- Code: `AKS/Bags/Defs.lean`
  - `bagSize k level` — the native interval size at each tree level (`2^k / 2^level`)
  - `nativeBagIdx k level r` — which bag an item belongs to by rank
  - `isJStranger` — the key predicate: item is j steps off its native path
  - `jStrangerCount` — counting strangers in a bag
- Key lemma: `isJStranger_antitone` — (j+1)-strange implies j-strange (proved)

### Lesson 1.2: The split-and-rebag procedure

- Paper: Section 3 — kick back fringes to parent, send halves to children
- Code: `AKS/Bags/Split.lean`
  - `concreteSplit` — position-based splitting into parent/left/right portions
  - `fringeSize` = `⌊λb⌋` — how many items get kicked back per side
  - Three modes: root (no parent), interior (all three targets), leaf (all to parent)
- Code: `AKS/Bags/SplitCard.lean` — cardinality bounds on each portion

### Lesson 1.3: Parallel execution via scatter embedding

- Paper: Section 3 — "inductively predictable subsequences"
- Code: `AKS/Bags/Stage.lean`
  - `ipsBagSize` — deterministic bag sizes (depend only on k and parameters, not permutation)
  - `WireMap` — order-preserving embedding of each bag's registers into global wires
  - `separatorStage` — apply separator to all active bags in parallel
  - `separatorStage_depth_le` — depth = d_sep per stage (proved, via disjoint wires)
  - Parity convention: `bagActive t level ↔ (t + level) % 2 = 0`

### Lesson 1.4: Full assembly

- Paper: Sections 3-4 — iterate stages, finish with small sorters
- Code: `AKS/Bags/TreeSort.lean`
  - `separatorSortingNetwork` — concatenate numStages separator stages
  - `separatorSortingNetwork_depth_le` — total depth ≤ numStages × d_sep (proved)
  - `separatorSortingNetwork_converges` — after O(log n) stages, zero strangers (proved)
- Code: `AKS/Seiferas.lean` — top-level theorem `seiferas_sorting_networks_exist_pow2`

## Part 2: The Invariant (Seiferas Sections 4-5)

### Lesson 2.1: The four paper clauses → nine Lean fields

- Paper: Section 4 — Clauses (1)-(4)
- Code: `AKS/Bags/Invariant.lean` — `SeifInvariant` structure with 9 fields:

| Paper Clause | Lean Field | What it says |
|---|---|---|
| (1) Alternating | `halternating` | Inactive levels are empty |
| (2) Uniform | `huniform` | All bags at a level have equal cardinality |
| (3) Capacity | `hcapacity` | Items ≤ `bagSize k level` (structural) |
| (4) Strangers | `hstranger_bound` | j-strangers ≤ λε^(j-1) × capacity |
| — | `hbags_disjoint` | Bags have disjoint register sets |
| — | `hbounded_depth` | Bags beyond maxLevel are empty |
| — | `hidx_bound` | Out-of-range indices are empty |
| — | `hitems_partition` | Every register belongs to some bag |
| — | `hroot_even` | Root bag has even cardinality |

- Fields 5-9 are formalization overhead (implicit in the paper)
- `bagCapacity k A ν t level = 2^k * ν^t * A^level` — decays per stage, grows per level
- `initialInvariant` — holds at stage 0 (all items in root)

### Lesson 2.2: Why the invariant suffices (convergence)

- Paper: Section 4, "How much successful iteration is enough?"
- Code: `TreeSort.lean`, `separatorSortingNetwork_converges`
- When leaf capacity < 1/λ: stranger bound `λε^(j-1) · cap < 1` forces strangers = 0
- O(log n) stages suffice because capacity decays by factor ν < 1 per stage

### Lesson 2.3: Maintaining Clause (3) — capacity bound

- Paper: Section 5, first part ("Only Clauses (3) and (4)...")
- Code: `AKS/Bags/SplitCard.lean`
- Two cases: b ≥ A (main case) and b < A (items equally distributed)
- Items from below ≤ 4λbA + 2, from above ≤ b/(2A)
- Constraint: **ν ≥ 4λA + 5/(2A)**

### Lesson 2.4: Maintaining Clause (4), j > 1 — easy case

- Paper: Section 5, "Finally we turn to restoration of Clause (4)"
- Code: `AKS/Bags/SplitStranger.lean`
  - `kick_stranger_bound` — fringe items have bounded strangers (proved)
  - `parent_stranger_bound` — parent items bounded for j ≥ 2 (proved)
- Two sources: (j+1)-strangers from children + filtered (j-1)-strangers from parent
- Constraint: **2Aε + 1/A ≤ ν**

### Lesson 2.5: Maintaining Clause (4), j = 1 — the hard case

- Paper: Section 5, "All that remains is the more involved Clause (4) case of j = 1"
- Design doc: `docs/clause4.md` — detailed three-source analysis
- Code: `AKS/Bags/SplitStranger.lean`, `AKS/Bags/SeparatorBridge.lean`
- Three sources of 1-strangers at bag B:
  1. 2-strangers at children (≤ 2λεbA) — proved via Clause (4) at j=2
  2. Filtered 1-strangers in parent D (≤ ελb/A) — proved
  3. C-native items in D sent to B instead of C — **the hard part**
- Source 3 uses the benchmark comparison argument (Seiferas page 5)
- `benchmark_analytic_bound` — the key sorry (three-source bound)
- Constraint: **2λεA + ελ/A + ε/(2A) + 2λεA/(1−(2εA)²) + 1/(8A³−2A) ≤ λν**

### Lesson 2.6: The separator bridge

- Paper: Section 6 — approximate separators
- Code: `AKS/Separator/Defs.lean` — `IsApproxSep`, `IsSeparator`
- Code: `AKS/Separator/FromHalver.lean` — halver → separator construction
- Code: `AKS/Bags/SeparatorBridge.lean` — bridging split-by-position with count-by-value
- Subtle issue: split uses position (`id`), but stranger counting uses post-separator permutation (`π_next`)

## Suggested reading order

1. `docs/seiferas.md` Sections 2-3 + `Bags/Defs.lean` (concepts)
2. `docs/seiferas.md` Section 4 + `Bags/Invariant.lean` (invariant structure)
3. `Bags/Split.lean` + `Bags/Stage.lean` (mechanics)
4. `docs/seiferas.md` Section 5 + `docs/clause4.md` + `Bags/SplitStranger.lean` (maintenance proof)
5. `Bags/TreeSort.lean` + `Seiferas.lean` (assembly)
