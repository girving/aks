# Separator-Based Sorting Network Proof (Seiferas Path)

Detailed plan for the Paterson (1990) / Seiferas (2009) separator-based
approach to proving AKS sorting networks have O(log n) depth.

**Design principles:**
1. **Computable constructions, not existentials.** Every network is a `def`,
   with properties proved as separate theorems. No `∃ (net : ...), ...`.
2. **Depth bounds, not size bounds.** Depth is the fundamental measure;
   size ≤ n/2 · depth follows from `size_le_half_n_mul_depth`.

## Primary References

- **`docs/seiferas.pdf`** — Seiferas (2009), "Sorting networks of logarithmic
  depth, further simplified". **Primary source.** Sections 3–7.
- **`docs/paterson.pdf`** — Paterson (1990), "Improved sorting networks with
  O(log N) depth". Sections 3–7. Seiferas simplifies this.

## Overview

The construction has three layers:

1. **Expanders → halvers** (already proved: `expanderHalver`, `expander_gives_halver`)
2. **Halvers → separators** (`Separator/`) — iterated halving, Seiferas Section 6
3. **Separators → sorting network** (`Bags/`) — tree-based invariant argument, Seiferas Sections 3–5

The top-level theorem: given an expander family with constant degree d and
spectral gap β < 1/2, there exists a sorting network of depth O(log n).

## Key Insight: O(log n) Depth

The sorting network applies separators to "bags" in a binary tree over O(log n)
stages. Within each stage, separators are applied to ALL active bags. The
critical insight (Seiferas Section 7): due to the alternating-empty-levels
invariant (Clause 1), active bags at any stage have **disjoint register sets**.
Therefore all separators within one stage run in **parallel**, giving:

    depth per stage = separator depth = O(1)
    number of stages = O(log n)
    total depth = O(log n)

This is fundamentally different from the nearsort path (`halverNetwork`), which
processes tree levels sequentially and gives O(log² n) depth.

In the comparator network representation, we concatenate all per-stage
comparator lists. The greedy `ComparatorNetwork.depth` computation automatically
discovers the parallelism (disjoint wires → same time step). The depth proof
shows disjointness → `depth_le_of_decomposition` gives the O(1) bound per stage.

## Parameters (Seiferas Section 4)

The construction is parameterized by:
- **A > 1**: capacity growth rate per tree level
- **ν ∈ (0, 1)**: capacity decay per stage
- **λ ∈ (0, 1/2)**: separator fringe fraction
- **ε > 0**: separator error rate (from halver spectral gap)

Subject to constraints (Seiferas Section 5):
- (C3) `ν ≥ 4·λ·A + 5/(2·A)`
- (C4, j>1) `2·A·ε + 1/A ≤ ν`
- (C4, j=1) `2·λ·ε·A + ε·λ/A + ε/(2·A) + 2·λ·ε·A/(1-(2·ε·A)²) + 1/(8·A³-2·A) ≤ λ·ν`

Seiferas's preview: λ = ε = 1/99, A = 10, ν = 0.65.

All theorems are parameterized over abstract A, ν, λ, ε with constraint
hypotheses (following the "parameterize over abstract bounds" style rule).

## File Structure

```
Separator/Defs.lean          — already exists (IsSeparator, IsApproxSep)
Separator/Family.lean        — SeparatorFamily structure
Separator/FromHalver.lean    — halver → separator computable construction

Bags/Defs.lean               — bag tree, register assignment, j-strangers
Bags/Invariant.lean          — four-clause invariant, maintenance lemmas
Bags/Stage.lean              — one-stage network construction + depth bound
Bags/TreeSort.lean           — full sorting network, correctness, depth O(log n)
```

Data flow:
```
Halver/Defs.lean ────→ Separator/Defs.lean
                            ↓
                       Separator/Family.lean
                            ↓
                       Separator/FromHalver.lean  (uses Nearsort/Construction.lean)
                            ↓
                       Bags/Defs.lean
                            ↓
                       Bags/Invariant.lean
                            ↓
                       Bags/Stage.lean
                            ↓
                       Bags/TreeSort.lean ──→ Tree/AKSNetwork.lean
```

---

## `Separator/` — Constructing Separators from Halvers

### Phase S1: `Separator/Family.lean` — SeparatorFamily Structure

```lean
/-- A family of (γ, ε)-separator networks, one per input size,
    with depth bounded by d. Analogous to `HalverFamily`. -/
structure SeparatorFamily (γ ε : ℝ) (d : ℕ) where
  /-- The separator network for each input size n. -/
  net : (n : ℕ) → ComparatorNetwork n
  /-- Each network is a (γ, ε)-separator. -/
  isSep : ∀ n, IsSeparator (net n) γ ε
  /-- Each network has depth at most d. -/
  depth_le : ∀ n, (net n).depth ≤ d
```

Derived:
```lean
theorem SeparatorFamily.size_le (family : SeparatorFamily γ ε d) (n : ℕ) :
    (family.net n).size ≤ n / 2 * d
```

**Risk**: LOW.

### Phase S2: `Separator/FromHalver.lean` — Halver → Separator

**Goal**: Given a `HalverFamily ε d`, build a `SeparatorFamily γ ε' d'`
where γ = 1/2^t, ε' = 2·t·ε, d' = t·d (Seiferas Section 6, Lemma 1).

#### Construction (computable)

Reuses `halverNetwork` from `Nearsort/Construction.lean`: iterating the
halver `t` times builds a network that provides (2·t·ε)-approximate
(1/2^t)-separation.

```lean
/-- Build a separator from a halver family by iterating t levels. -/
def halverToSeparator (n : ℕ) (family : HalverFamily ε d) (t : ℕ) :
    ComparatorNetwork n :=
  halverNetwork n family.net t
```

#### Sublemma S2a: Base case

```lean
/-- An ε-halver provides ε-approximate 1/2-separation (Seiferas Lemma 1 base).
    The halver property (rank-based bounds on displaced elements in each half)
    implies the separator property when γ = 1/2. -/
theorem halver_isSeparator_half {n : ℕ} (net : ComparatorNetwork n) (ε : ℝ) :
    IsEpsilonHalver net ε → IsSeparator net (1/2) ε
```

**Risk**: LOW–MEDIUM. Comparing `EpsilonInitialHalved` and `SepInitial` at
γ = 1/2. The rank-based formulations should align; floor/ceiling details
may require bridging lemmas.

#### Sublemma S2b: Induction step

```lean
/-- Halving refines separation: applying an ε₁-halver to both halves of a
    (γ, ε')-separated sequence gives (γ/2, ε' + 2·ε₁)-separation.

    Elements correctly in the γ-fringe stay correct. Elements that were
    ε'-displaced gain at most ε₁ additional displacement from the halver. -/
theorem separator_halving_step {n : ℕ}
    (γ ε' ε₁ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hsep : IsSeparator net γ ε')
    (hhalver : ∀ m, IsEpsilonHalver (halvers m) ε₁) :
    IsSeparator (halverNetwork_oneMoreLevel net halvers) (γ / 2) (ε' + 2 * ε₁)
```

**Risk**: MEDIUM. The key combinatorial argument: at finer resolution γ/2,
errors accumulate from (a) original ε' at resolution γ, and (b) ε₁ from
the new halving, applied twice (initial + final). Needs careful rank/floor
bookkeeping.

#### Sublemma S2c: Iterated halving (assembly)

```lean
/-- t levels of iterated ε-halving gives (2·t·ε)-approximate (1/2^t)-separation.
    Proof: induction on t using S2a (base) and S2b (step). -/
theorem halverToSeparator_isSeparator (n : ℕ) (family : HalverFamily ε d)
    (t : ℕ) (hε : 0 ≤ ε) :
    IsSeparator (halverToSeparator n family t) (1 / 2^t) (2 * t * ε)
```

**Risk**: LOW once S2a and S2b are done.

#### Sublemma S2d: Depth bound

```lean
/-- Iterated separator depth ≤ t · d. At each of t levels, halvers at the
    same level operate on disjoint wire ranges (different subintervals),
    so they run in parallel with depth ≤ d. Levels are sequential. -/
theorem halverToSeparator_depth_le (n : ℕ) (family : HalverFamily ε d)
    (t : ℕ) :
    (halverToSeparator n family t).depth ≤ t * d
```

**Risk**: MEDIUM. Needs a new `halverAtLevel_depth_le` theorem (halvers at
one tree level have disjoint wire ranges → depth = max of individual
depths ≤ d). Then sum across t levels.

#### Sublemma S2e: Bundle into SeparatorFamily

```lean
/-- Build a SeparatorFamily from a HalverFamily with t iteration levels. -/
def halverToSeparatorFamily (family : HalverFamily ε d) (t : ℕ)
    (hε : 0 ≤ ε) :
    SeparatorFamily (1 / 2^t) (2 * t * ε) (t * d) where
  net n := halverToSeparator n family t
  isSep n := halverToSeparator_isSeparator n family t hε
  depth_le n := halverToSeparator_depth_le n family t
```

---

## `Bags/` — Sorting via the Bag Tree

### Phase B1: `Bags/Defs.lean` — Bag Definitions and j-Strangers

Definitions for the binary bag tree and stranger counting (Seiferas Sections 2–3).

```lean
/-- Register range for bag (level, idx): positions
    [idx · ⌊n/2^level⌋, (idx+1) · ⌊n/2^level⌋). -/
def bagInterval (n level idx : ℕ) : Finset (Fin n)

/-- The bag index that position i is native to at a given level. -/
def nativeBagIdx (n level : ℕ) (i : Fin n) : ℕ :=
  i.val / (n / 2 ^ level)

/-- An item with sorted position p is j-strange at bag (level, idx) if
    its native path diverges from (level, idx)'s ancestry at least j
    levels above. j=1: parent differs (from sibling). j≥2: further. -/
def isJStranger (n : ℕ) (sortedPos : Fin n) (level idx j : ℕ) : Prop :=
  j ≥ 1 ∧ nativeBagIdx n (level - j) sortedPos ≠ idx / 2^j

/-- Count of j-strangers in a bag's current register set. -/
def jStrangerCount (n : ℕ) (perm : Fin n → Fin n)
    (regs : Finset (Fin n)) (level idx j : ℕ) : ℕ :=
  (regs.filter (fun i ↦ isJStranger n (perm i) level idx j)).card
```

Basic lemmas:
```lean
theorem bagInterval_partition ...     -- bags at one level partition [0, n)
theorem bagInterval_disjoint ...      -- bags at same level are disjoint
theorem jStranger_antitone ...        -- (j+1)-strange → j-strange
theorem stranger_geometric_sum ...    -- ∑_{j≥1} λε^{j-1}b = λb/(1-ε) (useful later)
```

**Risk**: LOW.

### Phase B2: `Bags/Invariant.lean` — Four-Clause Invariant

Define the invariant and prove it is maintained by one stage (Seiferas Section 5).

#### Invariant definition

```lean
/-- Seiferas's four-clause invariant (Section 4). -/
structure SeifInvariant (n : ℕ) (A ν λ ε : ℝ) (t : ℕ)
    (perm : Fin n → Fin n)
    (bagItems : ℕ → ℕ → Finset (Fin n)) where
  /-- (1) Alternating levels empty: levels with same parity as t are empty. -/
  alternating_empty : ∀ level idx,
    (t + level) % 2 = 0 → (bagItems level idx) = ∅
  /-- (2) Uniform: all bags at a given active level have equal size. -/
  uniform_size : ∀ level idx₁ idx₂,
    idx₁ < 2^level → idx₂ < 2^level →
    (bagItems level idx₁).card = (bagItems level idx₂).card
  /-- (3) Capacity: items in bag ≤ n·ν^t·A^level. -/
  capacity_bound : ∀ level idx,
    ((bagItems level idx).card : ℝ) ≤ ↑n * ν^t * A^(level : ℤ)
  /-- (4) Strangers: j-strangers ≤ λ·ε^(j-1)·capacity, ∀ j ≥ 1. -/
  stranger_bound : ∀ level idx j, j ≥ 1 →
    (jStrangerCount n perm (bagItems level idx) level idx j : ℝ) ≤
    λ * ε^(j-1) * (↑n * ν^t * A^(level : ℤ))
```

#### Clause maintenance sublemmas

**B2a. Clause (1) — Alternating empty**
```lean
theorem alternating_empty_maintained (inv : SeifInvariant ...) :
    <clause 1 at t+1>
```
**Risk**: LOW. Direct from rebagging definition.

**B2b. Clause (2) — Uniform size**
```lean
theorem uniform_size_maintained (inv : SeifInvariant ...) :
    <clause 2 at t+1>
```
**Risk**: LOW. By symmetry of construction.

**B2c. Clause (3) — Capacity**
```lean
/-- Capacity maintained when ν ≥ 4·λ·A + 5/(2·A).
    Items from children (kicked up): ≤ 2·λ·A · current_capacity
    Items from parent (sent down): ≤ 1/(2·A) · current_capacity
    Floor errors: contribute +5/(2·A) slack. -/
theorem capacity_maintained
    (inv : SeifInvariant n A ν λ ε t perm bagItems)
    (hν : ν ≥ 4 * λ * A + 5 / (2 * A)) :
    <clause 3 at t+1>
```
**Risk**: MEDIUM. Counting items from above/below with floor error terms.

Sublemmas:
```lean
theorem items_from_parent_le ...     -- parent sends ≤ b/(2A) to each child
theorem items_from_children_le ...   -- each child kicks ≤ λ·b·A items up
```

**B2d. Clause (4), j > 1**
```lean
/-- j-stranger bound for j ≥ 2: sources are (j+1)-strangers from children
    kicked up + (j-1)-strangers from parent sent down.
    Constraint: 2·A·ε + 1/A ≤ ν. -/
theorem stranger_bound_maintained_j_gt_1
    (inv : SeifInvariant ...) (hν : 2 * A * ε + 1 / A ≤ ν) (hj : j ≥ 2) :
    <clause 4 for j at t+1>
```
**Risk**: MEDIUM. Combinatorial counting of stranger sources.

**B2e. Clause (4), j = 1 — CRITICAL BOTTLENECK**
```lean
/-- 1-stranger bound (Seiferas Section 5, hardest case).
    Three sources of 1-strangers after one stage:
    (a) 2+-strangers at children kicked up: ≤ 2·λ·ε·A·b
    (b) 1-strangers at parent sent down: ≤ ε·λ·b/A
    (c) Sibling leakage: items native to sibling C sent to B by
        separator error. Bounded by geometric series in (2εA)².

    Master constraint:
    2·λ·ε·A + ε·λ/A + ε/(2·A) + 2·λ·ε·A/(1-(2·ε·A)²) + 1/(8·A³-2·A) ≤ λ·ν -/
theorem stranger_bound_maintained_j_eq_1
    (inv : SeifInvariant ...) (hmaster : <master constraint>) :
    <clause 4 for j=1 at t+1>
```
**Risk**: HIGH. This is the proof's critical bottleneck.

Sublemmas for B2e:
```lean
/-- Contribution (a): 2+-strangers at children that get kicked up. -/
theorem strangers_from_children_kicked_up ...

/-- Contribution (b): 1-strangers at parent sent down. -/
theorem strangers_from_parent_sent_down ...

/-- Contribution (c): sibling leakage via separator error.
    Uses separator's ε-approximate γ-separation: among items assigned
    to B's side, at most ε·γ·b_parent are actually native to sibling C.
    Cascading through levels gives geometric series in (2εA)². -/
theorem sibling_leakage_bound ...
```

**Fallback**: Axiomatize B2e if the proof is too hard. The statement is
directly from Seiferas Section 5 and can be verified against the paper.

### Phase B3: `Bags/Stage.lean` — One-Stage Construction

```lean
/-- Apply separator to all active bags at stage t. Computable. -/
def separatorStage (n : ℕ) (sep : SeparatorFamily γ ε d_sep)
    (stageIdx : ℕ) : ComparatorNetwork n

/-- Active bags have disjoint registers (from alternating-empty invariant). -/
theorem active_bags_disjoint (inv : SeifInvariant ...) :
    ∀ (l₁ i₁) (l₂ i₂), (l₁, i₁) ≠ (l₂, i₂) →
    active l₁ i₁ → active l₂ i₂ →
    Disjoint (bagItems l₁ i₁) (bagItems l₂ i₂)

/-- One stage has depth = separator depth (all bags parallel). -/
theorem separatorStage_depth_le :
    (separatorStage n sep stageIdx).depth ≤ d_sep
```

**Risk**: MEDIUM. The depth proof needs `active_bags_disjoint` →
`depth_le_of_decomposition`.

### Phase B4: `Bags/TreeSort.lean` — Assembly

```lean
/-- The full separator sorting network. Computable. -/
def separatorSortingNetwork (n : ℕ) (sep : SeparatorFamily γ ε d_sep)
    (numStages : ℕ) : ComparatorNetwork n :=
  { comparators := (List.range numStages).flatMap fun t ↦
      (separatorStage n sep t).comparators }

/-- Total depth = numStages · separator depth. -/
theorem separatorSortingNetwork_depth_le :
    (separatorSortingNetwork n sep numStages).depth ≤ numStages * d_sep

/-- After O(log n) stages, the network sorts (invariant → zero strangers → sorted). -/
theorem separatorSortingNetwork_sorts
    (hparams : <parameter constraints>)
    (hstages : numStages ≥ C_stages * Nat.log 2 n) :
    ∀ v : Fin n → Bool, Monotone ((separatorSortingNetwork n sep numStages).exec v)

/-- Depth bound: O(log n). -/
theorem separatorSortingNetwork_depth_bound :
    (separatorSortingNetwork n sep (C * Nat.log 2 n)).depth ≤ C' * Nat.log 2 n
```

**Risk**: MEDIUM (assembly, once all sublemmas are proved).

---

## Risk Summary

| Phase | Risk | Notes |
|-------|------|-------|
| S1. Family structure | LOW | Definition |
| S2a. Halver is separator | LOW–MEDIUM | Definition comparison |
| S2b. Halving refines separation | MEDIUM | Rank/floor bookkeeping |
| S2c–e. Assembly + bundle | LOW | Induction + definition |
| B1. Bag/stranger defs | LOW | Definitions |
| B2a–b. Clauses 1–2 | LOW | Direct from construction |
| B2c. Clause 3 (capacity) | MEDIUM | Floor arithmetic |
| B2d. Clause 4, j>1 | MEDIUM | Combinatorial counting |
| B2e. Clause 4, j=1 | **HIGH** | Critical bottleneck |
| B3. Stage depth | MEDIUM | Disjointness proof |
| B4. Assembly | MEDIUM | Connecting pieces |

**Critical path**: B2e (j=1 stranger bound) is the hardest lemma.
Everything else is LOW–MEDIUM risk.

## Relationship to Existing Code

### Shared (unchanged)
- `Sort/`: comparator network theory, depth, 0-1 principle
- `Halver/`: `IsEpsilonHalver`, `HalverFamily`, `expanderHalver` (fully proved)
- `Graph/`, `ZigZag/`: expander infrastructure
- `Nearsort/Construction.lean`: `halverNetwork`, `halverAtLevel` (reused by FromHalver)

### Parallel (not replaced)
- `Tree/Sorting.lean`: AKS original tree argument (nearsort-based, O(log² n) depth)
- `Tree/DamageStability.lean`, `Tree/DamageImprovement.lean`
- `Nearsort/Defs.lean`: ε-nearsort definitions

### New
- `Separator/Family.lean`, `Separator/FromHalver.lean`
- `Bags/Defs.lean`, `Bags/Invariant.lean`, `Bags/Stage.lean`, `Bags/TreeSort.lean`
