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

**Note:** The preview ν = 0.65 barely violates C3 (4λA + 5/(2A) = 0.6540 > 0.65).
Floor effects make it work in practice, but the Lean formalization should use
ν ≥ 0.655 or parameterize over abstract ν with C3 as a hypothesis.

All theorems are parameterized over abstract A, ν, λ, ε with constraint
hypotheses (following the "parameterize over abstract bounds" style rule).

## Rust Simulation Results (`rust/test-bags.rs`)

Comprehensive testing of the bag-tree construction has validated the definitions
and revealed important corrections to the plan. Key findings:

### Validated
- **Invariant holds** with perfect separator for all tested n (8 to 16384)
- **Convergence rate**: stages = `⌈log(2A)/log(1/ν)⌉ · log₂(n)` ≈ 7·log₂(n)
  for Seiferas preview params. Each doubling of n adds exactly 7 stages.
- **Capacity sublemmas**: `items_from_below ≤ 4λbA + 2` (ratio ≤ 0.99),
  `items_from_above ≤ b/(2A)` (ratio = 1.00 exactly), `total ≤ νb` (ratio ≤ 0.68)
- **Uniform size** (Clause 2) always holds perfectly
- **j-stranger monotonicity**: (j+1)-strange → j-strange confirmed
  (divergence at level ℓ-j propagates down: `a/2 ≠ b/2 → a ≠ b`)

### Corrections to Original Plan
1. **Parity convention (BUG)**: Original plan had `(t + level) % 2 = 0 → empty`.
   Correct is `(t + level) % 2 = 1 → empty` (or equivalently,
   `(t + level) % 2 ≠ 0 → empty`). At t=0, root (level 0) is nonempty,
   so (0+0)%2 = 0 must mean "potentially nonempty", not "empty".
2. **Convergence threshold**: The iteration stops when leaf capacity
   `n·ν^t·A^(maxLevel)` drops below `1/λ` (not below 1). The invariant
   only needs to hold until this threshold is reached.
3. **Deep-level dynamics**: At deep levels, capacity `n·ν^t·A^d` is initially
   huge relative to actual items. The kickback `⌊λb⌋` exceeds items, so
   everything gets kicked to parent. Items propagate to deeper levels only
   as capacities shrink. The "wave front" moves at rate ~7 levels per
   `log₂(n)` stages.
4. **Stranger bounds at small bags**: When capacity b < 1/(λ·ε^(j-1)), the
   stranger bound is < 1, requiring ZERO j-strangers (integers). This is
   achievable because small bags (2-4 items) are perfectly sorted by any
   comparator network. The ε error only matters for large bags.

## File Structure

```
Separator/Defs.lean          — already exists (IsSeparator, IsApproxSep)
Separator/Family.lean        — SeparatorFamily structure (already exists)
Separator/FromHalver.lean    — halver → separator computable construction (partially exists)

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

Already implemented. Contains `SeparatorFamily` structure with `net`, `isSep`,
`depth_le` fields and `twice_size_le` derived theorem.

### Phase S2: `Separator/FromHalver.lean` — Halver → Separator

**Goal**: Given a `HalverFamily ε d`, build a `SeparatorFamily γ ε' d'`
where γ = 1/2^t, ε' = 2·t·ε, d' = t·d (Seiferas Section 6, Lemma 1).

**Status**: `halver_isSeparator_half` proved. Three theorems sorry'd:
`separator_halving_step`, `halverToSeparator_isSeparator`, `halverToSeparator_depth_le`.

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

**Status**: PROVED.

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
/-- The bag tree has levels 0 (root) to maxLevel (pairs).
    maxLevel = Nat.log 2 n - 1 for n a power of 2. -/
def maxLevel (n : ℕ) : ℕ := Nat.log 2 n - 1

/-- Size of each bag's native interval at a given level: n / 2^level. -/
def bagSize (n level : ℕ) : ℕ := n / 2 ^ level

/-- The bag index that an item with sorted rank r is native to at a given level.
    nativeBagIdx(n, level, r) = r / (n / 2^level). -/
def nativeBagIdx (n level : ℕ) (r : ℕ) : ℕ :=
  r / bagSize n level

/-- An item with sorted rank r is j-strange at bag (level, idx) if
    its native path diverges from (level, idx)'s ancestry at level (level - j).

    Key properties (validated by Rust simulation):
    - (j+1)-strange → j-strange (divergence propagates down the tree:
      native(ℓ)/2 ≠ ancestor(ℓ)/2 implies native(ℓ) ≠ ancestor(ℓ))
    - j > level → not j-strange (can't diverge above root)
    - 0-strange is vacuously false (j ≥ 1 required) -/
def isJStranger (n : ℕ) (rank : ℕ) (level idx j : ℕ) : Prop :=
  j ≥ 1 ∧ j ≤ level ∧ nativeBagIdx n (level - j) rank ≠ idx / 2^j

/-- Count of j-strangers among items in a bag.
    `perm` maps register positions to sorted ranks. -/
def jStrangerCount (n : ℕ) (perm : Fin n → Fin n)
    (regs : Finset (Fin n)) (level idx j : ℕ) : ℕ :=
  (regs.filter (fun i ↦ isJStranger n (perm i).val level idx j)).card
```

**Changes from original plan:**
- Added `j ≤ level` guard to `isJStranger` (prevents nonsense when j > level)
- `nativeBagIdx` takes `ℕ` rank rather than `Fin n` (simpler, avoids coercion)

Basic lemmas:
```lean
theorem jStranger_antitone ...         -- (j+1)-strange → j-strange
theorem not_jStranger_of_gt_level ...  -- j > level → ¬isJStranger
theorem bagInterval_partition ...      -- bags at one level partition [0, n)
theorem bagInterval_disjoint ...       -- bags at same level are disjoint
```

**Risk**: LOW.

### Phase B2: `Bags/Invariant.lean` — Four-Clause Invariant

Define the invariant and prove it is maintained by one stage (Seiferas Section 5).

#### Invariant definition

```lean
/-- Seiferas's four-clause invariant (Section 4).

    **Parity convention (CORRECTED):** `(t + level) % 2 ≠ 0 → empty`.
    At t=0, root (level 0) is nonempty: (0+0)%2 = 0, so NOT required to be empty. ✓
    Odd levels at t=0 are empty: (0+1)%2 = 1 ≠ 0, so required to be empty. ✓

    **Convergence:** The invariant holds for stages t = 0, 1, ..., T where
    T is the last stage before leaf capacity `n·ν^T·A^maxLevel < 1/λ`. -/
structure SeifInvariant (n : ℕ) (A ν λ ε : ℝ) (t : ℕ)
    (perm : Fin n → Fin n)
    (bagItems : ℕ → ℕ → Finset (Fin n)) where
  /-- (1) Alternating levels empty: levels where (t + level) is odd are empty.
      CORRECTED from original plan which had the parity reversed. -/
  alternating_empty : ∀ level idx,
    (t + level) % 2 ≠ 0 → (bagItems level idx) = ∅
  /-- (2) Uniform: all bags at a given active level have equal size. -/
  uniform_size : ∀ level idx₁ idx₂,
    idx₁ < 2^level → idx₂ < 2^level →
    (bagItems level idx₁).card = (bagItems level idx₂).card
  /-- (3) Capacity: items in bag ≤ n·ν^t·A^level. -/
  capacity_bound : ∀ level idx,
    ((bagItems level idx).card : ℝ) ≤ ↑n * ν^t * A^level
  /-- (4) Strangers: j-strangers ≤ λ·ε^(j-1)·capacity, ∀ j ≥ 1. -/
  stranger_bound : ∀ level idx j, j ≥ 1 →
    (jStrangerCount n perm (bagItems level idx) level idx j : ℝ) ≤
    λ * ε^(j-1) * (↑n * ν^t * A^level)
```

**Changes from original plan:**
- **Parity FIXED**: `(t + level) % 2 ≠ 0 → empty` (was `= 0`, which is wrong)
- Capacity uses `A^level` (ℕ exponent) not `A^(level : ℤ)` — level is always ≥ 0

#### Rebagging procedure (one stage)

For each nonempty bag B at (level, idx) with capacity b = n·ν^t·A^level:
1. Apply separator to B's registers (approximately sorts by rank)
2. If has parent: kick `⌊λb⌋` smallest + `⌊λb⌋` largest to parent (level-1, idx/2)
3. If remainder is odd and has parent: kick one more to parent
4. If has children: split remainder evenly — first half to (level+1, 2·idx),
   second half to (level+1, 2·idx+1)
5. B becomes empty

**Special cases:**
- **Root (level 0)**: No parent, no kickback. All items split to children.
- **Leaves (level = maxLevel)**: No children. All items go to parent.
  Feasibility: items ≤ 2⌊λb⌋ + 1 (guaranteed when b ≥ 1/λ).

#### Clause maintenance sublemmas

**B2a. Clause (1) — Alternating empty**
```lean
theorem alternating_empty_maintained (inv : SeifInvariant ...) :
    <clause 1 at t+1>
```
**Risk**: LOW. Direct from rebagging definition: active bags (parity t%2) become
empty, inactive bags (parity (t+1)%2) receive items.

**B2b. Clause (2) — Uniform size**
```lean
theorem uniform_size_maintained (inv : SeifInvariant ...) :
    <clause 2 at t+1>
```
**Risk**: LOW. By symmetry of construction + uniform input sizes.

**B2c. Clause (3) — Capacity**
```lean
/-- Capacity maintained when ν ≥ 4·λ·A + 5/(2·A).
    Items from children (kicked up): ≤ 4⌊λbA⌋ + 2 ≤ 4λbA + 2
    Items from parent (sent down): ≤ b/(2A)
    Total: ≤ b(4λA + 1/(2A)) + 2 ≤ b(4λA + 5/(2A)) when b ≥ A.
    For b < A: upper bags have capacity < 1 (empty), so items_from_above = 0,
    and the constraint relaxes to ν ≥ 4λA (weaker). -/
theorem capacity_maintained
    (inv : SeifInvariant n A ν λ ε t perm bagItems)
    (hν : ν ≥ 4 * λ * A + 5 / (2 * A)) :
    <clause 3 at t+1>
```
**Risk**: MEDIUM. Counting items from above/below with floor error terms.

Sublemmas (validated by Rust: items_from_below/bound ≤ 0.99, items_from_above/bound = 1.00):
```lean
theorem items_from_parent_le ...     -- parent sends ≤ b/(2A) to each child
theorem items_from_children_le ...   -- two children kick ≤ 4⌊λbA⌋ + 2 items up
```

**B2d. Clause (4), j > 1**
```lean
/-- j-stranger bound for j ≥ 2: sources are (j+1)-strangers from children
    kicked up + (j-1)-strangers from parent sent down.
    Total: ≤ 2bAλε^j + ε(b/A)λε^{j-2} = λε^{j-1}b(2Aε + 1/A)
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

/-- Convergence: after T stages where n·ν^T·A^maxLevel < 1/λ,
    all items are within bounded subtrees of their native leaves.
    T = O(log n) since T ≈ log₂(n) · log(2A)/log(1/ν). -/
theorem separatorSortingNetwork_converges
    (hparams : <parameter constraints>)
    (hstages : numStages ≥ <T expression>) :
    <all bags have ≤ 1 item, or all strangers = 0>

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
| S1. Family structure | **DONE** | Already implemented |
| S2a. Halver is separator | **DONE** | `halver_isSeparator_half` proved |
| S2b. Halving refines separation | MEDIUM | Rank/floor bookkeeping |
| S2c–e. Assembly + bundle | LOW | Induction + definition |
| B1. Bag/stranger defs | LOW | Definitions, validated by Rust |
| B2a–b. Clauses 1–2 | LOW | Direct from construction |
| B2c. Clause 3 (capacity) | MEDIUM | Floor arithmetic, Rust-validated bounds |
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
- `Separator/Family.lean`, `Separator/FromHalver.lean` (already exist, partially proved)
- `Bags/Defs.lean`, `Bags/Invariant.lean`, `Bags/Stage.lean`, `Bags/TreeSort.lean`
