# Seiferas Path: Plan for Resolving Remaining Sorries

## Status

The Seiferas path (expanders → halvers → separators → bag-tree sorting) has **2 remaining
sorries** in the Bags/Seiferas subsystem:

1. **`separatorSortingNetwork_sorts`** (TreeSort.lean:87) — the main correctness theorem
2. **`halverToSeparatorFamily'.isSep`** (Seiferas.lean:120) — separator family needs `2^t ∣ n`

Both block `seiferas_sorting_networks_exist`.

## Architecture Overview

```
SeparatorFamily.net : (n : ℕ) → ComparatorNetwork n
  ↓
separatorStage n sep stageIdx : ComparatorNetwork n     -- currently: comparators := []
  ↓
separatorSortingNetwork n sep numStages : ComparatorNetwork n
  ↓
separatorSortingNetwork_sorts : Monotone (net.exec v)   -- sorry
```

The core problem: `separatorStage` is a placeholder (`comparators := []`). To prove
`separatorSortingNetwork_sorts`, we need:
- A real `separatorStage` that applies the separator to each active bag
- A proof that each stage maintains `SeifInvariant`
- A proof that convergence (all bags ≤ 1 item) implies sorted output

## Part B Progress (Rust Exploration + Lean Formalization)

### Completed: Rust Validation (`rust/test-split-hypotheses.rs`)

All split hypotheses validated with Seiferas parameters (A=10, ν=0.65, λ=ε=1/99):

| Hypothesis | Max ratio | Status |
|---|---|---|
| `hkick_stranger` (lam·ε^j·cap) | 0.0000 | trivially holds |
| `hparent_1stranger` (parentStrangerCoeff·cap) | 0.1786 | 82% margin |
| `hcnative_bound` (cnativeCoeff·cap(parent)) | 0.1793 | 82% margin |
| `hkick_pair` (4λA·cap, no +2) | 0.9995 | holds |
| even-item property | 100% | always holds |
| parent-empty when cap < A | 100% | always holds |

### Completed: Two-Case Capacity Proof in Lean

**Key finding (Seiferas Section 5):** The original `capacity_maintained` theorem
required `hcap_ge : A ≤ n·ν^t`, which fails at early stages. The fix is a
two-case proof:
- **Case 1 (cap ≥ A):** Standard: `4λAb + 2 + b/(2A) ≤ νb` (uses C3)
- **Case 2 (cap < A):** Parent empty, children have even items, no +2:
  `4λAb ≤ νb` (uses C3 with slack)

**Changes to `Invariant.lean`:**
- Removed `hcap_ge` from both `capacity_maintained` and `invariant_maintained`
- Added `hkick_pair` parameter: paired kick bound when `cap < A`
- Derived `hfrom_parent_empty` internally: when `cap(l) < A`,
  `cap(l-1) = cap(l)/A < 1`, so parent bag has card 0, hence empty

## Parallel Part B Work: Two Instances

The remaining Part B Lean formalization splits into two parallel streams that
share only the **split definition** (which positions go to parent/left/right).

### Shared Prerequisite: Split Definition

Both instances use the same position-based split. Given a separator applied to
a bag of `b` items at `(level, idx)`:
- **toParent** (fringe): positions `0..⌊λ·b⌋` and `b - ⌊λ·b⌋..b` (bottom λ and top λ)
- **toLeftChild**: positions `⌊λ·b⌋..⌊b/2⌋` (middle-left)
- **toRightChild**: positions `⌊b/2⌋..b - ⌊λ·b⌋` (middle-right)

This is defined per-bag. The `split : ℕ → ℕ → SplitResult n` function maps
`(level, idx)` to the three components. For inactive bags (odd parity), the split
is trivially `(∅, ∅, ∅)`.

The split definition should go in a new file `AKS/Bags/Split.lean` that imports
`AKS/Bags/Invariant.lean`. Both instances can create this file independently with
the same content, or one can create it first and the other rebase.

**Concrete Lean definition sketch:**
```lean
/-- Position-based split of a bag after separator application.
    Given `b` items, the fringe is the bottom and top `⌊λ·b⌋` positions;
    the middle is split at position `⌊b/2⌋`. -/
def concreteSplit (n : ℕ) (lam : ℝ) (bags : BagAssignment n)
    (output : Fin n → Fin n)  -- separator output permutation
    (level idx : ℕ) : SplitResult n :=
  let regs := bags level idx      -- registers in this bag
  let b := regs.card               -- bag size
  let fringeSize := ⌊lam * b⌋₊    -- items in each fringe
  -- Sort positions within the bag by their output value
  -- toParent = bottom fringeSize + top fringeSize positions
  -- toLeftChild = positions fringeSize .. b/2
  -- toRightChild = positions b/2 .. b - fringeSize
  { toParent := ...
    toLeftChild := ...
    toRightChild := ... }
```

### Instance 1: Cardinality Bounds (position counting)

**Goal:** Prove the cardinality hypotheses of `invariant_maintained` hold for
the concrete split.

**Hypotheses to prove:**
```
hsplit_sub  : ∀ l i, (split l i).toParent ⊆ bags l i ∧ ...
hsplit_leaf : ∀ l i, maxLevel n ≤ l → (split l i).toLeftChild = ∅ ∧ ...
hkick      : ∀ l i, ((split l i).toParent.card : ℝ) ≤ 2 * lam * bagCapacity n A ν t l + 1
hsend_left : ∀ l i, ((split l i).toLeftChild.card : ℝ) ≤ bagCapacity n A ν t l / 2
hsend_right: ∀ l i, ((split l i).toRightChild.card : ℝ) ≤ bagCapacity n A ν t l / 2
hkick_pair : ∀ l i, bagCapacity n A ν t l < A →
               ((split (l+1) (2*i)).toParent.card +
                (split (l+1) (2*i+1)).toParent.card : ℝ) ≤
               4 * lam * bagCapacity n A ν t (l+1)
hrebag_uniform  : ∀ level i₁ i₂, ... → (rebag split level i₁).card = ...
hrebag_disjoint : ∀ l₁ l₂ i₁ i₂, (l₁,i₁) ≠ (l₂,i₂) → Disjoint ...
```

**Mathematical content:** Pure position-range arithmetic.
- `hkick`: fringe has `2 * ⌊λ·b⌋` items ≤ `2λb` (floor bound) — the +1 comes
  from rounding. Since `b ≤ cap`, this gives `≤ 2λ·cap + 1`.
- `hsend_left/right`: middle-left has `⌊b/2⌋ - ⌊λ·b⌋` items ≤ `b/2 ≤ cap/2`.
- `hkick_pair`: when `cap < A`, both children have even item count (from uniform
  size + power-of-2 divisibility), so `2·⌊λ·b⌋` is exact (no +1 rounding), giving
  `4λ·A·cap` total for the pair.
- `hsplit_sub`: by construction, all items come from the bag.
- `hrebag_uniform`: from uniform bag sizes + uniform split.
- `hrebag_disjoint`: from split being a partition of disjoint bags.

**Key Lean tools:** `Nat.floor_le`, `Nat.div_le_self`, `Finset.card_filter_le`,
`SeifInvariant.uniform_size`, `SeifInvariant.bags_disjoint`.

**Does NOT reference:** `perm`, `nativeBagIdx`, `isJStranger`, `jStrangerCount`,
`siblingNativeCount`, `parentStrangerCoeff`, `cnativeCoeff`.

**File:** `AKS/Bags/SplitCard.lean` (new, imports `Split.lean` + `Invariant.lean`)

### Instance 2: Stranger Bounds (rank structure)

**Goal:** Prove the stranger-count hypotheses of `invariant_maintained` hold for
the concrete split.

**Hypotheses to prove:**
```
hkick_stranger    : ∀ l i j, 1 ≤ j →
                      (jStrangerCount n perm (split l i).toParent (l-1) (i/2) j : ℝ) ≤
                      lam * ε^j * bagCapacity n A ν t l
hparent_stranger  : ∀ level idx j, 2 ≤ j →
                      (jStrangerCount n perm (fromParent split level idx) level idx j : ℝ) ≤
                      lam * ε^(j-1) * bagCapacity n A ν t (level-1)
hparent_1stranger : ∀ level idx,
                      (jStrangerCount n perm (fromParent split level idx) level idx 1 : ℝ) ≤
                      parentStrangerCoeff A lam ε * bagCapacity n A ν t level
```

**Mathematical content:** Rank-based counting using the separator's (γ,ε) guarantee.

- `hkick_stranger`: Fringe items are from the extreme positions of the separator
  output. At the *parent* level `(l-1, i/2)`, most fringe items are native (they're
  in the wrong child but right parent). The ε factor comes from: the separator's
  error rate means only ε-fraction of items are on the wrong side of the separation
  boundary. For j ≥ 2, the bound factors through `isJStranger_antitone`.
  **Rust finding:** max ratio 0.0000, meaning fringe items have essentially 0
  strangers at parent level. The proof should be: fringe items ⊆ bag items,
  stranger count at parent level = 0 because fringe items are native to the
  parent (being in the correct half of the parent's range).

- `hparent_stranger` (j ≥ 2): Items from parent already satisfy the invariant's
  stranger bound at the parent level. Pushing through `fromParent` (which selects
  left/right child) preserves stranger counts via `jStrangerCount_mono` (subset).

- `hparent_1stranger`: This is the hardest. Decomposes via `parent_1stranger_bound`
  (already proved in `Invariant.lean`) into:
  - `hparent_stranger_j2`: 2-strangers among fromParent ≤ `lam·ε·cap(parent)` — follows
    from the invariant's stranger bound at j=2 + subset monotonicity.
  - `hcnative_bound`: sibling-native among fromParent ≤ `cnativeCoeff·cap(parent)` — this
    is the three-source decomposition (ε/2 halver misroutes + geometric series + ancestor items).

**Key Lean tools:** `jStrangerCount_mono` (subset monotonicity), `isJStranger_antitone`,
`jStrangerCount_one_eq_two_plus_sibling`, `parent_1stranger_bound` (already proved),
`IsSeparator`/`IsApproxSep` (separator guarantee from `Separator/Defs.lean`).

**Does NOT reference:** `Finset.card` bounds on split components (those are Instance 1's job).
Uses only that fringe ⊆ bag (structural) and the invariant's existing stranger bounds.

**File:** `AKS/Bags/SplitStranger.lean` (new, imports `Split.lean` + `Invariant.lean` + `Separator/Defs.lean`)

### Assembly (after both instances complete)

Once both instances deliver their results, a short assembly file combines them:

**File:** `AKS/Bags/SplitProof.lean` (imports `SplitCard.lean` + `SplitStranger.lean`)

```lean
/-- The concrete split satisfies all hypotheses of `invariant_maintained`. -/
theorem concrete_split_maintains_invariant ... :
    SeifInvariant n A ν lam ε (t + 1) perm (rebag (concreteSplit ...)) :=
  invariant_maintained (concreteSplit ...)
    inv hparams
    hsplit_sub_proof       -- from SplitCard
    hsplit_leaf_proof      -- from SplitCard
    hkick_proof            -- from SplitCard
    hsend_left_proof       -- from SplitCard
    hsend_right_proof      -- from SplitCard
    hkick_pair_proof       -- from SplitCard
    hkick_stranger_proof   -- from SplitStranger
    hparent_stranger_proof -- from SplitStranger
    hparent_1stranger_proof -- from SplitStranger
    hrebag_uniform_proof   -- from SplitCard
    hrebag_disjoint_proof  -- from SplitCard
```

This is ~20 lines of plumbing.

## Work Packages (updated)

### Part A: Low-Risk

#### WP-A1: Fix `halverToSeparatorFamily'.isSep` with power-of-2 restriction
(unchanged — see original description above)

#### WP-A2: Implement `separatorStage` (real construction)
(unchanged — see original description above)

#### WP-A3: Prove convergence → sorted
(unchanged — see original description above)

### Part B: Remaining Lean Formalization (two parallel streams)

**WP-B-card (Instance 1):** Cardinality bounds on the concrete split.
New file `AKS/Bags/SplitCard.lean`. ~150 lines.

**WP-B-stranger (Instance 2):** Stranger bounds on the concrete split.
New file `AKS/Bags/SplitStranger.lean`. ~200 lines.

**WP-B-assembly:** Combine both into `concrete_split_maintains_invariant`.
New file `AKS/Bags/SplitProof.lean`. ~20 lines. Depends on both streams.

## Dependency Graph (updated)

```
WP-A1 (fix isSep)              -- independent
WP-A2 (implement stage)        -- independent
   ↓
Split definition (Split.lean)  -- shared prerequisite, ~30 lines
   ↓                ↓
WP-B-card        WP-B-stranger  -- PARALLEL
(SplitCard.lean) (SplitStranger.lean)
   ↓                ↓
WP-B-assembly (SplitProof.lean) -- combines both
   ↓
WP-A3 (convergence→sorted)     -- final assembly
```

## Parameter Reference (Seiferas Section 5)

For reference, the Seiferas parameters (approximate):
- A ≈ 10 (capacity growth per level)
- ν ≈ 0.65 (capacity decay per stage)
- λ ≈ 1/99 (fringe fraction)
- ε ≈ 1/99 (separator error)
- γ = 1/2 (separator split fraction, since we use 1-level halving)
- Convergence: ~7 · log₂(n) stages

Constraints (all proved to be satisfiable with these parameters):
- C3: ν ≥ 4λA + 5/(2A)
- C4 (j>1): 2Aε + 1/A ≤ ν
- C4 (j=1): 2λεA + parentStrangerCoeff ≤ λν

## Key Invariant Change (from Part B exploration)

The `capacity_maintained` and `invariant_maintained` theorems were updated:

**Removed:** `hcap_ge : A ≤ n·ν^t` — this failed at stages t ≥ 11 for n = 1024
(cap(0) drops below A before convergence), making the invariant impossible to maintain.

**Added:** `hkick_pair` — when `bagCapacity(l) < A`, the paired kick from both
children has no +2 additive term (because children have even item counts due to
divisibility of n = 2^k across uniform bag sizes).

**Derived internally:** `hfrom_parent_empty` — when `bagCapacity(l) < A`,
`bagCapacity(l-1) = bagCapacity(l)/A < 1`, so the parent bag has 0 items, hence
`fromParent` is empty. This eliminates the parent contribution in Case 2.
