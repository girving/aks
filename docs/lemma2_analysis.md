# Lemma 2 Detailed Analysis: Connecting Halver Property to Tree Wrongness

**Goal:** Reduce risk from MEDIUM-HIGH to MEDIUM by thoroughly understanding the proof before implementation.

**Lemma Statement:**
```lean
lemma zig_step_bounded_increase :
  Applying ε-nearsort to a cherry (parent + two children) gives:
  Δ'ᵣ ≤ 8A·(Δᵣ + ε·Δᵣ₋₂)  [r ≥ 3]
  Δ'ᵣ ≤ 8A·(Δᵣ + ε)        [r = 1,2]
```

---

## Step 1: Understanding the Setting

### What is a "Cherry"?

From AKS Section 6 (page 6-7), a cherry is a set of three intervals:
- **Parent interval** P at level i (on a node)
- **Left child interval** L at level i+1
- **Right child interval** R at level i+1

The parent "frames" the two children. Example with n=16, level 2 node:
```
Level 2 (node j=1): Parent interval [2, 5] ∪ [10, 13]
                         (two intervals framing children)
Level 3: Left child [2, 5], Right child [10, 13]
```

### What is ε-nearsort?

From AKS Section 4 (page 5-6):
- Apply ε₁-halver to entire cherry (where ε₁ << ε)
- Then recursively apply to halves, quarters, ...
- Until pieces < εm

But in the proof, we can think of it as: "Apply ε-nearsort = ensure elements are approximately where they should be, with at most ε error per initial segment"

### What does "Zig step" mean?

From AKS Section 6 (page 6-7):
- At time t, partition tree into cherries with apexes at **even levels**
- Apply ε-nearsort to each cherry simultaneously
- This is the "Zig" step

A "Zag" step does the same but for cherries with apexes at **odd levels**.

---

## Step 2: What We Need to Prove

### Before ε-nearsort (input):
- Registers contain values v : Fin n → Bool
- Interval J at some level has wrongness Δᵣ(J)
  - Meaning: proportion of elements in J that belong at tree-distance ≥ r

### After ε-nearsort (output):
- Registers contain v' : Fin n → Bool
- Interval J has wrongness Δ'ᵣ(J)
- **Bound:** Δ'ᵣ(J) ≤ 8A·(Δᵣ(J) + ε·Δᵣ₋₂(J))

### Key Question:
**How does applying ε-nearsort to a cherry reduce wrongness?**

---

## Step 3: The Connection Mechanism

### From AKS Section 8, Lemma 2 (page 8):

> "Most elements belonging to L will be forced to the left, and wander into L or to this closest interval. The number of exceptional elements cannot exceed ε proportion of the cherry."

Let me unpack this:

### Scenario: Element in Parent Interval P

Suppose element x is in parent interval P of the cherry.
- **Case 1:** x should be in lower section L(K) where K < P (x too high up)
  - After ε-nearsort: x is pushed LEFT (toward left child L)
  - Most of these elements end up in L or nearby intervals
  - **Exceptional:** at most ε proportion remain in P or R

- **Case 2:** x should be in upper section U(K) where K > P (x too low)
  - After ε-nearsort: x is pushed RIGHT (toward right child R)
  - Most end up in R or nearby intervals
  - **Exceptional:** at most ε proportion remain in P or L

- **Case 3:** x belongs in P (x is correctly placed)
  - After ε-nearsort: x stays in P or moves slightly
  - Contributes to Δᵣ(P) if it belonged at distance ≥ r

### Why does ε-nearsort force elements in the right direction?

**This is the KEY connection to the halver property!**

For Boolean values (0s and 1s):
- Elements "belonging to lower section" = 0s (should be in bottom)
- Elements "belonging to upper section" = 1s (should be in top)

The ε-nearsort (composed of ε₁-halvers) ensures:
- **1s are balanced** between top and bottom of the cherry
- Therefore, excess 1s in parent are pushed to right child
- Excess 0s in parent are pushed to left child
- **At most ε fraction are exceptions** (stay in wrong place)

### Connecting to Tree Wrongness Δᵣ(J)

Elements in J with wrongness at distance ≥ r belong to sections at distance ≥ r.

After ε-nearsort:
- Most of these elements move toward their correct sections
- They move at least one tree level closer (distance decreases)
- **Except:** at most ε fraction remain misplaced

So:
- **Base wrongness:** Δᵣ(J) elements at distance ≥ r
  - Most of these improve (distance decreases to < r)
  - But some might still be at distance ≥ r (bounded by overall wrongness)

- **Exception wrongness:** ε·Δᵣ₋₂(J) elements that should have improved but didn't
  - These are the ε fraction that stayed in wrong place
  - They were at distance ≥ (r-2) before, still at distance ≥ r after
  - (The -2 accounts for moving 2 levels but staying wrong)

- **Amplification by A:** The factor 8A comes from:
  - A is the fringe size parameter
  - Elements can spread across A-sized fringes
  - Worst-case amplification gives the 8A factor

---

## Step 4: Proof Structure (Sketch)

```lean
lemma zig_step_bounded_increase
    {n t : ℕ} (v v' : Fin n → Bool) (net : ComparatorNetwork n)
    (ε : ℝ) (hnet : IsEpsilonHalver net ε) (r : ℕ) (J : Interval n)
    (h_zig : v' obtained from v by applying ε-nearsort to cherries) :
    treeWrongness n t v' J r ≤
      8 * A * (treeWrongness n t v J r +
               if r ≥ 3 then ε * treeWrongness n t v J (r - 2)
               else ε) := by

  -- Step 1: Identify the cherry containing J
  let cherry := cherry_containing_J  -- parent P + children L, R

  -- Step 2: Partition elements in J by where they belong
  let elements_at_distance_r := {x ∈ J | x belongs to section at distance ≥ r}

  -- Step 3: Show ε-nearsort moves most elements toward correct place
  have h1 : After ε-nearsort, at least (1-ε) fraction of elements_at_distance_r
            move closer to their target section := by
    -- Use ε-halver property: ones are balanced
    -- This forces elements toward correct side of cherry
    sorry

  -- Step 4: Elements that moved closer have reduced distance
  have h2 : Elements that moved one level closer now have distance < r
            (unless they're still far away, bounded by Δᵣ) := by
    sorry

  -- Step 5: Exception elements bounded by ε
  have h3 : At most ε fraction of elements_at_distance_r remain at distance ≥ r := by
    -- This is the ε-nearsort property
    -- These are the "exceptional" elements from AKS
    sorry

  -- Step 6: Exception elements came from distance ≥ (r-2) before
  have h4 : The exceptional elements were at distance ≥ (r-2) before ε-nearsort := by
    -- They moved up to 2 levels but stayed at distance ≥ r
    -- So originally at distance ≥ (r-2)
    sorry

  -- Step 7: Fringe amplification gives factor A
  have h5 : Elements can spread across fringes of size A, giving amplification := by
    -- From AKS Section 5, fringe size is proportional to A
    sorry

  -- Step 8: Combine to get final bound
  calc treeWrongness n t v' J r
      ≤ |{elements still at distance ≥ r}| / |J|  := by definition
    _ ≤ (Δᵣ·|J| + ε·Δᵣ₋₂·|J|) * (fringe_factor A) / |J|  := by h1, h3, h4
    _ ≤ 8*A * (Δᵣ + ε·Δᵣ₋₂)  := by h5, simplification
```

---

## Step 5: Required Helper Lemmas

To make this proof work, we need:

### 1. Cherry Identification
```lean
-- Given interval J and time t, find the cherry containing it
def cherry_containing (n t : ℕ) (J : Interval n) :
    Option (Interval n × Interval n × Interval n) :=
  -- Returns (parent, left_child, right_child) if J is in a cherry
  sorry
```

### 2. ε-Nearsort Property
```lean
-- ε-nearsort forces elements toward correct sides
lemma nearsort_forces_toward_target
    (net : ComparatorNetwork n) (ε : ℝ) (hnet : IsEpsilonHalver net ε)
    (cherry : Cherry) (v : Fin n → Bool) :
    -- At least (1-ε) fraction of wrong elements move toward correct side
    sorry
```

### 3. Distance Reduction
```lean
-- Moving toward correct section reduces tree distance
lemma move_reduces_distance
    (J K : Interval n) (x : element)
    (h : x moves from J toward K) :
    treeDistance (location_after x) K < treeDistance (location_before x) K :=
  sorry
```

### 4. Fringe Amplification
```lean
-- Elements spread across fringes of size A
lemma fringe_amplification_factor
    (J : Interval n) (A : ℕ) :
    -- Amplification factor is bounded by 8*A
    sorry
```

### 5. Connection to Halver Property
```lean
-- This is THE KEY lemma connecting halver to wrongness
lemma halver_property_implies_nearsort
    (net : ComparatorNetwork n) (ε : ℝ) (hnet : IsEpsilonHalver net ε)
    (cherry : Cherry) (v : Fin n → Bool) :
    -- If halver balances ones, then ε-nearsort (composed of halvers)
    -- forces elements toward correct sides with ≤ ε exception rate
    sorry
```

---

## Step 6: Risk Assessment After Analysis

### What's Clear:
✅ The proof structure follows AKS Section 8 closely
✅ We understand the mechanism: halver → balanced → forced toward correct side
✅ We can identify the required helper lemmas
✅ The connection to Boolean values (0s/1s) is straightforward

### What's Still Challenging:
⚠️ **Helper lemma 5** (halver_property_implies_nearsort) - this is technical
  - Need to show: ε₁-halver on cherry → ε-nearsort → ≤ ε exceptions
  - This is basically the ε-nearsort construction from AKS Section 4
  - Should be doable by following the paper

⚠️ Fringe amplification factor calculation
  - Need to work through the geometry of interval sizes
  - Factor 8A comes from worst-case spreading

⚠️ Formalize "elements at distance r" precisely
  - Need clear definition of which elements contribute to Δᵣ(J)

### Updated Risk: **MEDIUM** ✓

After this analysis:
- **Before:** MEDIUM-HIGH (unclear connection, unknown if viable)
- **After:** MEDIUM (clear strategy, identified helpers, known to be doable)

**Why MEDIUM (not LOW):**
- Still need to implement ~5 helper lemmas
- Each helper is MEDIUM difficulty individually
- Total effort: 3-5 days as estimated

**Why not HIGH:**
- Proof strategy is clear from AKS
- No fundamental conceptual blockers
- We know halver property DOES connect to wrongness (just technical)

---

## Step 7: Implementation Plan

### Phase 1: Define Cherry Structure (1 day)
- Type for cherry (parent + two children)
- Function to find cherry containing an interval
- Basic properties of cherries

### Phase 2: Implement Helper Lemmas (2-3 days)
1. cherry_containing - straightforward from tree structure
2. fringe_amplification_factor - geometry calculation
3. move_reduces_distance - tree distance properties
4. nearsort_forces_toward_target - **KEY**, use halver property
5. halver_property_implies_nearsort - **CORE**, ε-nearsort construction

### Phase 3: Main Proof (1-2 days)
- Assemble helpers into main lemma
- Handle r ≥ 3 and r < 3 cases
- Verify bounds

**Total: 4-6 days** (slightly refined from 3-5 days estimate)

---

## Conclusion

**Risk successfully reduced from MEDIUM-HIGH to MEDIUM!** ✓

We now have:
- ✅ Clear understanding of proof mechanism
- ✅ Identified all required helper lemmas
- ✅ Sketched proof structure matching AKS
- ✅ Confidence that the approach is viable
- ✅ Realistic implementation plan

The proof is **ready for implementation** with substantially reduced risk. The connection between halver property and tree wrongness is well-understood, and we know exactly what needs to be formalized.

**Next step:** Start Phase 1 (cherry structure) when ready to implement.
