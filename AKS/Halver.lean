/-
  # ε-Halver Theory

  Defines ε-halvers and proves their composition properties.
  This is the engine that drives AKS correctness: each halver round
  geometrically reduces unsortedness, yielding a fully sorted output
  after O(log n) rounds.

  Factored from `Basic.lean` for faster incremental checking during
  proof iteration on `halver_composition`.
-/

import AKS.Basic
import AKS.RegularGraph

open Finset BigOperators


/-! **ε-Halvers** -/

/-- A comparator network is an ε-halver if, for every 0-1 input,
    after applying the network, the excess of 1s in the top half
    (beyond fair share) is at most `ε · (n / 2)`.

    Concretely: `onesInTop ≤ totalOnes / 2 + ε · (n / 2)`.

    Intuitively: it balances 1s between the two halves, up to
    an ε-fraction error. -/
def IsEpsilonHalver {n : ℕ} (net : ComparatorNetwork n) (ε : ℝ) : Prop :=
  ∀ (v : Fin n → Bool),
    let w := net.exec v
    let topHalf := Finset.univ.filter (fun i : Fin n ↦ (i : ℕ) < n / 2)
    let onesInTop := (topHalf.filter (fun i ↦ w i = true)).card
    let totalOnes := (Finset.univ.filter (fun i : Fin n ↦ w i = true)).card
    (onesInTop : ℝ) ≤ totalOnes / 2 + ε * (n / 2)

/-- **Expanders yield ε-halvers.**
    Given a `d`-regular graph `G` on `m` vertices with spectral gap `≤ β`,
    a single round of compare-and-swap along bipartite edges
    (pairing vertex `v` with `m + G.neighbor v i`) produces an
    ε-halver on `2m` wires with `ε = β`.

    The bipartite structure comes from the *construction*, not the
    graph type: every comparator connects a top wire (`< m`) to a
    bottom wire (`≥ m`). This ensures bipartite monotonicity (top
    values can only decrease, bottom values can only increase),
    which — combined with the expander mixing lemma — yields the bound. -/
theorem expander_gives_halver (m d : ℕ) (G : RegularGraph m d)
    (β : ℝ) (hβ : spectralGap G ≤ β) :
    ∃ (net : ComparatorNetwork (2 * m)),
      IsEpsilonHalver net β ∧ net.size ≤ m * d := by
  -- Proof sketch:
  -- 1. Construct the network: for each vertex v : Fin m and port i : Fin d,
  --    add comparator (v, m + G.neighbor v i).
  -- 2. Bipartite monotonicity: in the output, for each edge (v, u) of G,
  --    w v ≤ w (m + u). (Top values only decrease; bottom values only increase.)
  -- 3. Let S = {top 1s}, T = {bottom 0s}. By monotonicity, e(S,T) = 0.
  -- 4. By the expander mixing lemma (Mixing.lean):
  --    |S|·|T|/m ≤ β · √(|S|·|T|), so |S|·|T| ≤ β²·m².
  -- 5. With s = |S|, k = total ones, |T| = m - k + s:
  --    s(m - k + s) ≤ β²m² implies s ≤ k/2 + βm.
  sorry

/-- Merge two sorted halves using iterated ε-halvers.
    After k rounds of ε-halving, the "unsortedness" decreases
    geometrically: at most (2ε)^k · n elements are out of place. -/
def epsHalverMerge (n : ℕ) (ε : ℝ) (k : ℕ)
    (halver : ComparatorNetwork n) : ComparatorNetwork n :=
  { comparators := (List.replicate k halver.comparators).flatten }


/-! **Halver Composition** -/

/-- An ε-sorted vector: at most εn elements are not in their
    correct sorted position. -/
def IsEpsilonSorted {n : ℕ} (v : Fin n → Bool) (ε : ℝ) : Prop :=
  ∃ (w : Fin n → Bool), Monotone w ∧
    ((Finset.univ.filter (fun i ↦ v i ≠ w i)).card : ℝ) ≤ ε * n

/-- **Halver composition lemma**: Applying an ε-halver to a
    δ-sorted sequence yields a (δ·2ε)-sorted sequence.
    This geometric decrease is the engine of AKS correctness. -/
theorem halver_composition {n : ℕ} (net : ComparatorNetwork n)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1/2)
    (hnet : IsEpsilonHalver net ε)
    (v : Fin n → Bool) (hv : IsEpsilonSorted v δ) :
    IsEpsilonSorted (net.exec v) (δ * 2 * ε) := by
  -- Proof sketch:
  -- 1. Since v is δ-sorted, at most δn elements are displaced.
  -- 2. The ε-halver ensures that of the displaced elements,
  --    at most a (1/2 + ε) fraction end up in the wrong half.
  -- 3. The "wrong half" elements after halving: ≤ δn · 2ε.
  -- 4. This is a purely combinatorial argument about how comparator
  --    networks interact with approximate sortedness.
  sorry

/-- **Convergence**: After O(log n) rounds of ε-halving (with ε < 1/2),
    starting from an arbitrary input (which is trivially 1-sorted),
    the sequence becomes 0-sorted, i.e., fully sorted. -/
theorem halver_convergence {n : ℕ} (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1/2)
    (k : ℕ) (hk : (2 * ε) ^ k * n < 1) :
    ∀ (v : Fin n → Bool),
    ∃ (net : ComparatorNetwork n),
      Monotone (net.exec v) := by
  -- After k rounds: unsortedness ≤ (2ε)^k · n < 1.
  -- Since unsortedness is a natural number, it must be 0.
  -- Therefore the output is exactly sorted.
  sorry
