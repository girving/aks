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

open Finset BigOperators


/-! **ε-Halvers** -/

/-- A comparator network is an ε-halver if, for every 0-1 input,
    after applying the network, the top half has at most (1/2 + ε)
    fraction of 1s.

    Intuitively: it pushes 1s toward the bottom half. -/
def IsEpsilonHalver {n : ℕ} (net : ComparatorNetwork n) (ε : ℝ) : Prop :=
  ∀ (v : Fin n → Bool),
    let w := net.exec v
    let topHalf := Finset.univ.filter (fun i : Fin n ↦ (i : ℕ) < n / 2)
    let onesInTop := (topHalf.filter (fun i ↦ w i = true)).card
    (onesInTop : ℝ) ≤ (n / 2 : ℝ) * (1 / 2 + ε)

/-- **Expanders yield ε-halvers.**
    A single round of compare-and-swap along expander edges
    produces an ε-halver with ε = λ₂. This is the core technical
    lemma connecting graph expansion to approximate sorting. -/
theorem expander_gives_halver (n d : ℕ) (G : BipartiteExpander n d)
    (lam₂ : ℝ) (hG : IsExpander n d G lam₂) :
    ∃ (net : ComparatorNetwork (2 * n)),
      IsEpsilonHalver net lam₂ ∧ net.size ≤ n * d := by
  -- Proof sketch:
  -- 1. Construct the network: for each left vertex i and port p,
  --    add comparator (i, n + G.neighbor i p).
  -- 2. The Expander Mixing Lemma shows that for any sets S, T:
  --    |e(S,T) - d|S||T|/n| ≤ λ₂ · d · √(|S|·|T|)
  -- 3. Apply this with S = {1s in top half}, T = {0s in bottom half}
  --    to show enough swaps occur to achieve ε-halving.
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
  -- 4. This requires careful counting using the expander mixing lemma.
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
