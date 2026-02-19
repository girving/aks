/-
  # Shrinking Bipartite Halvers

  Restricts a bipartite halver on 2M wires to 2n wires (n ≤ M), keeping only
  comparators where both endpoints are in the first n wires per half.

  The construction is purely about comparator networks — no graph theory needed.
  The quality analysis uses the padding argument: running the shrunk halver on
  input τ is equivalent to running the big halver on a padded input (M-n copies
  of -∞ in top, +∞ in bottom) and projecting to real wires. Bipartiteness
  ensures padding elements are invisible to all comparators.

  **Quality:** For segment k, the misplacement count is at most ε · (M - n + k).
  The uniform `IsEpsilonHalver` parameter is ε · (M - n + 1). The main halving
  bound (k = n) gives ε · M, i.e., quality ε · M / n as a fraction of n.
-/

import AKS.Halver.Defs

open Finset BigOperators


/-! **Bipartite Networks** -/

/-- A network on `2 * M` wires is bipartite: every comparator connects
    a top wire (`i.val < M`) to a bottom wire (`M ≤ j.val`). -/
def ComparatorNetwork.IsBipartite {M : ℕ} (net : ComparatorNetwork (2 * M)) : Prop :=
  ∀ c ∈ net.comparators, c.i.val < M ∧ M ≤ c.j.val


/-! **Shrinking Construction** -/

/-- Restrict a halver on `2 * M` wires to `2 * n` wires (`n ≤ M`).
    Keeps comparators `(i, j)` where `i < n` and `j ∈ [M, M + n)`,
    renumbering bottom wires `j ↦ n + (j - M)`. Comparators outside
    this range (including any non-bipartite ones) are dropped. -/
def shrinkHalver {M : ℕ} (net : ComparatorNetwork (2 * M)) (n : ℕ) (hn : n ≤ M) :
    ComparatorNetwork (2 * n) :=
  { comparators := net.comparators.filterMap fun c =>
      if h : c.i.val < n ∧ M ≤ c.j.val ∧ c.j.val < M + n then
        some ⟨⟨c.i.val, by omega⟩,
              ⟨n + (c.j.val - M), by omega⟩,
              by simp [Fin.lt_iff_val_lt_val]; omega⟩
      else none }

/-- Shrinking to the same size is the identity (for bipartite networks). -/
theorem shrinkHalver_self {M : ℕ} (net : ComparatorNetwork (2 * M))
    (hbip : net.IsBipartite) :
    shrinkHalver net M le_rfl = net := by
  sorry

/-- The shrunk halver is bipartite. -/
theorem shrinkHalver_isBipartite {M : ℕ} (net : ComparatorNetwork (2 * M))
    (n : ℕ) (hn : n ≤ M) :
    (shrinkHalver net n hn).IsBipartite := by
  sorry

/-- The shrunk halver has at most as many comparators as the original. -/
theorem shrinkHalver_size_le {M : ℕ} (net : ComparatorNetwork (2 * M))
    (n : ℕ) (hn : n ≤ M) :
    (shrinkHalver net n hn).size ≤ net.size := by
  sorry


/-! **Quality Bounds** -/

/-- **Per-segment initial bound.** If the original is a bipartite ε-halver on
    `2 * M` wires, the shrunk halver on `2 * n` wires satisfies: at most
    `ε · (M - n + k)` bottom-half positions have output rank `< k`.

    Proof sketch: embed `Perm (Fin (2n))` into `Perm (Fin (2M))` by padding:
    - Phantom-top wires (positions `n..M-1`): smallest values (ranks `0..M-n-1`)
    - Real wires: middle values (ranks `M-n..M+n-1`)
    - Phantom-bottom wires (`M+n..2M-1`): largest values (ranks `M+n..2M-1`)

    Bipartiteness ensures: a comparator between a phantom wire and a real wire
    is always a no-op (phantom-top < real, real < phantom-bottom). So the big
    halver's output on real wires equals the shrunk halver's output. The big
    halver's segment bound at threshold `M - n + k` gives the result. -/
theorem shrinkHalver_initialBound {M : ℕ} (net : ComparatorNetwork (2 * M))
    (hbip : net.IsBipartite) (ε : ℝ) (hε : IsEpsilonHalver net ε)
    (n : ℕ) (hn : 0 < n) (hnM : n ≤ M)
    (v : Equiv.Perm (Fin (2 * n))) (k : ℕ) (hk : k ≤ n) :
    ((univ.filter (fun pos : Fin (2 * n) ↦
        n ≤ rank pos ∧
        rank ((shrinkHalver net n hnM).exec v pos) < k)).card : ℝ) ≤
      ε * (↑M - ↑n + ↑k) := by
  sorry

/-- **Per-segment final bound** (dual of initial). -/
theorem shrinkHalver_finalBound {M : ℕ} (net : ComparatorNetwork (2 * M))
    (hbip : net.IsBipartite) (ε : ℝ) (hε : IsEpsilonHalver net ε)
    (n : ℕ) (hn : 0 < n) (hnM : n ≤ M)
    (v : Equiv.Perm (Fin (2 * n))) (k : ℕ) (hk : k ≤ n) :
    ((univ.filter (fun pos : Fin (2 * n) ↦
        pos.val < n ∧
        2 * n - k ≤ ((shrinkHalver net n hnM).exec v pos).val)).card : ℝ) ≤
      ε * (↑M - ↑n + ↑k) := by
  sorry

/-- **Uniform `IsEpsilonHalver` bound:** `ε' = ε · (M - n + 1)`.

    This is the tightest uniform bound: at `k = 1`, the per-segment bound gives
    `ε · (M - n + 1)`, and `ε · (M - n + k) ≤ ε · (M - n + 1) · k` for `k ≥ 1`.

    **Note:** `ε'` grows with `M - n`. The main halving bound (k = n) gives
    the tighter `ε · M` (i.e., quality `ε · M / n` as a fraction of `n`). -/
theorem shrinkHalver_isEpsilonHalver {M : ℕ} (net : ComparatorNetwork (2 * M))
    (hbip : net.IsBipartite) (ε : ℝ) (hε : IsEpsilonHalver net ε) (hε_nn : 0 ≤ ε)
    (n : ℕ) (hn : 0 < n) (hnM : n ≤ M) :
    IsEpsilonHalver (shrinkHalver net n hnM) (ε * (↑(M - n) + 1)) := by
  sorry


