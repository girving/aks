/-
  # Regular Graphs and Spectral Theory

  Lean 4 formalization of d-regular graphs via rotation maps,
  their normalized adjacency matrices, spectral gap, graph squaring,
  and the complete graph as a concrete example.

  These definitions and lemmas are general graph theory, used by
  `ZigZag.lean` for the zig-zag product construction and by
  `Basic.lean` (transitively) for the AKS sorting network.
-/

import AKS.Fin
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Matrix.Basic

open Matrix BigOperators Finset


/-! **Regular Graphs and Adjacency Matrices** -/

/-- A d-regular graph on n vertices, represented by a rotation map.

    The rotation map Rot(v, i) = (u, j) means: the i-th edge out of
    vertex v leads to vertex u, and this edge is the j-th edge out of u.

    This representation is essential for defining the zig-zag product
    cleanly, because it tracks the "port" structure at each vertex. -/
structure RegularGraph (n d : ℕ) where
  /-- Rot : V × [d] → V × [d], the rotation map. -/
  rot : Fin n × Fin d → Fin n × Fin d
  /-- Rotation is an involution: following an edge back returns you. -/
  rot_involution : ∀ x, rot (rot x) = x

/-- The vertex reached from v along port i. -/
def RegularGraph.neighbor {n d : ℕ} (G : RegularGraph n d)
    (v : Fin n) (i : Fin d) : Fin n :=
  (G.rot (v, i)).1

/-- The port at the far end of edge (v, i). -/
def RegularGraph.reversePort {n d : ℕ} (G : RegularGraph n d)
    (v : Fin n) (i : Fin d) : Fin d :=
  (G.rot (v, i)).2

theorem RegularGraph.neighbor_reversePort {n d : ℕ} (G : RegularGraph n d)
    (v : Fin n) (i : Fin d) :
    G.neighbor (G.neighbor v i) (G.reversePort v i) = v := by
  unfold RegularGraph.neighbor RegularGraph.reversePort
  rw [Prod.mk.eta]
  exact congr_arg Prod.fst (G.rot_involution (v, i))

theorem RegularGraph.reversePort_reversePort {n d : ℕ} (G : RegularGraph n d)
    (v : Fin n) (i : Fin d) :
    G.reversePort (G.neighbor v i) (G.reversePort v i) = i := by
  unfold RegularGraph.neighbor RegularGraph.reversePort
  rw [Prod.mk.eta]
  exact congr_arg Prod.snd (G.rot_involution (v, i))

/-- The normalized adjacency matrix of a d-regular graph.
    M[u, v] = (number of edges from u to v) / d.

    For a d-regular graph, the top eigenvalue is always 1
    (with eigenvector the all-ones vector), and the spectral gap
    is determined by the second-largest eigenvalue. -/
noncomputable def adjMatrix {n d : ℕ} (G : RegularGraph n d) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun u v ↦
    ((Finset.univ.filter (fun i : Fin d ↦ G.neighbor u i = v)).card : ℝ) / d

@[simp]
theorem adjMatrix_apply {n d : ℕ} (G : RegularGraph n d) (u v : Fin n) :
    adjMatrix G u v =
      ((Finset.univ.filter (fun i : Fin d ↦ G.neighbor u i = v)).card : ℝ) / d :=
  rfl

theorem adjMatrix_isSymm {n d : ℕ} (G : RegularGraph n d) : (adjMatrix G).IsSymm := by
  ext u v
  simp only [Matrix.transpose_apply, adjMatrix_apply]
  congr 1
  exact_mod_cast Finset.card_nbij' (G.reversePort v ·) (G.reversePort u ·)
    (fun i hi ↦ by
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rw [← hi]; exact G.neighbor_reversePort v i)
    (fun j hj ↦ by
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      rw [← hj]; exact G.neighbor_reversePort u j)
    (fun i hi ↦ by
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [← hi]; exact G.reversePort_reversePort v i)
    (fun j hj ↦ by
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [← hj]; exact G.reversePort_reversePort u j)

theorem adjMatrix_isHermitian {n d : ℕ} (G : RegularGraph n d) :
    (adjMatrix G).IsHermitian := by
  show (adjMatrix G)ᴴ = adjMatrix G
  rw [conjTranspose_eq_transpose_of_trivial]
  exact adjMatrix_isSymm G


/-! **Spectral Gap** -/

/-- The spectral gap λ(G): the second-largest singular value of the
    normalized adjacency matrix.

    Equivalently, the operator norm of M restricted to the subspace
    orthogonal to the all-ones vector:

      λ(G) = max { |⟨Mx, x⟩| / ⟨x, x⟩ : x ⊥ 𝟏 }

    We have 0 ≤ λ(G) ≤ 1, with λ(G) close to 0 meaning
    excellent expansion. -/
noncomputable def spectralGap {n d : ℕ} (G : RegularGraph n d) : ℝ :=
  if h : n ≤ 1 then 0
  else
    let evs := (adjMatrix_isHermitian G).eigenvalues₀
    max (evs ⟨1, by rw [Fintype.card_fin]; omega⟩)
        (-(evs ⟨n - 1, by rw [Fintype.card_fin]; omega⟩))

/-- Basic property: the spectral gap lies in [0, 1]. -/
theorem spectralGap_nonneg {n d : ℕ} (G : RegularGraph n d) :
    0 ≤ spectralGap G := by
  unfold spectralGap
  split_ifs with h
  · exact le_refl _
  · push_neg at h
    have hanti := (adjMatrix_isHermitian G).eigenvalues₀_antitone
    have hle : (⟨1, by rw [Fintype.card_fin]; omega⟩ : Fin (Fintype.card (Fin n))) ≤
               ⟨n - 1, by rw [Fintype.card_fin]; omega⟩ := by
      simp only [Fin.le_iff_val_le_val]; omega
    by_cases hev : 0 ≤ (adjMatrix_isHermitian G).eigenvalues₀
        ⟨1, by rw [Fintype.card_fin]; omega⟩
    · exact le_max_of_le_left hev
    · push_neg at hev
      exact le_max_of_le_right (by linarith [hanti hle])

theorem spectralGap_le_one {n d : ℕ} (G : RegularGraph n d) :
    spectralGap G ≤ 1 := by
  sorry

/-- The Expander Mixing Lemma: the spectral gap controls edge
    distribution. For any two vertex sets S, T ⊆ V:

      |e(S,T)/d - |S|·|T|/n| ≤ λ(G) · √(|S|·|T|)

    This is the link between spectral and combinatorial expansion. -/
theorem expander_mixing_lemma {n d : ℕ} (G : RegularGraph n d)
    (S T : Finset (Fin n)) :
    |((Finset.sum S fun v ↦ (T.filter (fun u ↦
        ∃ i : Fin d, G.neighbor v i = u)).card) : ℝ) / d
      - S.card * T.card / n|
    ≤ spectralGap G * Real.sqrt (S.card * T.card) := by
  -- Standard proof via Cauchy–Schwarz on the adjacency matrix
  -- restricted to 𝟏⊥. The key step is decomposing indicator
  -- vectors 1_S and 1_T into their projections onto 𝟏 and 𝟏⊥,
  -- then bounding the cross term using the spectral gap.
  sorry


/-! **Graph Squaring** -/

-- The square G² of a d-regular graph: take two steps.
-- G² is d²-regular. Rot_{G²}(v, (i,j)) follows edge i from v,
-- then edge j from the result.

/-- The rotation map for G²: decode port as (i,j), take step i then step j,
    encode the reverse ports as j'*d + i'. Uses projections (not destructuring)
    so that simp can work with it. -/
private def square_rot {n d : ℕ} (G : RegularGraph n d)
    (p : Fin n × Fin (d * d)) : Fin n × Fin (d * d) :=
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; exact absurd p.2.isLt (by simp))
  let i : Fin d := ⟨p.2.val / d, (Nat.div_lt_iff_lt_mul hd).mpr p.2.isLt⟩
  let j : Fin d := ⟨p.2.val % d, Nat.mod_lt _ hd⟩
  let step1 := G.rot (p.1, i)
  let step2 := G.rot (step1.1, j)
  (step2.1, ⟨step2.2.val * d + step1.2.val, Fin.pair_lt step2.2 step1.2⟩)

private theorem square_rot_involution {n d : ℕ} (G : RegularGraph n d)
    (p : Fin n × Fin (d * d)) : square_rot G (square_rot G p) = p := by
  obtain ⟨v, ij⟩ := p
  simp only [square_rot, fin_encode_fst, fin_encode_snd, Prod.mk.eta, G.rot_involution,
    fin_div_add_mod]

def RegularGraph.square {n d : ℕ} (G : RegularGraph n d) :
    RegularGraph n (d * d) where
  rot := square_rot G
  rot_involution := square_rot_involution G

/-- **Squaring squares the spectral gap.**

    λ(G²) = λ(G)²

    This is immediate: the adjacency matrix of G² is M², and
    if Mx = λx then M²x = λ²x. -/
theorem spectralGap_square {n d : ℕ} (G : RegularGraph n d) :
    spectralGap G.square = (spectralGap G) ^ 2 := by
  -- The normalized adjacency matrix of G² is (adjMatrix G)².
  -- Eigenvalues of M² are squares of eigenvalues of M.
  -- The second-largest eigenvalue of M² is the square of the
  -- second-largest eigenvalue of M.
  sorry


/-! **Complete Graph** -/

/-- Rotation map for the complete graph K_{n+1}: the i-th neighbor of v is
    obtained by skipping v in the enumeration, using `Fin.succAbove`.
    The reverse port is `Fin.predAbove`. -/
private def complete_rot {n : ℕ}
    (p : Fin (n + 1) × Fin n) : Fin (n + 1) × Fin n :=
  (p.1.succAbove p.2, p.2.predAbove p.1)

private theorem complete_rot_involution {n : ℕ}
    (p : Fin (n + 1) × Fin n) :
    complete_rot (complete_rot p) = p := by
  simp only [complete_rot, Fin.succAbove_succAbove_predAbove,
    Fin.predAbove_predAbove_succAbove, Prod.mk.eta]

/-- The complete graph on `n + 1` vertices as a regular graph.
    K_{n+1} is n-regular. λ(K_{n+1}) = 1/n. -/
def completeGraph (n : ℕ) : RegularGraph (n + 1) n where
  rot := complete_rot
  rot_involution := complete_rot_involution

/-- The spectral gap of the complete graph. -/
theorem spectralGap_complete (n : ℕ) (hn : n ≥ 1) :
    spectralGap (completeGraph n) = 1 / (n : ℝ) := by
  -- The eigenvalues of the normalized adjacency matrix of K_{n+1} are:
  --   1 (multiplicity 1) and -1/n (multiplicity n).
  -- So λ(K_{n+1}) = 1/n.
  sorry
