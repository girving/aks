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
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix

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
      rw [← hi]; apply G.neighbor_reversePort)
    (fun j hj ↦ by
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      rw [← hj]; apply G.neighbor_reversePort)
    (fun i hi ↦ by
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [← hi]; apply G.reversePort_reversePort)
    (fun j hj ↦ by
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [← hj]; apply G.reversePort_reversePort)

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

private theorem adjMatrix_entry_nonneg {n d : ℕ} (G : RegularGraph n d) (u v : Fin n) :
    0 ≤ adjMatrix G u v :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private theorem adjMatrix_norm_row_sum_le {n d : ℕ} (G : RegularGraph n d) (u : Fin n) :
    ∑ v, ‖adjMatrix G u v‖ ≤ 1 := by
  simp_rw [Real.norm_of_nonneg (adjMatrix_entry_nonneg G u _), adjMatrix_apply, ← Finset.sum_div]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have h_nat : (Finset.univ : Finset (Fin d)).card =
        ∑ v ∈ (Finset.univ : Finset (Fin n)),
          (Finset.univ.filter (fun i : Fin d ↦ G.neighbor u i = v)).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ ↦ Finset.mem_coe.mpr (Finset.mem_univ _))
    simp only [Finset.card_univ, Fintype.card_fin] at h_nat
    have h_sum : (∑ v : Fin n,
        ((Finset.univ.filter (fun i : Fin d ↦ G.neighbor u i = v)).card : ℝ)) = d := by
      exact_mod_cast h_nat.symm
    rw [h_sum, div_self (Nat.cast_ne_zero.mpr (by omega))]

private theorem adjMatrix_eigenvalue_abs_le_one {n d : ℕ} (G : RegularGraph n d)
    {μ : ℝ} (hμ : μ ∈ spectrum ℝ (adjMatrix G)) : |μ| ≤ 1 := by
  rw [← Matrix.spectrum_toLin'] at hμ
  have hev : Module.End.HasEigenvalue (Matrix.toLin' (adjMatrix G)) μ :=
    Module.End.HasEigenvalue.of_mem_spectrum hμ
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hev
  rw [Metric.mem_closedBall] at hk
  have hnn := adjMatrix_entry_nonneg G k k
  calc |μ| = ‖μ‖ := (Real.norm_eq_abs μ).symm
    _ = dist μ 0 := (dist_zero_right μ).symm
    _ ≤ dist μ (adjMatrix G k k) + dist (adjMatrix G k k) 0 := dist_triangle _ _ _
    _ = dist μ (adjMatrix G k k) + ‖adjMatrix G k k‖ := by rw [dist_zero_right]
    _ ≤ (∑ j ∈ Finset.univ.erase k, ‖adjMatrix G k j‖) + ‖adjMatrix G k k‖ := by
        linarith
    _ = ∑ j, ‖adjMatrix G k j‖ := Finset.sum_erase_add _ _ (Finset.mem_univ k)
    _ ≤ 1 := adjMatrix_norm_row_sum_le G k

theorem spectralGap_le_one {n d : ℕ} (G : RegularGraph n d) :
    spectralGap G ≤ 1 := by
  unfold spectralGap
  split_ifs with h
  · linarith
  · push_neg at h
    set hA := adjMatrix_isHermitian G
    apply max_le
    · -- evs ⟨1, _⟩ ≤ 1
      have hmem : hA.eigenvalues₀ ⟨1, by rw [Fintype.card_fin]; omega⟩ ∈
          spectrum ℝ (adjMatrix G) := by
        rw [hA.spectrum_real_eq_range_eigenvalues]
        exact ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)) ⟨1, by rw [Fintype.card_fin]; omega⟩,
          by unfold Matrix.IsHermitian.eigenvalues; simp [Equiv.symm_apply_apply]⟩
      exact le_of_abs_le (adjMatrix_eigenvalue_abs_le_one G hmem)
    · -- -(evs ⟨n-1, _⟩) ≤ 1
      have hmem : hA.eigenvalues₀ ⟨n - 1, by rw [Fintype.card_fin]; omega⟩ ∈
          spectrum ℝ (adjMatrix G) := by
        rw [hA.spectrum_real_eq_range_eigenvalues]
        exact ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)) ⟨n - 1, by rw [Fintype.card_fin]; omega⟩,
          by unfold Matrix.IsHermitian.eigenvalues; simp [Equiv.symm_apply_apply]⟩
      have := adjMatrix_eigenvalue_abs_le_one G hmem
      linarith [abs_le.mp this]

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

private theorem square_neighbor_unfold {n d : ℕ} (G : RegularGraph n d)
    (u : Fin n) (p : Fin (d * d)) (hd : 0 < d) :
    G.square.neighbor u p =
      G.neighbor (G.neighbor u ⟨p.val / d, (Nat.div_lt_iff_lt_mul hd).mpr p.isLt⟩)
        ⟨p.val % d, Nat.mod_lt _ hd⟩ := rfl

private theorem adjMatrix_square_eq_sq {n d : ℕ} (G : RegularGraph n d) :
    adjMatrix G.square = (adjMatrix G) ^ 2 := by
  ext u v
  simp only [adjMatrix_apply, sq, Matrix.mul_apply, div_mul_div_comm]
  rw [← Finset.sum_div, Nat.cast_mul]
  congr 1
  -- Need: ↑(filter card) = ∑ w, ↑card_uw * ↑card_wv  (as ℝ)
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · -- Prove the Nat-level identity and cast
    have key : (univ.filter (fun p : Fin (d * d) ↦ G.square.neighbor u p = v)).card =
        ∑ w : Fin n, (univ.filter (fun i : Fin d ↦ G.neighbor u i = w)).card *
          (univ.filter (fun j : Fin d ↦ G.neighbor w j = v)).card := by
      -- Partition by intermediate vertex
      rw [Finset.card_eq_sum_card_fiberwise
        (f := fun p ↦ G.neighbor u ⟨p.val / d, (Nat.div_lt_iff_lt_mul hd).mpr p.isLt⟩)
        (fun _ _ ↦ Finset.mem_coe.mpr (Finset.mem_univ _))]
      congr 1; ext w
      -- Fiber card = card_uw * card_wv
      rw [← Finset.card_product]
      apply Finset.card_nbij'
        -- forward: decode port p as (p/d, p%d)
        (fun p ↦ (⟨p.val / d, (Nat.div_lt_iff_lt_mul hd).mpr p.isLt⟩,
                   ⟨p.val % d, Nat.mod_lt _ hd⟩))
        -- backward: encode (i, j) as i * d + j
        (fun ij ↦ ⟨ij.1.val * d + ij.2.val, Fin.pair_lt ij.1 ij.2⟩)
      -- forward MapsTo
      · intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_product] at hp ⊢
        exact ⟨hp.2, by rw [← hp.2, ← square_neighbor_unfold G u p hd]; exact hp.1⟩
      -- backward MapsTo
      · intro ij hij
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_product] at hij ⊢
        constructor
        · -- G.square.neighbor u ⟨i*d+j, _⟩ = v
          rw [square_neighbor_unfold G u _ hd, fin_encode_fst, fin_encode_snd]
          rw [hij.1]; exact hij.2
        · -- G.neighbor u ⟨(i*d+j)/d, _⟩ = w
          have := fin_encode_fst ij.1 ij.2
            ((Nat.div_lt_iff_lt_mul hd).mpr (Fin.pair_lt ij.1 ij.2))
          simp only [this]; exact hij.1
      -- LeftInvOn: backward ∘ forward = id
      · intro p hp
        exact fin_div_add_mod p _
      -- RightInvOn: forward ∘ backward = id
      · intro ij hij
        refine Prod.ext ?_ ?_
        · exact fin_encode_fst ij.1 ij.2
            ((Nat.div_lt_iff_lt_mul hd).mpr (Fin.pair_lt ij.1 ij.2))
        · exact fin_encode_snd ij.1 ij.2 (Nat.mod_lt _ hd)
    exact_mod_cast key

/-- Each eigenvalue of M² is a square of some eigenvalue of M.
    The spectral theorem gives eigenbasis `{vᵢ}` with `Mvᵢ = λᵢvᵢ`,
    so `M²vᵢ = λᵢ²vᵢ`. Since `{vᵢ}` is a complete basis, the
    eigenvalues of M² are exactly `{λᵢ²}` as a multiset.
    Formalizing this requires connecting the eigenvector bases of M and M²
    (e.g., via `ContinuousFunctionalCalculus` spectral mapping, which
    needs a `CStarAlgebra` instance not yet available for `Matrix _ _ ℝ`). -/
private theorem eigenvalues₀_pow_sq {n : ℕ} (_hn : 1 < n)
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    (i : Fin (Fintype.card (Fin n))) :
    ∃ j, (hM.pow 2).eigenvalues₀ i = (hM.eigenvalues₀ j) ^ 2 := by
  open Polynomial in
  -- charpoly of M^2 factors over squared eigenvalues via CFC
  have hcp : (M ^ 2).charpoly = ∏ j, (Polynomial.X - Polynomial.C ((hM.eigenvalues j) ^ 2)) := by
    conv_lhs => rw [← cfc_pow_id (R := ℝ) M 2 hM.isSelfAdjoint]
    exact hM.charpoly_cfc_eq (· ^ 2)
  -- eigenvalues₀ i is in the spectrum of M^2
  have hmem : (hM.pow 2).eigenvalues₀ i ∈ spectrum ℝ (M ^ 2) := by
    rw [(hM.pow 2).spectrum_real_eq_range_eigenvalues]
    exact ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)) i, by
      unfold Matrix.IsHermitian.eigenvalues; simp [Equiv.symm_apply_apply]⟩
  -- convert to root of charpoly, use product factorization
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hcp, Polynomial.isRoot_prod] at hmem
  obtain ⟨j, -, hj⟩ := hmem
  rw [Polynomial.root_X_sub_C] at hj
  -- lift from eigenvalues j to eigenvalues₀
  refine ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)).symm j, ?_⟩
  rw [← hj]
  unfold Matrix.IsHermitian.eigenvalues; simp

/-- Reverse direction: each squared eigenvalue of M appears among eigenvalues of M². -/
private theorem eigenvalue_sq_mem_eigenvalues₀_sq {n : ℕ} (_hn : 1 < n)
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    (j : Fin (Fintype.card (Fin n))) :
    ∃ i, (hM.pow 2).eigenvalues₀ i = (hM.eigenvalues₀ j) ^ 2 := by
  open Polynomial in
  -- charpoly of M^2 factors over squared eigenvalues
  have hcp : (M ^ 2).charpoly = ∏ k, (Polynomial.X - Polynomial.C ((hM.eigenvalues k) ^ 2)) := by
    conv_lhs => rw [← cfc_pow_id (R := ℝ) M 2 hM.isSelfAdjoint]
    exact hM.charpoly_cfc_eq (· ^ 2)
  -- hM.eigenvalues₀ j ^ 2 is a root of (M^2).charpoly
  have hroot : (M ^ 2).charpoly.IsRoot (hM.eigenvalues₀ j ^ 2) := by
    rw [hcp, isRoot_prod]
    refine ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)) j, Finset.mem_univ _, ?_⟩
    rw [root_X_sub_C]
    unfold Matrix.IsHermitian.eigenvalues; simp
  -- so it's in the spectrum
  have hmem : hM.eigenvalues₀ j ^ 2 ∈ spectrum ℝ (M ^ 2) :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot
  -- spectrum = range of eigenvalues
  rw [(hM.pow 2).spectrum_real_eq_range_eigenvalues] at hmem
  obtain ⟨k, hk⟩ := hmem
  exact ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)).symm k, by
    rw [← hk]; unfold Matrix.IsHermitian.eigenvalues; simp⟩

/-- Row sums of the adjacency matrix equal 1 when d ≥ 1. -/
private theorem adjMatrix_row_sum {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d)
    (u : Fin n) : ∑ v, adjMatrix G u v = 1 := by
  simp_rw [adjMatrix_apply, ← Finset.sum_div]
  have h_nat : (Finset.univ : Finset (Fin d)).card =
      ∑ v ∈ (Finset.univ : Finset (Fin n)),
        (Finset.univ.filter (fun i : Fin d ↦ G.neighbor u i = v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ ↦ Finset.mem_coe.mpr (Finset.mem_univ _))
  simp only [Finset.card_univ, Fintype.card_fin] at h_nat
  have h_sum : (∑ v : Fin n,
      ((Finset.univ.filter (fun i : Fin d ↦ G.neighbor u i = v)).card : ℝ)) = d := by
    exact_mod_cast h_nat.symm
  rw [h_sum, div_self (Nat.cast_ne_zero.mpr (by omega))]

/-- 1 is in the spectrum of any regular graph's adjacency matrix (when d ≥ 1). -/
private theorem one_mem_spectrum_adjMatrix {n d : ℕ} (G : RegularGraph n d)
    (hn : 1 < n) (hd : 0 < d) : (1 : ℝ) ∈ spectrum ℝ (adjMatrix G) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot, Matrix.eval_charpoly]
  -- The all-ones vector is an eigenvector with eigenvalue 1
  have hmv : adjMatrix G *ᵥ (fun _ ↦ 1 : Fin n → ℝ) = fun _ ↦ 1 := by
    ext u; simp only [Matrix.mulVec, dotProduct, mul_one]
    exact adjMatrix_row_sum G hd u
  have hne : (fun _ : Fin n ↦ (1 : ℝ)) ≠ 0 := by
    intro h; have := congr_fun h ⟨0, by omega⟩; simp at this
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨fun _ ↦ 1, hne, by
    ext u; simp [Matrix.sub_mulVec, hmv, Matrix.scalar]⟩

/-- The top eigenvalue of a regular graph's adjacency matrix is 1 (when d ≥ 1). -/
private theorem adjMatrix_top_eigenvalue {n d : ℕ} (G : RegularGraph n d) (hn : 1 < n)
    (hd : 0 < d) :
    (adjMatrix_isHermitian G).eigenvalues₀ ⟨0, by rw [Fintype.card_fin]; omega⟩ = 1 := by
  set hA := adjMatrix_isHermitian G
  set i0 : Fin (Fintype.card (Fin n)) := ⟨0, by rw [Fintype.card_fin]; omega⟩
  apply le_antisymm
  · -- ≤ 1: from |eigenvalue| ≤ 1
    have hmem : hA.eigenvalues₀ i0 ∈ spectrum ℝ (adjMatrix G) := by
      rw [hA.spectrum_real_eq_range_eigenvalues]
      exact ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)) i0, by
        unfold Matrix.IsHermitian.eigenvalues; simp [Equiv.symm_apply_apply]⟩
    exact le_of_abs_le (adjMatrix_eigenvalue_abs_le_one G hmem)
  · -- ≥ 1: eigenvalues₀ ⟨0, _⟩ is the max, and 1 is an eigenvalue
    have h1 := one_mem_spectrum_adjMatrix G hn hd
    rw [hA.spectrum_real_eq_range_eigenvalues] at h1
    obtain ⟨j, hj⟩ := h1
    have : hA.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j) = 1 := by
      rw [← hj]; unfold Matrix.IsHermitian.eigenvalues; simp
    rw [← this]
    haveI : NeZero (Fintype.card (Fin n)) := ⟨by rw [Fintype.card_fin]; omega⟩
    exact hA.eigenvalues₀_antitone (Fin.zero_le _)

/-- For a ≥ x ≥ c, we have x² ≤ max(a², c²). -/
private theorem sq_le_max_sq {a x c : ℝ} (hax : a ≥ x) (hxc : x ≥ c) :
    x ^ 2 ≤ max (a ^ 2) (c ^ 2) := by
  by_cases hx : x ≤ 0
  · exact le_max_of_le_right (by nlinarith)
  · exact le_max_of_le_left (by nlinarith)

/-- Transport: eigenvalues₀ are the same for equal matrices. -/
private theorem eigenvalues₀_congr {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (i : Fin (Fintype.card (Fin n))) :
    hA.eigenvalues₀ i = hB.eigenvalues₀ i := by
  subst h; rfl

/-- The eigenvalue multisets of M² and {λ_j²} agree (via charpoly root equality). -/
private theorem eigenvalue_multiset_sq {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) :
    Finset.univ.val.map (fun j ↦ (hM.pow 2).eigenvalues j) =
    Finset.univ.val.map (fun j ↦ hM.eigenvalues j ^ 2) := by
  open Polynomial in
  have hcp1 : (M ^ 2).charpoly = ∏ j, (X - C ((hM.pow 2).eigenvalues j : ℝ)) :=
    (hM.pow 2).charpoly_eq
  have hcp2 : (M ^ 2).charpoly = ∏ j, (X - C ((hM.eigenvalues j) ^ 2)) := by
    conv_lhs => rw [← cfc_pow_id (R := ℝ) M 2 hM.isSelfAdjoint]
    exact hM.charpoly_cfc_eq (· ^ 2)
  -- Both factorizations give the same polynomial, so their root multisets agree
  have heq : ∏ j : Fin n, (X - C ((hM.pow 2).eigenvalues j : ℝ)) =
             ∏ j : Fin n, (X - C ((hM.eigenvalues j) ^ 2)) := by
    rw [← hcp1, ← hcp2]
  -- Use roots_multiset_prod_X_sub_C to extract multisets
  have hr1 := roots_multiset_prod_X_sub_C (R := ℝ)
    (Finset.univ.val.map (fun j : Fin n ↦ ((hM.pow 2).eigenvalues j : ℝ)))
  have hr2 := roots_multiset_prod_X_sub_C (R := ℝ)
    (Finset.univ.val.map (fun j : Fin n ↦ (hM.eigenvalues j ^ 2 : ℝ)))
  simp only [Multiset.map_map, Function.comp] at hr1 hr2
  -- Equal polynomials have equal roots
  rw [← hr1, ← hr2]
  congr 1

/-! **Projection and Spectral Gap Recharacterization** -/

/-- The uniform projection matrix: all entries equal 1/n. -/
private noncomputable def uniformProj (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun _ _ ↦ (1 : ℝ) / n)

@[simp] private theorem uniformProj_apply {n : ℕ} (u v : Fin n) :
    uniformProj n u v = 1 / n := rfl

private theorem uniformProj_isSymm {n : ℕ} : (uniformProj n).IsSymm := by
  ext u v; simp

private theorem uniformProj_isHermitian {n : ℕ} : (uniformProj n).IsHermitian := by
  show (uniformProj n)ᴴ = uniformProj n
  rw [conjTranspose_eq_transpose_of_trivial]
  exact uniformProj_isSymm.eq

private theorem adjMatrix_mul_uniformProj {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d) :
    adjMatrix G * uniformProj n = uniformProj n := by
  ext u v
  simp only [Matrix.mul_apply, uniformProj_apply, mul_one_div, ← Finset.sum_div,
    adjMatrix_row_sum G hd u]

private theorem uniformProj_mul_adjMatrix {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d) :
    uniformProj n * adjMatrix G = uniformProj n := by
  have h := adjMatrix_mul_uniformProj G hd
  calc uniformProj n * adjMatrix G
      = ((uniformProj n * adjMatrix G)ᵀ)ᵀ := (Matrix.transpose_transpose _).symm
    _ = ((adjMatrix G)ᵀ * (uniformProj n)ᵀ)ᵀ := by rw [Matrix.transpose_mul]
    _ = (adjMatrix G * uniformProj n)ᵀ := by
        rw [(adjMatrix_isSymm G).eq, uniformProj_isSymm.eq]
    _ = (uniformProj n)ᵀ := by rw [h]
    _ = uniformProj n := uniformProj_isSymm.eq

private theorem uniformProj_sq {n : ℕ} (hn : 0 < n) :
    uniformProj n * uniformProj n = uniformProj n := by
  ext u v
  simp only [Matrix.mul_apply, uniformProj_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

private theorem sub_uniformProj_isHermitian {n d : ℕ} (G : RegularGraph n d) :
    (adjMatrix G - uniformProj n).IsHermitian := by
  show (adjMatrix G - uniformProj n)ᴴ = adjMatrix G - uniformProj n
  rw [conjTranspose_sub, adjMatrix_isHermitian G, uniformProj_isHermitian]

/-- Key identity: (M - P)² = M² - P, from MP = PM = P and P² = P. -/
private theorem sq_sub_uniformProj {n d : ℕ} (G : RegularGraph n d)
    (hd : 0 < d) (hn : 0 < n) :
    (adjMatrix G - uniformProj n) ^ 2 = (adjMatrix G) ^ 2 - uniformProj n := by
  rw [sq, sq, sub_mul, mul_sub, mul_sub,
    adjMatrix_mul_uniformProj G hd, uniformProj_mul_adjMatrix G hd,
    uniformProj_sq hn, sub_self, sub_zero]

/-- Helper: the sum ∑ i, v i = 0 for an eigenvector of M with eigenvalue μ₀ ≠ 1. -/
private theorem eigenvec_sum_eq_zero {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d)
    {μ₀ : ℝ} {v : Fin n → ℝ} (hv : adjMatrix G *ᵥ v = μ₀ • v) (hmu1 : μ₀ ≠ 1) :
    ∑ i, v i = 0 := by
  have h1 : ∑ u, (adjMatrix G *ᵥ v) u = ∑ u, v u := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]; congr 1; ext j
    simp_rw [show ∀ i, adjMatrix G i j = adjMatrix G j i from
      fun i ↦ ((adjMatrix_isSymm G).apply i j).symm]
    rw [← Finset.sum_mul, adjMatrix_row_sum G hd j, one_mul]
  have h2 : ∑ u, (adjMatrix G *ᵥ v) u = μ₀ * ∑ u, v u := by
    simp only [hv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  have h0 : (1 - μ₀) * ∑ u, v u = 0 := by linarith [h1.symm.trans h2]
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (Ne.symm hmu1))

/-- Helper: P *ᵥ v = 0 when ∑ v = 0. -/
private theorem uniformProj_mulVec_eq_zero {n : ℕ}
    {v : Fin n → ℝ} (h_sum : ∑ i, v i = 0) :
    uniformProj n *ᵥ v = 0 := by
  ext i; simp only [Matrix.mulVec, dotProduct, uniformProj_apply, Pi.zero_apply]
  rw [← Finset.mul_sum, h_sum, mul_zero]

/-- Eigenvectors of M with eigenvalue ≠ 1 are also eigenvectors of M - P. -/
private theorem eigenvalue_sub_uniformProj_of_ne_one {n d : ℕ} (G : RegularGraph n d)
    (hd : 0 < d) {μ₀ : ℝ} (hmu : μ₀ ∈ spectrum ℝ (adjMatrix G)) (hmu1 : μ₀ ≠ 1) :
    μ₀ ∈ spectrum ℝ (adjMatrix G - uniformProj n) := by
  -- Get eigenvector v with Mv = μ₀ • v, v ≠ 0
  rw [← Matrix.spectrum_toLin'] at hmu
  obtain ⟨v, hv⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hmu).exists_hasEigenvector
  have hv_eq : adjMatrix G *ᵥ v = μ₀ • v := by
    have := hv.apply_eq_smul; rwa [Matrix.toLin'_apply] at this
  have h_sum := eigenvec_sum_eq_zero G hd hv_eq hmu1
  have hPv := uniformProj_mulVec_eq_zero h_sum
  -- (M - P) *ᵥ v = μ₀ • v
  have hMPv : (adjMatrix G - uniformProj n) *ᵥ v = μ₀ • v := by
    rw [Matrix.sub_mulVec, hv_eq, hPv, sub_zero]
  -- Conclude via charpoly (matching one_mem_spectrum_adjMatrix pattern)
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot, Matrix.eval_charpoly]
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv.2, by
    rw [Matrix.sub_mulVec]
    have hsv : Matrix.scalar (Fin n) μ₀ *ᵥ v = μ₀ • v := by
      rw [show Matrix.scalar (Fin n) μ₀ = μ₀ • (1 : Matrix _ _ ℝ) from
        Algebra.algebraMap_eq_smul_one μ₀, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hsv, hMPv, sub_self]⟩

/-- Non-zero eigenvalues of M - P are eigenvalues of M (with eigenvectors ⊥ 1). -/
private theorem eigenvalue_of_sub_uniformProj {n d : ℕ} (G : RegularGraph n d)
    (hd : 0 < d) {μ₀ : ℝ} (hmu : μ₀ ∈ spectrum ℝ (adjMatrix G - uniformProj n))
    (hmu0 : μ₀ ≠ 0) : μ₀ ∈ spectrum ℝ (adjMatrix G) := by
  -- Get eigenvector v with (M-P)v = μ₀ • v, v ≠ 0
  rw [← Matrix.spectrum_toLin'] at hmu
  obtain ⟨v, hv⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hmu).exists_hasEigenvector
  have hv_eq : (adjMatrix G - uniformProj n) *ᵥ v = μ₀ • v := by
    have := hv.apply_eq_smul; rwa [Matrix.toLin'_apply] at this
  -- n > 0 since v ≠ 0 lives in Fin n → ℝ
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (funext (Fin.elim0 ·) : v = 0) hv.2
    · exact h
  -- ∑ v = 0 because row sums of M - P are 0 and μ₀ ≠ 0
  have h_sum : ∑ i, v i = 0 := by
    have h_zero : ∑ u, ((adjMatrix G - uniformProj n) *ᵥ v) u = 0 := by
      simp only [Matrix.sub_mulVec, Pi.sub_apply, Finset.sum_sub_distrib]
      have hMsum : ∑ u, (adjMatrix G *ᵥ v) u = ∑ u, v u := by
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_comm]; congr 1; ext j
        simp_rw [show ∀ i, adjMatrix G i j = adjMatrix G j i from
          fun i ↦ ((adjMatrix_isSymm G).apply i j).symm]
        rw [← Finset.sum_mul, adjMatrix_row_sum G hd j, one_mul]
      have hPsum : ∑ u, (uniformProj n *ᵥ v) u = ∑ u, v u := by
        simp only [Matrix.mulVec, dotProduct, uniformProj_apply]
        simp_rw [← Finset.mul_sum]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        field_simp
      linarith
    have h_eq : ∑ u, ((adjMatrix G - uniformProj n) *ᵥ v) u = μ₀ * ∑ u, v u := by
      simp_rw [hv_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact (mul_eq_zero.mp (by linarith : μ₀ * ∑ u, v u = 0)).resolve_left hmu0
  have hPv := uniformProj_mulVec_eq_zero h_sum
  -- Mv = (M-P)v + Pv = μ₀v + 0 = μ₀v
  have hMv : adjMatrix G *ᵥ v = μ₀ • v := by
    have : adjMatrix G *ᵥ v = (adjMatrix G - uniformProj n) *ᵥ v + uniformProj n *ᵥ v := by
      rw [← Matrix.add_mulVec, sub_add_cancel]
    rw [this, hv_eq, hPv, add_zero]
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot, Matrix.eval_charpoly]
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv.2, by
    rw [Matrix.sub_mulVec]
    have hsv : Matrix.scalar (Fin n) μ₀ *ᵥ v = μ₀ • v := by
      rw [show Matrix.scalar (Fin n) μ₀ = μ₀ • (1 : Matrix _ _ ℝ) from
        Algebra.algebraMap_eq_smul_one μ₀, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hsv, hMv, sub_self]⟩

theorem spectralGap_square {n d : ℕ} (G : RegularGraph n d) :
    spectralGap G.square = (spectralGap G) ^ 2 := by
  sorry


/-! **Operator-Norm Spectral Gap** -/

/-- The random walk operator of a d-regular graph, as a continuous linear map
    on `EuclideanSpace`. Maps f to the function averaging f over neighbors:
    `(Wf)(v) = (1/d) ∑ᵢ f(G.neighbor v i)`. -/
noncomputable def RegularGraph.walkCLM {n d : ℕ} (G : RegularGraph n d) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)) (adjMatrix G)

/-- The mean projection: maps f to the constant function with value mean(f).
    `(Pf)(v) = (1/n) ∑ᵢ f(i)`. -/
noncomputable def meanCLM (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)) (uniformProj n)

/-- The spectral gap as the operator norm of the walk restricted to the
    orthogonal complement of the constant functions. -/
noncomputable def spectralGap' {n d : ℕ} (G : RegularGraph n d) : ℝ :=
  ‖G.walkCLM - meanCLM n‖

theorem spectralGap_nonneg' {n d : ℕ} (G : RegularGraph n d) :
    0 ≤ spectralGap' G :=
  norm_nonneg _

private theorem walkCLM_sub_meanCLM_eq {n d : ℕ} (G : RegularGraph n d) :
    G.walkCLM - meanCLM n =
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)) (adjMatrix G - uniformProj n) := by
  show (Matrix.toEuclideanCLM (𝕜 := ℝ)) (adjMatrix G) -
    (Matrix.toEuclideanCLM (𝕜 := ℝ)) (uniformProj n) =
    (Matrix.toEuclideanCLM (𝕜 := ℝ)) (adjMatrix G - uniformProj n)
  rw [map_sub]

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

private theorem adjMatrix_complete_entry {n : ℕ} (u v : Fin (n + 1)) :
    adjMatrix (completeGraph n) u v = if u = v then 0 else 1 / (n : ℝ) := by
  simp only [adjMatrix_apply]
  -- The neighbor function of completeGraph is succAbove
  show ((univ.filter (fun i : Fin n ↦ u.succAbove i = v)).card : ℝ) / n =
    if u = v then 0 else 1 / (n : ℝ)
  split_ifs with h
  · -- u = v: filter is empty since succAbove never hits u
    subst h
    have : univ.filter (fun i : Fin n ↦ u.succAbove i = u) = ∅ :=
      filter_eq_empty_iff.mpr (fun i _ ↦ Fin.succAbove_ne u i)
    rw [this, Finset.card_empty, Nat.cast_zero, zero_div]
  · -- u ≠ v: filter is singleton since succAbove is injective and surjective onto {≠ v}
    obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq (Ne.symm h)
    have : univ.filter (fun i : Fin n ↦ u.succAbove i = v) = {z} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hi ↦ Fin.succAbove_right_injective (hi.trans hz.symm), fun hi ↦ hi ▸ hz⟩
    rw [this, Finset.card_singleton, Nat.cast_one]

private theorem mulVec_adjMatrix_complete {n : ℕ} (_hn : n ≥ 1)
    (x : Fin (n + 1) → ℝ) (u : Fin (n + 1)) :
    (adjMatrix (completeGraph n) *ᵥ x) u = (∑ i, x i) / n - x u / n := by
  simp only [Matrix.mulVec, dotProduct, adjMatrix_complete_entry]
  -- Goal: ∑ v, (if u = v then 0 else 1/n) * x v = (∑ v, x v)/n - x u/n
  -- Rewrite: (if u = v then 0 else 1/n) * x v = 1/n * x v - (if u = v then 1/n * x v else 0)
  have step : ∀ v, (if u = v then (0 : ℝ) else 1 / ↑n) * x v =
      1 / ↑n * x v - if u = v then 1 / ↑n * x v else 0 := by
    intro v; split_ifs <;> ring
  simp_rw [step, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [Finset.sum_ite_eq, Finset.mem_univ]
  ring

private theorem eigenvalues_complete {n : ℕ} (hn : n ≥ 1) (j : Fin (n + 1)) :
    (adjMatrix_isHermitian (completeGraph n)).eigenvalues j = 1 ∨
    (adjMatrix_isHermitian (completeGraph n)).eigenvalues j = -(1 / (n : ℝ)) := by
  set hA := adjMatrix_isHermitian (completeGraph n)
  set ev := hA.eigenvalues j
  set e : Fin (n + 1) → ℝ := ⇑(hA.eigenvectorBasis j)
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Key equation: for all u, ev * e u = (∑ i, e i) / n - e u / n
  have heq : ∀ u, ev * e u = (∑ i, e i) / ↑n - e u / ↑n := by
    intro u
    have := congr_fun (hA.mulVec_eigenvectorBasis j) u
    rw [mulVec_adjMatrix_complete hn _ u] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    linarith
  -- Rearrange: e u * (ev + 1/n) = (∑ i, e i) / n
  have hrearr : ∀ u, e u * (ev + 1 / ↑n) = (∑ i, e i) / ↑n := by
    intro u; have h := heq u; field_simp at h ⊢; nlinarith
  -- Case split on ev + 1/n = 0
  by_cases hev : ev + 1 / (↑n : ℝ) = 0
  · -- Case 1: ev = -1/n
    right; linarith
  · -- Case 2: ev + 1/n ≠ 0 → e is constant → ev = 1
    left
    -- All e u are equal (constant function)
    have hconst : ∀ u v, e u = e v :=
      fun u v ↦ mul_right_cancel₀ hev ((hrearr u).trans (hrearr v).symm)
    -- e is nonzero (from orthonormal basis)
    have hne : ∃ u, e u ≠ 0 := by
      by_contra hall; push_neg at hall
      exact hA.eigenvectorBasis.toBasis.ne_zero j (by ext u; exact hall u)
    obtain ⟨u₀, hu₀⟩ := hne
    -- Since e is constant: ∑ i, e i = (n+1) * e u₀
    have hconst' : ∀ i, e i = e u₀ := fun i ↦ hconst i u₀
    have hsum : ∑ i : Fin (n + 1), e i = (↑n + 1) * e u₀ := by
      simp_rw [hconst', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    -- From the equation: e u₀ * (ev + 1/n) = (n+1) * e u₀ / n
    have hkey := hrearr u₀
    rw [hsum] at hkey
    -- Divide by e u₀ ≠ 0: ev + 1/n = (n+1)/n, so ev = 1
    have hevn : ev + 1 / ↑n = (↑n + 1) / ↑n := by
      field_simp at hkey ⊢; nlinarith
    have : (↑n + 1) / (↑n : ℝ) = 1 + 1 / ↑n := by rw [add_div, div_self hn']
    linarith

private theorem trace_adjMatrix_complete {n : ℕ} :
    (adjMatrix (completeGraph n)).trace = 0 := by
  simp only [Matrix.trace, Matrix.diag, adjMatrix_complete_entry, ite_true, Finset.sum_const_zero]

/-- Each sorted eigenvalue of K_{n+1} is 1 or -1/n. -/
private theorem eigenvalues₀_complete_dichotomy {n : ℕ} (hn : n ≥ 1)
    (k : Fin (Fintype.card (Fin (n + 1)))) :
    (adjMatrix_isHermitian (completeGraph n)).eigenvalues₀ k = 1 ∨
    (adjMatrix_isHermitian (completeGraph n)).eigenvalues₀ k = -(1 / (n : ℝ)) := by
  set hA := adjMatrix_isHermitian (completeGraph n)
  -- eigenvalues₀ k is in the range of eigenvalues (by definition, they're a permutation)
  have hmem : hA.eigenvalues₀ k ∈ Set.range hA.eigenvalues :=
    ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)) k, by
      unfold Matrix.IsHermitian.eigenvalues; simp [Equiv.symm_apply_apply]⟩
  obtain ⟨j, hj⟩ := hmem
  rw [← hj]
  exact eigenvalues_complete hn j

/-- Sum of sorted eigenvalues of K_{n+1} is 0. -/
private theorem sum_eigenvalues₀_complete {n : ℕ} :
    ∑ k, (adjMatrix_isHermitian (completeGraph n)).eigenvalues₀ k = 0 := by
  set hA := adjMatrix_isHermitian (completeGraph n)
  have htr := hA.trace_eq_sum_eigenvalues
  simp only [RCLike.ofReal_real_eq_id, id_eq, trace_adjMatrix_complete] at htr
  have hreindex : ∑ j : Fin (n + 1), hA.eigenvalues j = ∑ k, hA.eigenvalues₀ k := by
    change ∑ j, hA.eigenvalues₀
      ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j) = _
    exact Equiv.sum_comp _ _
  linarith

/-- The second sorted eigenvalue of K_{n+1} is -(1/n). -/
private theorem eigenvalues₀_second_complete {n : ℕ} (hn : n ≥ 1) :
    (adjMatrix_isHermitian (completeGraph n)).eigenvalues₀
      ⟨1, by rw [Fintype.card_fin]; omega⟩ = -(1 / (n : ℝ)) := by
  set hA := adjMatrix_isHermitian (completeGraph n) with hA_def
  set i0 : Fin (Fintype.card (Fin (n + 1))) := ⟨0, by rw [Fintype.card_fin]; omega⟩
  set i1 : Fin (Fintype.card (Fin (n + 1))) := ⟨1, by rw [Fintype.card_fin]; omega⟩
  have hdichotomy : ∀ k, hA.eigenvalues₀ k = 1 ∨ hA.eigenvalues₀ k = -(1 / (↑n : ℝ)) := by
    intro k; rw [hA_def]; exact eigenvalues₀_complete_dichotomy hn k
  have hanti := hA.eigenvalues₀_antitone
  have hsum : ∑ k, hA.eigenvalues₀ k = 0 := by rw [hA_def]; exact sum_eigenvalues₀_complete
  have hn' : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  rcases hdichotomy i1 with h1 | h1
  · exfalso
    have h1n : (0 : ℝ) < 1 / ↑n := by positivity
    -- If ev₀(1) = 1, then ev₀(0) ≥ ev₀(1) = 1, so ev₀(0) = 1 too
    have h0 : hA.eigenvalues₀ i0 = 1 := by
      rcases hdichotomy i0 with h0 | h0
      · exact h0
      · linarith [hanti (show i0 ≤ i1 by simp [Fin.le_iff_val_le_val, i0, i1])]
    -- Each shifted eigenvalue ≥ 0, and two of them = (n+1)/n, exceeding the total
    have hnn : ∀ k, 0 ≤ hA.eigenvalues₀ k + 1 / ↑n := by
      intro k; rcases hdichotomy k with h | h <;> rw [h] <;> linarith
    have hsum_shift : ∑ k, (hA.eigenvalues₀ k + 1 / (↑n : ℝ)) = (↑n + 1) / ↑n := by
      rw [Finset.sum_add_distrib, hsum, zero_add, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]; simp [Fintype.card_fin]; field_simp
    have hexpand : (↑n + 1) / (↑n : ℝ) = 1 + 1 / ↑n := by field_simp
    linarith [Finset.add_le_sum (f := fun k ↦ hA.eigenvalues₀ k + 1 / (↑n : ℝ))
      (fun k _ ↦ hnn k) (Finset.mem_univ i0) (Finset.mem_univ i1)
      (show i0 ≠ i1 by simp [Fin.ext_iff, i0, i1])]
  · exact h1

/-- The last sorted eigenvalue of K_{n+1} is -(1/n). -/
private theorem eigenvalues₀_last_complete {n : ℕ} (hn : n ≥ 1) :
    (adjMatrix_isHermitian (completeGraph n)).eigenvalues₀
      ⟨n, by rw [Fintype.card_fin]; omega⟩ = -(1 / (n : ℝ)) := by
  set hA := adjMatrix_isHermitian (completeGraph n) with hA_def
  set in_ : Fin (Fintype.card (Fin (n + 1))) := ⟨n, by rw [Fintype.card_fin]; omega⟩
  have hdichotomy : ∀ k, hA.eigenvalues₀ k = 1 ∨ hA.eigenvalues₀ k = -(1 / (↑n : ℝ)) := by
    intro k; rw [hA_def]; exact eigenvalues₀_complete_dichotomy hn k
  have hanti := hA.eigenvalues₀_antitone
  have hsum : ∑ k, hA.eigenvalues₀ k = 0 := by rw [hA_def]; exact sum_eigenvalues₀_complete
  have hn' : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  rcases hdichotomy in_ with h | h
  · exfalso
    -- If ev₀(n) = 1, then all ev₀(k) ≥ 1 by antitone (n is max index), so all = 1
    have hall : ∀ k, hA.eigenvalues₀ k = 1 := by
      intro k
      have hle : k ≤ in_ := by
        simp only [Fin.le_iff_val_le_val, in_]
        have := k.isLt; simp [Fintype.card_fin] at this; omega
      rcases hdichotomy k with hk | hk
      · exact hk
      · exfalso; linarith [hanti hle, show (0:ℝ) < 1 / ↑n from by positivity]
    -- But then sum = card > 0, contradicting sum = 0
    simp_rw [hall, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hsum
    simp [Fintype.card_fin] at hsum; linarith
  · exact h

/-- The spectral gap of the complete graph. -/
theorem spectralGap_complete (n : ℕ) (hn : n ≥ 1) :
    spectralGap (completeGraph n) = 1 / (n : ℝ) := by
  have hn' : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  unfold spectralGap
  simp only [dif_neg (show ¬(n + 1 ≤ 1) by omega)]
  -- Use show to inline the let and align ⟨n + 1 - 1, _⟩ with ⟨n, _⟩ (defeq)
  show max ((adjMatrix_isHermitian (completeGraph n)).eigenvalues₀ ⟨1, _⟩)
    (-((adjMatrix_isHermitian (completeGraph n)).eigenvalues₀ ⟨n, _⟩)) = 1 / ↑n
  have h1n : (0 : ℝ) < 1 / ↑n := by positivity
  rw [eigenvalues₀_second_complete hn, eigenvalues₀_last_complete hn, neg_neg]
  exact max_eq_right (by linarith)

/-- For K_{n+1}: M - P = -(1/n) • (I - P) as matrices. -/
private theorem adjMatrix_complete_sub_uniformProj {n : ℕ} (hn : n ≥ 1) :
    adjMatrix (completeGraph n) - uniformProj (n + 1) =
    -(1 / (n : ℝ)) • (1 - uniformProj (n + 1)) := by
  ext u v
  simp only [adjMatrix_complete_entry, uniformProj_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : (↑n : ℝ) + 1 ≠ 0 := by positivity
  split_ifs with h <;> field_simp <;> push_cast <;> ring

/-- The spectral gap of the complete graph (operator-norm version). -/
theorem spectralGap_complete' (n : ℕ) (hn : n ≥ 1) :
    spectralGap' (completeGraph n) = 1 / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold spectralGap'
  -- Transfer to matrix identity via toEuclideanCLM
  rw [walkCLM_sub_meanCLM_eq, adjMatrix_complete_sub_uniformProj hn,
    map_smul, map_sub, map_one]
  -- ‖-(1/n) • T‖ = |-(1/n)| · ‖T‖ = (1/n) · ‖T‖
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_div, abs_one, Nat.abs_cast]
  -- Remains: 1 / n * ‖1 - toEuclideanCLM (uniformProj (n+1))‖ = 1 / n
  -- Need: ‖1 - meanCLM (n+1)‖ = 1
  sorry
