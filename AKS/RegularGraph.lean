/-
  # Regular Graphs and Spectral Theory

  Lean 4 formalization of `d`-regular graphs via rotation maps,
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
import Mathlib.Algebra.Order.Chebyshev

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


/-! **Walk Operator (CLM-first)** -/

/-- The walk function on plain vectors: averages f over the d neighbors of
    each vertex.  `(walkFun G f)(v) = (1/d) ∑ᵢ f(G.neighbor v i)`. -/
noncomputable def RegularGraph.walkFun {n d : ℕ} (G : RegularGraph n d)
    (f : Fin n → ℝ) : Fin n → ℝ :=
  fun v ↦ (∑ i : Fin d, f (G.neighbor v i)) / d

/-- The walk operator as a linear map on `EuclideanSpace`. -/
noncomputable def RegularGraph.walkLM {n d : ℕ} (G : RegularGraph n d) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun f := WithLp.toLp 2 (G.walkFun (WithLp.ofLp f))
  map_add' f g := by
    apply PiLp.ext; intro v
    simp [RegularGraph.walkFun, Finset.sum_add_distrib, add_div]
  map_smul' r f := by
    apply PiLp.ext; intro v
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, RegularGraph.walkFun, ← Finset.mul_sum, mul_div_assoc]

/-- The random walk operator of a d-regular graph, as a continuous linear map
    on `EuclideanSpace`. Maps f to the function averaging f over neighbors:
    `(Wf)(v) = (1/d) ∑ᵢ f(G.neighbor v i)`. -/
noncomputable def RegularGraph.walkCLM {n d : ℕ} (G : RegularGraph n d) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  G.walkLM.toContinuousLinearMap

@[simp]
theorem RegularGraph.walkCLM_apply {n d : ℕ} (G : RegularGraph n d)
    (f : EuclideanSpace ℝ (Fin n)) (v : Fin n) :
    G.walkCLM f v = (∑ i : Fin d, f (G.neighbor v i)) / d :=
  rfl


/-! **Mean Projection (CLM-first)** -/

/-- The mean function on plain vectors: maps f to the constant function
    with value `(1/n) ∑ᵢ f(i)`. -/
noncomputable def meanFun (n : ℕ)
    (f : Fin n → ℝ) : Fin n → ℝ :=
  fun _ ↦ (∑ i, f i) / n

/-- The mean projection as a linear map on `EuclideanSpace`. -/
noncomputable def meanLM (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun f := WithLp.toLp 2 (meanFun n (WithLp.ofLp f))
  map_add' f g := by
    apply PiLp.ext; intro v
    simp [meanFun, Finset.sum_add_distrib, add_div]
  map_smul' r f := by
    apply PiLp.ext; intro v
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, meanFun, ← Finset.mul_sum, mul_div_assoc]

/-- The mean projection: maps f to the constant function with value mean(f).
    `(Pf)(v) = (1/n) ∑ᵢ f(i)`. -/
noncomputable def meanCLM (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (meanLM n).toContinuousLinearMap

@[simp]
theorem meanCLM_apply (n : ℕ) (f : EuclideanSpace ℝ (Fin n)) (v : Fin n) :
    meanCLM n f v = (∑ i, f i) / n :=
  rfl


/-! **Operator Norm Helpers** -/

/-- The rotation map as an equivalence (since it's an involution). -/
private def RegularGraph.rotEquiv {n d : ℕ} (G : RegularGraph n d) :
    Fin n × Fin d ≃ Fin n × Fin d where
  toFun := G.rot
  invFun := G.rot
  left_inv := G.rot_involution
  right_inv := G.rot_involution

/-- Double-counting via the rotation bijection: summing g(neighbor(v,i))
    over all vertex-port pairs equals summing g(v) over all pairs. -/
private theorem RegularGraph.sum_neighbor_eq {n d : ℕ} (G : RegularGraph n d)
    (g : Fin n → ℝ) :
    ∑ v : Fin n, ∑ i : Fin d, g (G.neighbor v i) =
    ∑ v : Fin n, ∑ _i : Fin d, g v := by
  simp_rw [← Fintype.sum_prod_type']
  exact G.rotEquiv.sum_comp (fun p ↦ g p.1)


/-- The walk operator is a contraction: ‖W‖ ≤ 1. -/
theorem RegularGraph.walkCLM_norm_le_one {n d : ℕ} (G : RegularGraph n d) :
    ‖G.walkCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f; rw [one_mul]
  -- Reduce to squared norms via sqrt
  rw [← Real.sqrt_sq (norm_nonneg (G.walkCLM f)), ← Real.sqrt_sq (norm_nonneg f)]
  apply Real.sqrt_le_sqrt
  simp_rw [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, walkCLM_apply]
  -- Goal: ∑ v, ((∑ i, f(nbr v i)) / d)² ≤ ∑ v, (f v)²
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp; exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  · have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
    have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
    -- Jensen: ((∑ x_i) / d)² ≤ (∑ x_i²) / d
    have jensen : ∀ v : Fin n, ((∑ i : Fin d, f (G.neighbor v i)) / ↑d) ^ 2 ≤
        (∑ i : Fin d, f (G.neighbor v i) ^ 2) / ↑d := by
      intro v
      have cs := @sq_sum_le_card_mul_sum_sq (Fin d) ℝ _ _ _ _
        Finset.univ (fun i ↦ f (G.neighbor v i))
      simp only [Finset.card_univ, Fintype.card_fin] at cs
      rw [div_pow, sq (d : ℝ), ← div_div]
      apply div_le_div_of_nonneg_right _ hd_pos.le
      rw [div_le_iff₀ hd_pos, mul_comm]
      exact cs
    -- Sum Jensen, then double-count, then simplify
    calc ∑ v, ((∑ i : Fin d, f (G.neighbor v i)) / ↑d) ^ 2
        ≤ ∑ v, (∑ i : Fin d, f (G.neighbor v i) ^ 2) / ↑d :=
          Finset.sum_le_sum (fun v _ ↦ jensen v)
      _ = (∑ v, ∑ i, f (G.neighbor v i) ^ 2) / ↑d := by
          rw [Finset.sum_div]
      _ = (∑ v, ∑ _i : Fin d, f v ^ 2) / ↑d := by
          rw [G.sum_neighbor_eq (fun v ↦ f v ^ 2)]
      _ = (∑ v, ↑d * (f v ^ 2)) / ↑d := by
          congr 1; apply Finset.sum_congr rfl; intro v _
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ∑ v, f v ^ 2 := by
          rw [← Finset.mul_sum, mul_div_cancel_left₀ _ hd_ne]

/-! **Spectral Gap** -/

/-- The spectral gap λ(G): the operator norm of the walk operator
    restricted to the subspace orthogonal to the constant functions.

      λ(G) = ‖W - P‖

    where W is the random walk operator and P is the mean projection.
    We have 0 ≤ λ(G) ≤ 1, with λ(G) close to 0 meaning
    excellent expansion. -/
noncomputable def spectralGap {n d : ℕ} (G : RegularGraph n d) : ℝ :=
  ‖G.walkCLM - meanCLM n‖

/-- The spectral gap is nonneg. -/
theorem spectralGap_nonneg {n d : ℕ} (G : RegularGraph n d) :
    0 ≤ spectralGap G :=
  norm_nonneg _

/-- The mean projection doesn't increase the norm: ‖Pf‖ ≤ ‖f‖. -/
private theorem meanCLM_apply_norm_le (n : ℕ) (f : EuclideanSpace ℝ (Fin n)) :
    ‖meanCLM n f‖ ≤ ‖f‖ := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg f)]
  apply Real.sqrt_le_sqrt
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs, meanCLM_apply]
  -- Goal: ∑ v, ((∑ i, f i) / n)² ≤ ∑ v, (f v)²
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have cs := @sq_sum_le_card_mul_sum_sq (Fin n) ℝ _ _ _ _
      Finset.univ (fun i ↦ f i)
    simp only [Finset.card_univ, Fintype.card_fin] at cs
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow]
    -- Goal: n * (∑ f)² / n² ≤ ∑ f²
    have h_simp : ↑n * ((∑ i : Fin n, f i) ^ 2 / (↑n) ^ 2) =
        (∑ i : Fin n, f i) ^ 2 / ↑n := by
      field_simp
    rw [h_simp, div_le_iff₀ hn_pos]
    linarith [mul_comm (↑n : ℝ) (∑ x : Fin n, f x ^ 2)]

/-- Subtracting the mean doesn't increase the norm: ‖f - Pf‖ ≤ ‖f‖. -/
private theorem norm_sub_meanCLM_le (n : ℕ) (f : EuclideanSpace ℝ (Fin n)) :
    ‖f - meanCLM n f‖ ≤ ‖f‖ := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg f)]
  apply Real.sqrt_le_sqrt
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs]
  have hfv : ∀ v : Fin n, (f - meanCLM n f) v = f v - (∑ i, f i) / ↑n := by
    intro v; simp [meanCLM_apply]
  simp_rw [hfv]
  -- Goal: ∑ v, (f v - (∑ i, f i) / n)² ≤ ∑ v, (f v)²
  -- ∑(f v - μ)² = ∑ f v² - (∑ f)²/n ≤ ∑ f v²  (by CS: (∑ f)²/n ≥ 0)
  set S := ∑ i : Fin n, f i
  have expand : ∀ v : Fin n, (f v - S / ↑n) ^ 2 =
      f v ^ 2 - 2 * (S / ↑n) * f v + (S / ↑n) ^ 2 := fun v ↦ by ring
  simp_rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- Need: ∑ f v² - 2(S/n)·S + n·(S/n)² ≤ ∑ f v²
  -- i.e., n·(S/n)² ≤ 2(S/n)·S
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hn_ne := ne_of_gt hn_pos
    -- 2(S/n)·S - n·(S/n)² = S²/n ≥ 0
    have key : 2 * (S / ↑n) * S - ↑n * (S / ↑n) ^ 2 = S ^ 2 / ↑n := by
      field_simp; ring
    linarith [div_nonneg (sq_nonneg S) hn_pos.le]

/-- The walk operator preserves the mean projection: W(Pf) = Pf (when d > 0). -/
private theorem walkCLM_comp_meanCLM {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d) :
    ∀ f : EuclideanSpace ℝ (Fin n), G.walkCLM (meanCLM n f) = meanCLM n f := by
  intro f; ext v
  simp only [RegularGraph.walkCLM_apply, meanCLM_apply]
  -- Goal: (∑ i : Fin d, (∑ j, f j) / n) / d = (∑ j, f j) / n
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by positivity)

theorem spectralGap_le_one {n d : ℕ} (G : RegularGraph n d) :
    spectralGap G ≤ 1 := by
  unfold spectralGap
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f; rw [one_mul]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- d = 0: walkCLM sends everything to 0
    have hW : G.walkCLM f = 0 := by
      ext v; simp [RegularGraph.walkCLM_apply]
    simp only [ContinuousLinearMap.sub_apply, hW, zero_sub, norm_neg]
    exact meanCLM_apply_norm_le n f
  · -- d > 0: factor as W(f - Pf) using WP = P
    have hWP := walkCLM_comp_meanCLM G hd f
    calc ‖(G.walkCLM - meanCLM n) f‖
        = ‖G.walkCLM f - meanCLM n f‖ := by
          simp [ContinuousLinearMap.sub_apply]
      _ = ‖G.walkCLM f - G.walkCLM (meanCLM n f)‖ := by rw [hWP]
      _ = ‖G.walkCLM (f - meanCLM n f)‖ := by rw [map_sub]
      _ ≤ ‖G.walkCLM‖ * ‖f - meanCLM n f‖ := G.walkCLM.le_opNorm _
      _ ≤ 1 * ‖f - meanCLM n f‖ := by
          apply mul_le_mul_of_nonneg_right G.walkCLM_norm_le_one (norm_nonneg _)
      _ = ‖f - meanCLM n f‖ := one_mul _
      _ ≤ ‖f‖ := norm_sub_meanCLM_le n f



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


/-! **CLM Algebraic Identities for Spectral Gap Squaring** -/

/-- Rotation bijection swaps function arguments in a product sum:
    ∑_{v,i} f(neighbor(v,i))·g(v) = ∑_{v,i} f(v)·g(neighbor(v,i)). -/
private theorem RegularGraph.sum_neighbor_swap {n d : ℕ} (G : RegularGraph n d)
    (f g : Fin n → ℝ) :
    ∑ v : Fin n, ∑ i : Fin d, f (G.neighbor v i) * g v =
    ∑ v : Fin n, ∑ i : Fin d, f v * g (G.neighbor v i) := by
  simp_rw [← Fintype.sum_prod_type', RegularGraph.neighbor]
  -- Reindex by rot (a bijection): ∑ p, h(rot p) = ∑ p, h(p)
  have h := G.rotEquiv.sum_comp (fun q ↦ f q.1 * g (G.rot q).1)
  simp only [show ∀ p, (G.rotEquiv p : Fin n × Fin d) = G.rot p from fun _ ↦ rfl,
    G.rot_involution] at h
  exact h

/-- The walk operator is self-adjoint: ⟪Wf, g⟫ = ⟪f, Wg⟫. -/
private theorem walkCLM_isSelfAdjoint {n d : ℕ} (G : RegularGraph n d) :
    IsSelfAdjoint G.walkCLM := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  change @inner ℝ _ _ (G.walkCLM f) g = @inner ℝ _ _ f (G.walkCLM g)
  -- inner on EuclideanSpace: ⟪x, y⟫ = ∑ v, y v * x v (via RCLike.inner_apply)
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    RegularGraph.walkCLM_apply]
  -- Goal: ∑ v, g v * ((∑ i, f(nbr v i))/d) = ∑ v, ((∑ i, g(nbr v i))/d) * f v
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · simp_rw [mul_div_assoc', div_mul_eq_mul_div, ← Finset.sum_div]
    congr 1
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    exact (G.sum_neighbor_swap (fun v ↦ g v) (fun v ↦ f v)).symm

/-- The mean projection is self-adjoint: ⟪Pf, g⟫ = ⟪f, Pg⟫. -/
private theorem meanCLM_isSelfAdjoint (n : ℕ) :
    IsSelfAdjoint (meanCLM n) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  change @inner ℝ _ _ (meanCLM n f) g = @inner ℝ _ _ f (meanCLM n g)
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, meanCLM_apply]
  -- ∑ v, g v * ((∑ i, f i)/n) = ∑ v, ((∑ i, g i)/n) * f v
  simp_rw [mul_div_assoc', div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]

/-- The mean projection is idempotent: P(Pf) = Pf. -/
private theorem meanCLM_idempotent (n : ℕ) :
    meanCLM n * meanCLM n = (meanCLM n : EuclideanSpace ℝ (Fin n) →L[ℝ] _) := by
  ext f v
  simp only [ContinuousLinearMap.mul_apply, meanCLM_apply, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · exact mul_div_cancel_left₀ _ (by positivity)

/-- The mean projection absorbs the walk operator: P ∘ W = P (for d > 0). -/
private theorem meanCLM_comp_walkCLM {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d) :
    meanCLM n * G.walkCLM = (meanCLM n : EuclideanSpace ℝ (Fin n) →L[ℝ] _) := by
  ext f v
  simp only [ContinuousLinearMap.mul_apply, meanCLM_apply, RegularGraph.walkCLM_apply]
  -- Goal: (∑ u, (∑ i, f(nbr u i)) / d) / n = (∑ u, f u) / n
  congr 1
  -- Pull /d out of the sum
  rw [← Finset.sum_div]
  -- Now: (∑ u, ∑ i, f(nbr u i)) / d = ∑ u, f u
  rw [G.sum_neighbor_eq (fun v ↦ f v)]
  -- (∑ u, ∑ _i, f u) / d = ∑ u, f u
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, mul_div_cancel_left₀ _ (by positivity : (d : ℝ) ≠ 0)]

/-- Equivalence between Fin d × Fin d and Fin (d * d) via the
    encode/decode pair (i * d + j) ↔ (i, j). -/
private def finPairEquiv {d : ℕ} (hd : 0 < d) : Fin d × Fin d ≃ Fin (d * d) where
  toFun ij := ⟨ij.1.val * d + ij.2.val, Fin.pair_lt ij.1 ij.2⟩
  invFun p := (⟨p.val / d, (Nat.div_lt_iff_lt_mul hd).mpr p.isLt⟩,
               ⟨p.val % d, Nat.mod_lt _ hd⟩)
  left_inv ij := Prod.ext
    (fin_encode_fst ij.1 ij.2 ((Nat.div_lt_iff_lt_mul hd).mpr (Fin.pair_lt ij.1 ij.2)))
    (fin_encode_snd ij.1 ij.2 (Nat.mod_lt _ hd))
  right_inv p := fin_div_add_mod p (Fin.pair_lt
    ⟨p.val / d, (Nat.div_lt_iff_lt_mul hd).mpr p.isLt⟩
    ⟨p.val % d, Nat.mod_lt _ hd⟩)

/-- The walk operator of G² equals the square of G's walk operator:
    W_{G²} = W_G ∘ W_G. -/
private theorem walkCLM_sq {n d : ℕ} (G : RegularGraph n d) :
    G.square.walkCLM = G.walkCLM * G.walkCLM := by
  ext f v
  simp only [ContinuousLinearMap.mul_apply, RegularGraph.walkCLM_apply]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · -- Transform RHS: (∑ i, (∑ j, ...)/d) / d → (∑ i, ∑ j, ...) / (d*d)
    rw [← Finset.sum_div, div_div,
      show (↑(d * d) : ℝ) = ↑d * ↑d from by push_cast; ring]
    -- Both sides: (sum) / (d * d). Show numerators equal.
    congr 1
    -- LHS: ∑ p : Fin(d*d), f(sq.nbr v p) = ∑ (i,j) : Fin d × Fin d, f(nbr(nbr v i) j)
    rw [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (finPairEquiv hd).symm _ _ (fun _ ↦ rfl)

theorem spectralGap_square {n d : ℕ} (G : RegularGraph n d) :
    spectralGap G.square = (spectralGap G) ^ 2 := by
  unfold spectralGap
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- d = 0: both walkCLMs are 0, spectralGap = ‖meanCLM‖
    have hW : G.walkCLM = 0 := by
      ext f v; simp [RegularGraph.walkCLM_apply]
    have hW2 : G.square.walkCLM = 0 := by
      ext f v; simp [RegularGraph.walkCLM_apply]
    simp only [hW, hW2, zero_sub, norm_neg]
    -- ‖P‖ = ‖P‖² since P is self-adjoint idempotent
    have hidp := meanCLM_idempotent n
    have hsa := meanCLM_isSelfAdjoint n
    rw [← hsa.norm_mul_self, hidp]
  · -- d > 0: algebraic identity (W - P)² = W² - P
    -- Use abbreviations W and P (let, not set, to keep transparent)
    let W := G.walkCLM
    let P : EuclideanSpace ℝ (Fin n) →L[ℝ] _ := meanCLM n
    have hWP : W * P = P := by
      refine ContinuousLinearMap.ext (fun f ↦ ?_)
      exact walkCLM_comp_meanCLM G hd f
    have hPW : P * W = P := meanCLM_comp_walkCLM G hd
    have hPP : P * P = P := meanCLM_idempotent n
    have hsq : (W - P) * (W - P) = W * W - P := by
      have : (W - P) * (W - P) = W * W - W * P - P * W + P * P := by
        simp only [mul_sub, sub_mul]; abel
      rw [this, hWP, hPW, hPP]; abel
    rw [walkCLM_sq G, ← hsq]
    have hsa : IsSelfAdjoint (W - P) := by
      rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric, ContinuousLinearMap.coe_sub]
      exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        (walkCLM_isSelfAdjoint G)).sub
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (meanCLM_isSelfAdjoint n)))
    rw [← hsa.norm_mul_self]


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

/-- The neighbor function of the complete graph is `succAbove`. -/
private theorem completeGraph_neighbor {n : ℕ} (v : Fin (n + 1)) (i : Fin n) :
    (completeGraph n).neighbor v i = v.succAbove i := rfl

/-- For the complete graph, the walk operator gives the average over all
    *other* vertices: `(Wf)(v) = ((∑ f) - f v) / n`. -/
private theorem walkCLM_completeGraph_apply {n : ℕ}
    (f : EuclideanSpace ℝ (Fin (n + 1))) (v : Fin (n + 1)) :
    (completeGraph n).walkCLM f v = ((∑ j, f j) - f v) / ↑n := by
  simp only [RegularGraph.walkCLM_apply, completeGraph_neighbor]
  congr 1
  have := Fin.sum_univ_succAbove (fun j ↦ f j) v
  linarith

/-- The CLM operator identity for the complete graph:
    `W - P = -(1/n) • (1 - P)` where W = walkCLM, P = meanCLM. -/
private theorem walkCLM_sub_meanCLM_completeGraph {n : ℕ} (hn : n ≥ 1) :
    (completeGraph n).walkCLM - meanCLM (n + 1) =
    (-(1 / (n : ℝ))) • (ContinuousLinearMap.id ℝ _ - meanCLM (n + 1)) := by
  refine ContinuousLinearMap.ext (fun f ↦ ?_)
  apply PiLp.ext; intro v
  show (completeGraph n).walkCLM f v - meanCLM (n + 1) f v =
    -(1 / (↑n : ℝ)) * (f v - meanCLM (n + 1) f v)
  rw [walkCLM_completeGraph_apply, meanCLM_apply]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : (↑n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- The norm of the orthogonal complement projection `1 - meanCLM` is 1
    (for n ≥ 2 vertices, i.e., non-constant functions exist). -/
private theorem norm_id_sub_meanCLM {n : ℕ} (hn : n ≥ 2) :
    ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) - meanCLM n‖ = 1 := by
  set T := ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) - meanCLM n
  apply le_antisymm
  · -- Upper bound: ‖Tf‖ ≤ ‖f‖ (1 - P is a contraction)
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f; rw [one_mul]
    show ‖f - meanCLM n f‖ ≤ ‖f‖
    exact norm_sub_meanCLM_le n f
  · -- Lower bound: exhibit f with Pf = 0, f ≠ 0, so ‖Tf‖ = ‖f‖
    -- Build test vector: 1 at index 0, -1 at index 1, 0 elsewhere
    set v0 : Fin n := ⟨0, by omega⟩
    set v1 : Fin n := ⟨1, by omega⟩
    let g : Fin n → ℝ := fun i ↦ if i = v0 then 1 else if i = v1 then -1 else 0
    let f : EuclideanSpace ℝ (Fin n) := (WithLp.equiv 2 _).symm g
    have hfv : ∀ i, f i = g i := fun _ ↦ rfl
    have hgsum : ∑ i, g i = 0 := by
      have hne : v0 ≠ v1 := by simp [Fin.ext_iff, v0, v1]
      have hsplit : ∀ i : Fin n, g i = (if i = v0 then (1:ℝ) else 0) +
                                        (if i = v1 then (-1:ℝ) else 0) := by
        intro i; simp only [g]; split_ifs with h1 h2
        · exact absurd (h1.symm.trans h2) hne
        · ring
        · ring
        · ring
      simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true, add_neg_cancel]
    have hfsum : ∑ i, f i = 0 := by simp_rw [hfv]; exact hgsum
    have hf_ne : f ≠ 0 := by
      intro h
      have : g v0 = 0 := by
        calc g v0 = f v0 := (hfv v0).symm
          _ = (0 : EuclideanSpace ℝ (Fin n)) v0 := by rw [h]
          _ = 0 := rfl
      simp [g] at this
    -- T f = f since Pf = 0
    have hTf : T f = f := by
      apply PiLp.ext; intro v
      show f v - meanCLM n f v = f v
      rw [meanCLM_apply, hfsum, zero_div, sub_zero]
    -- From ‖Tf‖ = ‖f‖ and T.le_opNorm: ‖f‖ ≤ ‖T‖ * ‖f‖
    have h_le := T.le_opNorm f
    rw [hTf] at h_le
    exact le_of_mul_le_mul_right (by rw [one_mul]; exact h_le) (norm_pos_iff.mpr hf_ne)

/-- The spectral gap of the complete graph: λ(K_{n+1}) = 1/n. -/
theorem spectralGap_complete (n : ℕ) (hn : n ≥ 1) :
    spectralGap (completeGraph n) = 1 / (n : ℝ) := by
  unfold spectralGap
  rw [walkCLM_sub_meanCLM_completeGraph hn, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_div, abs_one, Nat.abs_cast,
    norm_id_sub_meanCLM (show n + 1 ≥ 2 by omega), mul_one]
