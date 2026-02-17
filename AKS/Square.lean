/-
  # Graph Squaring and Spectral Gap Squaring

  The square G² of a `d`-regular graph takes two steps along G's edges,
  yielding a d²-regular graph. The key result is `spectralGap_square`:
  λ(G²) = λ(G)², proved via the C*-algebra identity
  `(W - P)² = W² - P` (from `WP = PW = P`).
-/

import AKS.RegularGraph

open Matrix BigOperators Finset


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

/-- The mean projection absorbs the walk operator: P ∘ W = P (for d > 0). -/
theorem meanCLM_comp_walkCLM {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d) :
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
