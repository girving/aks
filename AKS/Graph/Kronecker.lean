module
/-
  # Kronecker Product of Regular Graphs

  The Kronecker (tensor) product G₁ ⊗ G₂ has vertex set V₁ × V₂ and edges
  (u₁,u₂) ~ (v₁,v₂) iff u₁ ~ v₁ in G₁ AND u₂ ~ v₂ in G₂. The result is
  a (d₁ * d₂)-regular graph on (n₁ * n₂) vertices.

  Key result: `spectralGap (G₁.kronecker G₂) ≤ max (spectralGap G₁) (spectralGap G₂)`
-/

public import AKS.Graph.Square

@[expose] public section


open Matrix BigOperators Finset


/-! **Product Fin Equivalence** -/

/-- Equivalence between `Fin n₁ × Fin n₂` and `Fin (n₁ * n₂)` via `(a, b) ↦ a * n₂ + b`.
    Generalizes `finPairEquiv` to different factor sizes. -/
def finProdEquiv {n₁ n₂ : ℕ} (hn₂ : 0 < n₂) : Fin n₁ × Fin n₂ ≃ Fin (n₁ * n₂) where
  toFun p := ⟨p.1.val * n₂ + p.2.val, Fin.pair_lt p.1 p.2⟩
  invFun k := (⟨k.val / n₂, (Nat.div_lt_iff_lt_mul hn₂).mpr k.isLt⟩,
               ⟨k.val % n₂, Nat.mod_lt _ hn₂⟩)
  left_inv p := Prod.ext
    (fin_encode_fst p.1 p.2 ((Nat.div_lt_iff_lt_mul hn₂).mpr (Fin.pair_lt p.1 p.2)))
    (fin_encode_snd p.1 p.2 (Nat.mod_lt _ hn₂))
  right_inv k := fin_div_add_mod k (Fin.pair_lt
    ⟨k.val / n₂, (Nat.div_lt_iff_lt_mul hn₂).mpr k.isLt⟩
    ⟨k.val % n₂, Nat.mod_lt _ hn₂⟩)


/-! **Kronecker Product Definition** -/

/-- The rotation map for the Kronecker product G₁ ⊗ G₂:
    decode vertex as (v₁, v₂) and port as (i, j),
    apply G₁.rot to (v₁, i) and G₂.rot to (v₂, j) independently,
    re-encode the results. -/
def kronecker_rot {n₁ n₂ d₁ d₂ : ℕ} (G₁ : RegularGraph n₁ d₁) (G₂ : RegularGraph n₂ d₂)
    (p : Fin (n₁ * n₂) × Fin (d₁ * d₂)) : Fin (n₁ * n₂) × Fin (d₁ * d₂) :=
  have hn₂ : 0 < n₂ := Nat.pos_of_ne_zero (by
    rintro rfl; exact absurd p.1.isLt (by simp))
  have hd₂ : 0 < d₂ := Nat.pos_of_ne_zero (by
    rintro rfl; exact absurd p.2.isLt (by simp))
  let v₁ : Fin n₁ := ⟨p.1.val / n₂, (Nat.div_lt_iff_lt_mul hn₂).mpr p.1.isLt⟩
  let v₂ : Fin n₂ := ⟨p.1.val % n₂, Nat.mod_lt _ hn₂⟩
  let i : Fin d₁ := ⟨p.2.val / d₂, (Nat.div_lt_iff_lt_mul hd₂).mpr p.2.isLt⟩
  let j : Fin d₂ := ⟨p.2.val % d₂, Nat.mod_lt _ hd₂⟩
  let r₁ := G₁.rot (v₁, i)
  let r₂ := G₂.rot (v₂, j)
  (⟨r₁.1.val * n₂ + r₂.1.val, Fin.pair_lt r₁.1 r₂.1⟩,
   ⟨r₁.2.val * d₂ + r₂.2.val, Fin.pair_lt r₁.2 r₂.2⟩)

theorem kronecker_rot_involution {n₁ n₂ d₁ d₂ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (G₂ : RegularGraph n₂ d₂)
    (p : Fin (n₁ * n₂) × Fin (d₁ * d₂)) :
    kronecker_rot G₁ G₂ (kronecker_rot G₁ G₂ p) = p := by
  obtain ⟨v, ij⟩ := p
  simp only [kronecker_rot, fin_encode_fst, fin_encode_snd, Prod.mk.eta,
    G₁.rot_involution, G₂.rot_involution, fin_div_add_mod]

/-- The Kronecker (tensor) product of two regular graphs. -/
def RegularGraph.kronecker {n₁ n₂ d₁ d₂ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (G₂ : RegularGraph n₂ d₂) :
    RegularGraph (n₁ * n₂) (d₁ * d₂) where
  rot := kronecker_rot G₁ G₂
  rot_involution := kronecker_rot_involution G₁ G₂


/-! **Neighbor Unfold** -/

theorem kronecker_neighbor_unfold {n₁ n₂ d₁ d₂ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (G₂ : RegularGraph n₂ d₂)
    (u : Fin (n₁ * n₂)) (port : Fin (d₁ * d₂))
    (hn₂ : 0 < n₂) (hd₂ : 0 < d₂) :
    (G₁.kronecker G₂).neighbor u port =
      ⟨(G₁.neighbor ⟨u.val / n₂, (Nat.div_lt_iff_lt_mul hn₂).mpr u.isLt⟩
                     ⟨port.val / d₂, (Nat.div_lt_iff_lt_mul hd₂).mpr port.isLt⟩).val * n₂ +
       (G₂.neighbor ⟨u.val % n₂, Nat.mod_lt _ hn₂⟩
                     ⟨port.val % d₂, Nat.mod_lt _ hd₂⟩).val,
       Fin.pair_lt
         (G₁.neighbor ⟨u.val / n₂, (Nat.div_lt_iff_lt_mul hn₂).mpr u.isLt⟩
                      ⟨port.val / d₂, (Nat.div_lt_iff_lt_mul hd₂).mpr port.isLt⟩)
         (G₂.neighbor ⟨u.val % n₂, Nat.mod_lt _ hn₂⟩
                      ⟨port.val % d₂, Nat.mod_lt _ hd₂⟩)⟩ := by
  simp only [RegularGraph.kronecker, RegularGraph.neighbor, kronecker_rot]


/-! **Paired Neighbor Lemma** -/

/-- The Kronecker neighbor at an encoded vertex-port pair decomposes as
    `nbr_K(v₁*n₂+v₂, i*d₂+j) = nbr₁(v₁,i)*n₂ + nbr₂(v₂,j)`. -/
theorem kronecker_neighbor_pair {n₁ n₂ d₁ d₂ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (G₂ : RegularGraph n₂ d₂)
    (v₁ : Fin n₁) (v₂ : Fin n₂) (i : Fin d₁) (j : Fin d₂) :
    (G₁.kronecker G₂).neighbor
      ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩
      ⟨i.val * d₂ + j.val, Fin.pair_lt i j⟩ =
    ⟨(G₁.neighbor v₁ i).val * n₂ + (G₂.neighbor v₂ j).val,
      Fin.pair_lt (G₁.neighbor v₁ i) (G₂.neighbor v₂ j)⟩ := by
  simp only [RegularGraph.kronecker, RegularGraph.neighbor, kronecker_rot,
    fin_encode_fst, fin_encode_snd]


/-! **Walk Operator Decomposition** -/

/-- The Kronecker walk operator factors as a product of walks:
    `W_K f(v₁,v₂) = (1/(d₁d₂)) ∑_i ∑_j f(nbr₁(v₁,i), nbr₂(v₂,j))`. -/
theorem kronecker_walkCLM_apply {n₁ n₂ d₁ d₂ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (G₂ : RegularGraph n₂ d₂)
    (hd₂ : 0 < d₂)
    (f : EuclideanSpace ℝ (Fin (n₁ * n₂))) (v₁ : Fin n₁) (v₂ : Fin n₂) :
    (G₁.kronecker G₂).walkCLM f ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩ =
    (∑ i : Fin d₁, ∑ j : Fin d₂,
      f ⟨(G₁.neighbor v₁ i).val * n₂ + (G₂.neighbor v₂ j).val,
        Fin.pair_lt (G₁.neighbor v₁ i) (G₂.neighbor v₂ j)⟩) / (d₁ * d₂) := by
  show (∑ p : Fin (d₁ * d₂),
    f ((G₁.kronecker G₂).neighbor ⟨v₁.val * n₂ + v₂.val, _⟩ p)) / ↑(d₁ * d₂) = _
  rw [show (↑(d₁ * d₂) : ℝ) = ↑d₁ * ↑d₂ from by push_cast; ring]
  congr 1
  -- Reindex via finProdEquiv, using kronecker_neighbor_pair for each summand
  rw [← (Fintype.sum_prod_type' (fun (i : Fin d₁) (j : Fin d₂) ↦
    f ⟨(G₁.neighbor v₁ i).val * n₂ + (G₂.neighbor v₂ j).val,
      Fin.pair_lt (G₁.neighbor v₁ i) (G₂.neighbor v₂ j)⟩))]
  refine Fintype.sum_equiv (finProdEquiv hd₂).symm _ _ (fun p ↦ ?_)
  -- p : Fin (d₁ * d₂); show f(nbr_K(v, p)) = f(nbr₁(v₁,(p/d₂))*n₂+nbr₂(v₂,(p%d₂)))
  let ij := (finProdEquiv hd₂).symm p
  have hp : p = ⟨ij.1.val * d₂ + ij.2.val, Fin.pair_lt ij.1 ij.2⟩ :=
    ((finProdEquiv hd₂).right_inv p).symm
  conv_lhs => rw [hp]
  exact congr_arg f (kronecker_neighbor_pair G₁ G₂ v₁ v₂ ij.1 ij.2)


/-! **Double-Counting for Kronecker Graphs** -/

/-- Reindex a vertex sum over `Fin (n₁ * n₂)` as a double sum. -/
theorem kronecker_sum_vertex_eq {n₁ n₂ : ℕ} (hn₂ : 0 < n₂) (g : Fin (n₁ * n₂) → ℝ) :
    ∑ v : Fin (n₁ * n₂), g v =
    ∑ v₁ : Fin n₁, ∑ v₂ : Fin n₂,
      g ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩ := by
  rw [← (Fintype.sum_prod_type' (fun (v₁ : Fin n₁) (v₂ : Fin n₂) ↦
    g ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩))]
  exact ((finProdEquiv hn₂).sum_comp g).symm

/-- Double-counting for the Kronecker graph: summing over neighbors in the
    first factor equals summing over all vertices with multiplicity `d₁`. -/
theorem kronecker_sum_neighbor₁_eq {n₁ d₁ : ℕ}
    (G₁ : RegularGraph n₁ d₁)
    (g : Fin n₁ → ℝ) :
    ∑ v₁ : Fin n₁, ∑ i : Fin d₁, g (G₁.neighbor v₁ i) =
    ∑ v₁ : Fin n₁, ∑ _i : Fin d₁, g v₁ :=
  G₁.sum_neighbor_eq g


/-! **Spectral Gap Bound** -/

/-- The spectral gap of the Kronecker product is at most the max of the factors' gaps:
    `spectralGap (G₁.kronecker G₂) ≤ max (spectralGap G₁) (spectralGap G₂)` -/
-- The spectral gap bound applied to a single function: ‖(W-P)f‖ ≤ λ(G) · ‖f‖
private theorem spectralGap_apply_le {n d : ℕ} (G : RegularGraph n d)
    (f : EuclideanSpace ℝ (Fin n)) :
    ‖(G.walkCLM - meanCLM n) f‖ ≤ spectralGap G * ‖f‖ :=
  (G.walkCLM - meanCLM n).le_opNorm f

/-! **Slice operations for the spectral gap proof** -/

-- The v₁-slice of f: g_{v₁}(v₂) = f(v₁*n₂ + v₂)
private noncomputable def slice {n₁ n₂ : ℕ}
    (f : EuclideanSpace ℝ (Fin (n₁ * n₂))) (v₁ : Fin n₁) :
    EuclideanSpace ℝ (Fin n₂) :=
  WithLp.toLp 2 (fun v₂ ↦ f ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩)

-- The slice mean: h(v₁) = (1/n₂) ∑_{v₂} f(v₁, v₂)
private noncomputable def sliceMean {n₁ n₂ : ℕ}
    (f : EuclideanSpace ℝ (Fin (n₁ * n₂))) : EuclideanSpace ℝ (Fin n₁) :=
  WithLp.toLp 2 (fun v₁ ↦ (∑ v₂ : Fin n₂,
    f ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩) / n₂)

@[simp] private theorem slice_apply {n₁ n₂ : ℕ}
    (f : EuclideanSpace ℝ (Fin (n₁ * n₂))) (v₁ : Fin n₁) (v₂ : Fin n₂) :
    slice f v₁ v₂ = f ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩ := rfl

@[simp] private theorem sliceMean_apply {n₁ n₂ : ℕ}
    (f : EuclideanSpace ℝ (Fin (n₁ * n₂))) (v₁ : Fin n₁) :
    sliceMean f v₁ = (∑ v₂ : Fin n₂,
      f ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩) / n₂ := rfl

-- sliceMean f = meanCLM applied to each slice
private theorem sliceMean_eq {n₁ n₂ : ℕ}
    (f : EuclideanSpace ℝ (Fin (n₁ * n₂))) (v₁ : Fin n₁) (v₂ : Fin n₂) :
    meanCLM n₂ (slice f v₁) v₂ = sliceMean f v₁ := by
  simp [meanCLM_apply, slice_apply, sliceMean_apply]

-- ‖slice f v₁‖² as sum
private theorem slice_norm_sq {n₁ n₂ : ℕ}
    (f : EuclideanSpace ℝ (Fin (n₁ * n₂))) (v₁ : Fin n₁) :
    ‖slice f v₁‖ ^ 2 = ∑ v₂ : Fin n₂,
      f ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  congr 1; ext v₂
  simp [Real.norm_eq_abs, sq_abs, slice_apply]

-- ‖f‖² = ∑_{v₁} ‖slice f v₁‖² (Pythagorean over slices)
private theorem norm_sq_eq_sum_slice {n₁ n₂ : ℕ} (hn₂ : 0 < n₂)
    (f : EuclideanSpace ℝ (Fin (n₁ * n₂))) :
    ‖f‖ ^ 2 = ∑ v₁ : Fin n₁, ‖slice f v₁‖ ^ 2 := by
  simp_rw [slice_norm_sq]
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs]
  exact kronecker_sum_vertex_eq hn₂ _

-- Bound ‖(W₂-P₂)(slice f u₁)‖² ≤ λ₂² · ‖slice f u₁‖²
private theorem slice_deviation_bound {n₁ n₂ d₂ : ℕ}
    (G₂ : RegularGraph n₂ d₂)
    (f : EuclideanSpace ℝ (Fin (n₁ * n₂))) (u₁ : Fin n₁) :
    ‖(G₂.walkCLM - meanCLM n₂) (slice f u₁)‖ ^ 2 ≤
    spectralGap G₂ ^ 2 * ‖slice f u₁‖ ^ 2 := by
  have h := spectralGap_apply_le G₂ (slice f u₁)
  have ha : 0 ≤ ‖(G₂.walkCLM - meanCLM n₂) (slice f u₁)‖ := norm_nonneg _
  calc ‖(G₂.walkCLM - meanCLM n₂) (slice f u₁)‖ ^ 2
      ≤ (spectralGap G₂ * ‖slice f u₁‖) ^ 2 := sq_le_sq' (by linarith) h
    _ = spectralGap G₂ ^ 2 * ‖slice f u₁‖ ^ 2 := by ring

-- Bound ‖(W₁-P₁)(sliceMean f)‖² ≤ λ₁² · ‖sliceMean f‖²
private theorem mean_deviation_bound {n₁ n₂ d₁ : ℕ}
    (G₁ : RegularGraph n₁ d₁)
    (f : EuclideanSpace ℝ (Fin (n₁ * n₂))) :
    ‖(G₁.walkCLM - meanCLM n₁) (sliceMean f)‖ ^ 2 ≤
    spectralGap G₁ ^ 2 * ‖sliceMean f‖ ^ 2 := by
  have h := spectralGap_apply_le G₁ (sliceMean f)
  have ha : 0 ≤ ‖(G₁.walkCLM - meanCLM n₁) (sliceMean f)‖ := norm_nonneg _
  calc ‖(G₁.walkCLM - meanCLM n₁) (sliceMean f)‖ ^ 2
      ≤ (spectralGap G₁ * ‖sliceMean f‖) ^ 2 := sq_le_sq' (by linarith) h
    _ = spectralGap G₁ ^ 2 * ‖sliceMean f‖ ^ 2 := by ring

-- Cauchy-Schwarz on slices: n₂ · ‖sliceMean f‖² ≤ ‖f‖²
private theorem sliceMean_norm_sq_le {n₁ n₂ : ℕ} (hn₂ : 0 < n₂)
    (f : EuclideanSpace ℝ (Fin (n₁ * n₂))) :
    ↑n₂ * ‖sliceMean f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, norm_sq_eq_sum_slice hn₂ f]
  simp_rw [Real.norm_eq_abs, sq_abs, sliceMean_apply, slice_norm_sq]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro v₁ _
  have hn₂' : (0 : ℝ) < ↑n₂ := Nat.cast_pos.mpr hn₂
  have key : (∑ v₂ : Fin n₂,
      f ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩) ^ 2 ≤
      ↑n₂ * ∑ v₂ : Fin n₂,
      (f ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩) ^ 2 := by
    have h := @sq_sum_le_card_mul_sum_sq _ ℝ _ _ _ _ Finset.univ
      (fun v₂ ↦ f ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    convert h using 1
  calc (n₂ : ℝ) * ((∑ v₂ : Fin n₂,
        f ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩) / ↑n₂) ^ 2
      = (∑ v₂ : Fin n₂,
        f ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩) ^ 2 / ↑n₂ := by field_simp
    _ ≤ (↑n₂ * ∑ v₂ : Fin n₂,
        (f ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩) ^ 2) / ↑n₂ :=
        div_le_div_of_nonneg_right key (by positivity)
    _ = ∑ v₂ : Fin n₂,
        (f ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩) ^ 2 := by field_simp

-- Variance decomposition: ∑ (g - c)² + n·c² = ∑ g²  when ∑g = n·c
private theorem sum_sq_decomp {m : ℕ} (g : Fin m → ℝ) (c : ℝ)
    (hsum : ∑ i, g i = ↑m * c) :
    ∑ i, (g i - c) ^ 2 + ↑m * c ^ 2 = ∑ i, g i ^ 2 := by
  have h1 : ∑ i : Fin m, (2 * g i * c) = 2 * c * ∑ i, g i := by
    rw [Finset.mul_sum]; congr 1; ext i; ring
  simp only [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [h1, hsum]; ring

-- The v₂-marginal of (W_K - P_K)f equals n₂ · ((W₁ - P₁)(sliceMean f))(v₁).
-- This is the key identity that enables the orthogonal decomposition.
private theorem kronecker_marginal {n₁ n₂ d₁ d₂ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (G₂ : RegularGraph n₂ d₂)
    (hn₂ : 0 < n₂) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (f : EuclideanSpace ℝ (Fin (n₁ * n₂))) (v₁ : Fin n₁) :
    ∑ v₂ : Fin n₂, ((G₁.kronecker G₂).walkCLM - meanCLM (n₁ * n₂)) f
      ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩ =
    ↑n₂ * ((G₁.walkCLM - meanCLM n₁) (sliceMean f)) v₁ := by
  have hn₂' : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn₁' : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := @Fin.pos' n₁ ⟨v₁⟩; omega)
  have hd₁' : (d₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hd₂' : (d₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Walk part: ∑ v₂, (W_K f)(v₁,v₂) = n₂ · (W₁ h)(v₁)
  have hW : ∑ v₂ : Fin n₂, (G₁.kronecker G₂).walkCLM f
      ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩ =
    ↑n₂ * G₁.walkCLM (sliceMean f) v₁ := by
    simp_rw [kronecker_walkCLM_apply G₁ G₂ hd₂ f v₁]
    rw [← Finset.sum_div]
    -- LHS: (∑ v₂ ∑ i ∑ j f(nbr₁(v₁,i)*n₂+nbr₂(v₂,j))) / (d₁ * d₂)
    rw [Finset.sum_comm (f := fun v₂ i ↦ _)]
    -- Now: (∑ i ∑ v₂ ∑ j ...) / (d₁ * d₂)
    -- For each i, use sum_neighbor_eq for G₂
    have hinner : ∀ i : Fin d₁,
        ∑ v₂ : Fin n₂, ∑ j : Fin d₂,
          f ⟨(G₁.neighbor v₁ i).val * n₂ + (G₂.neighbor v₂ j).val,
            Fin.pair_lt (G₁.neighbor v₁ i) (G₂.neighbor v₂ j)⟩ =
        ∑ v₂ : Fin n₂, ∑ _j : Fin d₂,
          f ⟨(G₁.neighbor v₁ i).val * n₂ + v₂.val,
            Fin.pair_lt (G₁.neighbor v₁ i) v₂⟩ := by
      intro i
      exact G₂.sum_neighbor_eq (fun v₂ ↦
        f ⟨(G₁.neighbor v₁ i).val * n₂ + v₂.val,
          Fin.pair_lt (G₁.neighbor v₁ i) v₂⟩)
    simp_rw [hinner]
    -- Now inner sum is d₂ copies of the same thing
    simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    -- LHS: (∑ i, ∑ v₂, d₂ * f(...)) / (d₁ * d₂)
    -- Factor d₂ out of inner and outer sums
    simp_rw [← Finset.mul_sum]
    -- Now: (d₂ * ∑ i, ∑ v₂, f(...)) / (d₁ * d₂)
    rw [mul_comm (↑d₁ : ℝ) (↑d₂ : ℝ), mul_div_mul_left _ _ hd₂']
    -- (∑ i, ∑ v₂, f(nbr₁(v₁,i), v₂)) / d₁ = n₂ * (W₁ h) v₁
    -- Rewrite RHS: n₂ * (∑ i, sliceMean f (nbr)) / d₁
    show _ = ↑n₂ * (G₁.walkCLM (sliceMean f)).ofLp v₁
    rw [show (G₁.walkCLM (sliceMean f)).ofLp v₁ =
      (∑ i, (sliceMean f) (G₁.neighbor v₁ i)) / ↑d₁ from by
        show _ = _; rw [RegularGraph.walkCLM_apply]]
    simp only [sliceMean_apply]
    -- Both sides: (∑ i, ∑ v₂, f(...)) / d₁ = n₂ * ((∑ i, (∑ v₂, f(...)) / n₂) / d₁)
    -- Pull n₂ inside division, cancel n₂ with each /n₂
    rw [← mul_div_assoc]; congr 1
    rw [Finset.mul_sum]; congr 1; ext i
    rw [mul_div_cancel₀ _ hn₂']
  -- Mean part: ∑ v₂, (P_K f)(v₁,v₂) = n₂ · (P₁ h)(v₁)
  have hP : ∑ v₂ : Fin n₂, meanCLM (n₁ * n₂) f
      ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩ =
    ↑n₂ * meanCLM n₁ (sliceMean f) v₁ := by
    simp only [meanCLM_apply, sliceMean_apply]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    -- LHS: n₂ * ((∑ u, f u) / (n₁ * n₂))
    -- RHS: n₂ * ((∑ u₁, (∑ v₂, f(u₁,v₂)) / n₂) / n₁)
    congr 1
    rw [kronecker_sum_vertex_eq hn₂]
    simp_rw [Finset.sum_div, div_div, mul_comm (↑n₂ : ℝ) (↑n₁ : ℝ), ← Nat.cast_mul]
  -- Combine: ∑ (Wf - Pf) = ∑ Wf - ∑ Pf = n₂·W₁h - n₂·P₁h = n₂·(W₁-P₁)h
  have hsplit : ∀ v₂ : Fin n₂,
      ((G₁.kronecker G₂).walkCLM - meanCLM (n₁ * n₂)) f
        ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩ =
      (G₁.kronecker G₂).walkCLM f ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩ -
      meanCLM (n₁ * n₂) f ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩ :=
    fun _ ↦ rfl
  simp_rw [hsplit, Finset.sum_sub_distrib, hW, hP]
  show _ = ↑n₂ * ((G₁.walkCLM - meanCLM n₁) (sliceMean f)).ofLp v₁
  rw [ContinuousLinearMap.sub_apply,
      show (G₁.walkCLM (sliceMean f) - (meanCLM n₁) (sliceMean f)).ofLp v₁ =
        (G₁.walkCLM (sliceMean f)).ofLp v₁ - ((meanCLM n₁) (sliceMean f)).ofLp v₁ from rfl]
  ring

-- Tighter spectral gap using (W-P)P = 0: ‖(W-P)g‖² ≤ λ²·(‖g‖² - ‖Pg‖²)
private theorem spectralGap_apply_tight {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d)
    (g : EuclideanSpace ℝ (Fin n)) :
    ‖(G.walkCLM - meanCLM n) g‖ ^ 2 ≤
    spectralGap G ^ 2 * (‖g‖ ^ 2 - ‖meanCLM n g‖ ^ 2) := by
  have hsa : ContinuousLinearMap.adjoint (meanCLM n) = meanCLM n :=
    meanCLM_isSelfAdjoint n
  have hP2 : meanCLM n (meanCLM n g) = meanCLM n g :=
    ContinuousLinearMap.ext_iff.mp (meanCLM_idempotent n) g
  have hWP : (G.walkCLM - meanCLM n) g = (G.walkCLM - meanCLM n) (g - meanCLM n g) := by
    have h1 : G.walkCLM (meanCLM n g) = meanCLM n g := walkCLM_comp_meanCLM G hd g
    simp only [ContinuousLinearMap.sub_apply, map_sub, h1, hP2, sub_self, sub_zero]
  rw [hWP]
  have hspec := (G.walkCLM - meanCLM n).le_opNorm (g - meanCLM n g)
  have hPyth : ‖g - meanCLM n g‖ ^ 2 = ‖g‖ ^ 2 - ‖meanCLM n g‖ ^ 2 := by
    rw [norm_sub_sq_real]
    suffices h : @inner ℝ _ _ g (meanCLM n g) = ‖meanCLM n g‖ ^ 2 by linarith
    rw [← real_inner_self_eq_norm_sq]
    have key := ContinuousLinearMap.adjoint_inner_left (meanCLM n) g (meanCLM n g)
    rw [hsa, hP2] at key
    rwa [real_inner_comm] at key
  calc ‖(G.walkCLM - meanCLM n) (g - meanCLM n g)‖ ^ 2
      ≤ (spectralGap G * ‖g - meanCLM n g‖) ^ 2 := by
        apply sq_le_sq'
        · linarith [norm_nonneg ((G.walkCLM - meanCLM n) (g - meanCLM n g)),
                     mul_nonneg (spectralGap_nonneg G) (norm_nonneg (g - meanCLM n g))]
        · exact hspec
    _ = spectralGap G ^ 2 * ‖g - meanCLM n g‖ ^ 2 := by ring
    _ = spectralGap G ^ 2 * (‖g‖ ^ 2 - ‖meanCLM n g‖ ^ 2) := by rw [hPyth]

-- ‖Pg‖² = n · (mean(g))² for the mean projection
private theorem meanCLM_norm_sq {m : ℕ} (g : EuclideanSpace ℝ (Fin m)) :
    ‖meanCLM m g‖ ^ 2 = ↑m * (((∑ i, g i) / ↑m) ^ 2) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs, meanCLM_apply]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

-- The A-term equals the average of slice deviations.
-- Key insight: mean parts cancel (P_K f(v) = P₁(h)(v₁)), leaving only walk difference.
private theorem kronecker_A_eq {n₁ n₂ d₁ d₂ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (G₂ : RegularGraph n₂ d₂)
    (hn₂ : 0 < n₂) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (f : EuclideanSpace ℝ (Fin (n₁ * n₂))) (v₁ : Fin n₁) (v₂ : Fin n₂) :
    ((G₁.kronecker G₂).walkCLM - meanCLM (n₁ * n₂)) f
      ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩ -
    ((G₁.walkCLM - meanCLM n₁) (sliceMean f)) v₁ =
    (∑ i : Fin d₁, ((G₂.walkCLM - meanCLM n₂) (slice f (G₁.neighbor v₁ i))) v₂) /
    ↑d₁ := by
  have hd₁' : (d₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hd₂' : (d₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn₂' : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Mean cancellation: P_K f(v₁,v₂) = P₁(sliceMean f)(v₁)
  have hmean : meanCLM (n₁ * n₂) f ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩ =
      meanCLM n₁ (sliceMean f) v₁ := by
    simp only [meanCLM_apply, sliceMean]
    rw [kronecker_sum_vertex_eq hn₂]; simp_rw [Finset.sum_div]
    push_cast [Nat.cast_mul]; simp_rw [div_div, mul_comm (n₂ : ℝ) (n₁ : ℝ)]
  -- Reduce to walk difference using mean cancellation
  suffices hwalk :
      (G₁.kronecker G₂).walkCLM f ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩ -
      G₁.walkCLM (sliceMean f) v₁ =
      (∑ i : Fin d₁, ((G₂.walkCLM - meanCLM n₂) (slice f (G₁.neighbor v₁ i))) v₂) /
      ↑d₁ by
    have h1 : ((G₁.kronecker G₂).walkCLM - meanCLM (n₁ * n₂)) f
        ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩ =
      (G₁.kronecker G₂).walkCLM f ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩ -
      meanCLM (n₁ * n₂) f ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩ := rfl
    have h2 : ((G₁.walkCLM - meanCLM n₁) (sliceMean f)) v₁ =
      G₁.walkCLM (sliceMean f) v₁ - meanCLM n₁ (sliceMean f) v₁ := rfl
    rw [h1, h2, hmean]; linarith
  -- Expand RHS per-summand: (W₂-P₂)(slice)(v₂) as raw sums
  have hRHS_i : ∀ i : Fin d₁,
      ((G₂.walkCLM - meanCLM n₂) (slice f (G₁.neighbor v₁ i))) v₂ =
      (∑ j : Fin d₂, f ⟨(G₁.neighbor v₁ i).val * n₂ + (G₂.neighbor v₂ j).val,
        Fin.pair_lt (G₁.neighbor v₁ i) (G₂.neighbor v₂ j)⟩) / ↑d₂ -
      (∑ u₂ : Fin n₂, f ⟨(G₁.neighbor v₁ i).val * n₂ + u₂.val,
        Fin.pair_lt (G₁.neighbor v₁ i) u₂⟩) / ↑n₂ := by
    intro i
    show (G₂.walkCLM (slice f (G₁.neighbor v₁ i)) v₂ -
      meanCLM n₂ (slice f (G₁.neighbor v₁ i)) v₂ : ℝ) = _
    rw [RegularGraph.walkCLM_apply, meanCLM_apply]; simp only [slice]
  simp_rw [hRHS_i, Finset.sum_sub_distrib, Finset.sum_div]
  -- Expand LHS walk operators
  rw [kronecker_walkCLM_apply G₁ G₂ hd₂ f v₁ v₂, RegularGraph.walkCLM_apply]
  simp only [sliceMean]
  -- Both sides: walk/(d₁*d₂) - mean_sum/d₁ = walk_sum/d₂/d₁ - mean_sum/n₂/d₁
  rw [sub_div]; congr 1
  · simp_rw [← Finset.sum_div]; rw [div_div, mul_comm (d₂ : ℝ)]
  · congr 1; congr 1; ext i; rw [Finset.sum_div]

-- The "A-part" bound: within-fiber deviation via Jensen + double-counting.
private theorem kronecker_A_bound {n₁ n₂ d₁ d₂ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (G₂ : RegularGraph n₂ d₂)
    (hn₂ : 0 < n₂) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (f : EuclideanSpace ℝ (Fin (n₁ * n₂))) :
    ∑ v₁ : Fin n₁, ∑ v₂ : Fin n₂,
      (((G₁.kronecker G₂).walkCLM - meanCLM (n₁ * n₂)) f
        ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩ -
       ((G₁.walkCLM - meanCLM n₁) (sliceMean f)) v₁) ^ 2 ≤
    spectralGap G₂ ^ 2 * (‖f‖ ^ 2 - ↑n₂ * ‖sliceMean f‖ ^ 2) := by
  have hd₁' : (d₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hd₁_pos : (0 : ℝ) < ↑d₁ := Nat.cast_pos.mpr hd₁
  -- Step 1: Rewrite A using the identity
  simp_rw [kronecker_A_eq G₁ G₂ hn₂ hd₁ hd₂ f]
  -- Step 2: Jensen per (v₁, v₂): ((∑ a_i)/d₁)² ≤ (∑ a_i²)/d₁
  have hjensen : ∀ v₁ : Fin n₁, ∀ v₂ : Fin n₂,
      ((∑ i : Fin d₁, ((G₂.walkCLM - meanCLM n₂) (slice f (G₁.neighbor v₁ i))) v₂) /
       ↑d₁) ^ 2 ≤
      (∑ i : Fin d₁, (((G₂.walkCLM - meanCLM n₂) (slice f (G₁.neighbor v₁ i))) v₂) ^ 2) /
       ↑d₁ := by
    intro v₁ v₂
    have cs := @sq_sum_le_card_mul_sum_sq (Fin d₁) ℝ _ _ _ _ Finset.univ
      (fun i ↦ ((G₂.walkCLM - meanCLM n₂) (slice f (G₁.neighbor v₁ i))) v₂)
    simp only [Finset.card_univ, Fintype.card_fin] at cs
    rw [div_pow, sq (d₁ : ℝ), ← div_div]
    exact div_le_div_of_nonneg_right (div_le_iff₀ hd₁_pos |>.mpr (by rw [mul_comm]; exact cs))
      hd₁_pos.le
  -- Step 3: Sum Jensen over v₂, then use spectral gap
  calc ∑ v₁ : Fin n₁, ∑ v₂ : Fin n₂, _ ≤
      ∑ v₁ : Fin n₁, ∑ v₂ : Fin n₂,
        (∑ i : Fin d₁, (((G₂.walkCLM - meanCLM n₂)
          (slice f (G₁.neighbor v₁ i))) v₂) ^ 2) / ↑d₁ :=
        Finset.sum_le_sum (fun v₁ _ ↦ Finset.sum_le_sum (fun v₂ _ ↦ hjensen v₁ v₂))
    _ = (∑ v₁ : Fin n₁, ∑ v₂ : Fin n₂, ∑ i : Fin d₁,
          (((G₂.walkCLM - meanCLM n₂) (slice f (G₁.neighbor v₁ i))) v₂) ^ 2) / ↑d₁ := by
        simp_rw [Finset.sum_div]
    _ = (∑ v₁ : Fin n₁, ∑ i : Fin d₁,
          ‖(G₂.walkCLM - meanCLM n₂) (slice f (G₁.neighbor v₁ i))‖ ^ 2) / ↑d₁ := by
        congr 1; congr 1; ext v₁
        rw [Finset.sum_comm]; congr 1; ext i
        rw [EuclideanSpace.norm_sq_eq]; congr 1; ext v₂
        simp [Real.norm_eq_abs, sq_abs]
    -- Step 4: Apply tighter spectral gap
    _ ≤ (∑ v₁ : Fin n₁, ∑ i : Fin d₁,
          spectralGap G₂ ^ 2 * (‖slice f (G₁.neighbor v₁ i)‖ ^ 2 -
            ‖meanCLM n₂ (slice f (G₁.neighbor v₁ i))‖ ^ 2)) / ↑d₁ := by
        apply div_le_div_of_nonneg_right _ hd₁_pos.le
        apply Finset.sum_le_sum; intro v₁ _
        apply Finset.sum_le_sum; intro i _
        exact spectralGap_apply_tight G₂ hd₂ _
    -- Step 5: Factor λ₂², double-count, cancel d₁, expand norms
    _ = spectralGap G₂ ^ 2 * (‖f‖ ^ 2 - ↑n₂ * ‖sliceMean f‖ ^ 2) := by
        -- Double-count with the combined function
        set g := fun u₁ ↦ ‖slice f u₁‖ ^ 2 - ‖meanCLM n₂ (slice f u₁)‖ ^ 2
        have hdc := G₁.sum_neighbor_eq g
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hdc
        -- Factor λ₂² out of inner sum
        simp_rw [← Finset.mul_sum]
        -- Now: (λ₂² * ∑ v₁ ∑ i g(nbr)) / d₁
        rw [mul_div_assoc]
        -- Now: λ₂² * (∑ v₁ ∑ i g(nbr)) / d₁
        rw [hdc, ← Finset.mul_sum, mul_div_cancel_left₀ _ hd₁']
        -- Now: λ₂² * ∑ v₁ g(v₁) = λ₂² * (‖f‖² - n₂·‖h‖²)
        congr 1
        -- Expand: ∑ g(v₁) = ∑ ‖slice‖² - ∑ ‖P₂(slice)‖² = ‖f‖² - n₂·‖h‖²
        simp only [g, Finset.sum_sub_distrib]
        rw [norm_sq_eq_sum_slice hn₂]
        congr 1
        -- ∑ ‖P₂(slice f v₁)‖² = n₂·‖sliceMean f‖²
        rw [EuclideanSpace.norm_sq_eq]
        simp_rw [Real.norm_eq_abs, sq_abs, meanCLM_norm_sq]
        rw [Finset.mul_sum]
        simp_rw [sliceMean_apply, slice_apply]

-- Core decomposition bound via A+B orthogonal decomposition.
-- Proof: variance decomposition per fiber, then A-bound + B-bound.
private theorem kronecker_norm_decomp {n₁ n₂ d₁ d₂ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (G₂ : RegularGraph n₂ d₂)
    (hn₂ : 0 < n₂) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (f : EuclideanSpace ℝ (Fin (n₁ * n₂))) :
    ‖((G₁.kronecker G₂).walkCLM - meanCLM (n₁ * n₂)) f‖ ^ 2 ≤
    spectralGap G₂ ^ 2 * (‖f‖ ^ 2 - ↑n₂ * ‖sliceMean f‖ ^ 2) +
    ↑n₂ * (spectralGap G₁ ^ 2 * ‖sliceMean f‖ ^ 2) := by
  set B : Fin n₁ → ℝ := fun v₁ ↦ ((G₁.walkCLM - meanCLM n₁) (sliceMean f)) v₁
  -- Step 1: Expand LHS as double sum
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs]
  rw [kronecker_sum_vertex_eq hn₂]
  -- Step 2: Variance decomposition per fiber
  have hsum := kronecker_marginal G₁ G₂ hn₂ hd₁ hd₂ f
  have hvar : ∀ v₁ : Fin n₁,
      ∑ v₂ : Fin n₂, (((G₁.kronecker G₂).walkCLM - meanCLM (n₁ * n₂)) f
        ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩) ^ 2 =
      ∑ v₂ : Fin n₂, (((G₁.kronecker G₂).walkCLM - meanCLM (n₁ * n₂)) f
        ⟨v₁.val * n₂ + v₂.val, Fin.pair_lt v₁ v₂⟩ - B v₁) ^ 2 +
      ↑n₂ * (B v₁) ^ 2 := by
    intro v₁
    exact (sum_sq_decomp _ (B v₁) (hsum v₁)).symm
  simp_rw [hvar, Finset.sum_add_distrib, ← Finset.mul_sum]
  -- Goal: ∑ (Wf-B)² + n₂ · ∑ B² ≤ RHS
  have hA := kronecker_A_bound G₁ G₂ hn₂ hd₁ hd₂ f
  have hB : ↑n₂ * ∑ v₁ : Fin n₁, (B v₁) ^ 2 ≤
      ↑n₂ * (spectralGap G₁ ^ 2 * ‖sliceMean f‖ ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n₂)
    -- ∑ B² = ‖(W₁-P₁)(sliceMean f)‖²
    have hBeq : ∑ v₁ : Fin n₁, (B v₁) ^ 2 =
        ‖(G₁.walkCLM - meanCLM n₁) (sliceMean f)‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      congr 1; ext v₁; show (B v₁) ^ 2 = ‖B v₁‖ ^ 2
      rw [Real.norm_eq_abs, sq_abs]
    rw [hBeq]
    exact mean_deviation_bound G₁ f
  linarith

-- Key bound: ‖(W_K-P)f‖² ≤ max(λ₁,λ₂)² · ‖f‖²
private theorem kronecker_sq_norm_bound {n₁ n₂ d₁ d₂ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (G₂ : RegularGraph n₂ d₂)
    (f : EuclideanSpace ℝ (Fin (n₁ * n₂))) :
    ‖((G₁.kronecker G₂).walkCLM - meanCLM (n₁ * n₂)) f‖ ^ 2 ≤
    (max (spectralGap G₁) (spectralGap G₂)) ^ 2 * ‖f‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos n₂ with rfl | hn₂
  · have : Subsingleton (EuclideanSpace ℝ (Fin (n₁ * 0))) := by
      rw [show n₁ * 0 = 0 from by omega]; infer_instance
    simp [Subsingleton.elim f 0]
  rcases Nat.eq_zero_or_pos n₁ with rfl | hn₁
  · have : Subsingleton (EuclideanSpace ℝ (Fin (0 * n₂))) := by
      rw [show 0 * n₂ = 0 from by omega]; infer_instance
    simp [Subsingleton.elim f 0]
  -- d₁ = 0 or d₂ = 0: Kronecker degree is 0, use spectralGap_zero_degree
  -- When degree 0: ‖(W-P)f‖ ≤ ‖f‖ (spectralGap ≤ 1), and max(λ₁,λ₂) ≥ 1
  have degree_zero_case (hle_f : ‖((G₁.kronecker G₂).walkCLM - meanCLM (n₁ * n₂)) f‖ ≤ ‖f‖)
      (hmax : 1 ≤ max (spectralGap G₁) (spectralGap G₂)) :
      ‖((G₁.kronecker G₂).walkCLM - meanCLM (n₁ * n₂)) f‖ ^ 2 ≤
      (max (spectralGap G₁) (spectralGap G₂)) ^ 2 * ‖f‖ ^ 2 :=
    calc _ ≤ ‖f‖ ^ 2 := by nlinarith [norm_nonneg (((G₁.kronecker G₂).walkCLM - meanCLM (n₁ * n₂)) f)]
       _ ≤ _ := le_mul_of_one_le_left (sq_nonneg _)
         ((one_le_sq_iff₀ (le_max_of_le_left (spectralGap_nonneg G₁))).mpr hmax)
  rcases Nat.eq_zero_or_pos d₁ with rfl | hd₁
  · exact degree_zero_case
      (((G₁.kronecker G₂).walkCLM - meanCLM (n₁ * n₂)).le_opNorm f |>.trans
        (mul_le_of_le_one_left (norm_nonneg f) (spectralGap_le_one _)))
      (by rw [spectralGap_zero_degree G₁ hn₁]; exact le_max_left _ _)
  rcases Nat.eq_zero_or_pos d₂ with rfl | hd₂
  · exact degree_zero_case
      (((G₁.kronecker G₂).walkCLM - meanCLM (n₁ * n₂)).le_opNorm f |>.trans
        (mul_le_of_le_one_left (norm_nonneg f) (spectralGap_le_one _)))
      (by rw [spectralGap_zero_degree G₂ hn₂]; exact le_max_right _ _)
  -- Main case: d₁ > 0, d₂ > 0
  -- S = n₂ · ‖sliceMean f‖², with 0 ≤ S ≤ ‖f‖²
  have hS_nonneg : 0 ≤ ↑n₂ * ‖sliceMean f‖ ^ 2 :=
    mul_nonneg (Nat.cast_nonneg n₂) (sq_nonneg _)
  have hS_le := sliceMean_norm_sq_le hn₂ f
  -- Combine decomposition with max algebra
  calc ‖((G₁.kronecker G₂).walkCLM - meanCLM (n₁ * n₂)) f‖ ^ 2
      ≤ spectralGap G₂ ^ 2 * (‖f‖ ^ 2 - ↑n₂ * ‖sliceMean f‖ ^ 2) +
        ↑n₂ * (spectralGap G₁ ^ 2 * ‖sliceMean f‖ ^ 2) :=
        kronecker_norm_decomp G₁ G₂ hn₂ hd₁ hd₂ f
    _ = spectralGap G₂ ^ 2 * (‖f‖ ^ 2 - ↑n₂ * ‖sliceMean f‖ ^ 2) +
        spectralGap G₁ ^ 2 * (↑n₂ * ‖sliceMean f‖ ^ 2) := by ring
    _ ≤ (max (spectralGap G₁) (spectralGap G₂)) ^ 2 * ‖f‖ ^ 2 := by
        -- Algebra: b²(X-S) + a²S ≤ max(a,b)²X for 0 ≤ S ≤ X
        rcases le_or_gt (spectralGap G₁) (spectralGap G₂) with hab | hab
        · rw [max_eq_right hab]
          nlinarith [sq_nonneg (spectralGap G₂ - spectralGap G₁),
                     mul_nonneg (sub_nonneg.mpr hab) (spectralGap_nonneg G₁),
                     mul_nonneg hS_nonneg (sub_nonneg.mpr hab)]
        · rw [max_eq_left (le_of_lt hab)]
          nlinarith [sq_nonneg (spectralGap G₁ - spectralGap G₂),
                     mul_nonneg (sub_nonneg.mpr (le_of_lt hab)) (spectralGap_nonneg G₂),
                     mul_nonneg (sub_nonneg.mpr hS_le) (sub_nonneg.mpr (le_of_lt hab))]

theorem spectralGap_kronecker {n₁ n₂ d₁ d₂ : ℕ}
    (G₁ : RegularGraph n₁ d₁) (G₂ : RegularGraph n₂ d₂) :
    spectralGap (G₁.kronecker G₂) ≤ max (spectralGap G₁) (spectralGap G₂) := by
  show ‖(G₁.kronecker G₂).walkCLM - meanCLM (n₁ * n₂)‖ ≤
    max (spectralGap G₁) (spectralGap G₂)
  apply ContinuousLinearMap.opNorm_le_bound _
    (le_max_of_le_left (spectralGap_nonneg G₁))
  intro f
  -- Reduce to squared norms: ‖x‖ ≤ M*‖f‖ ← ‖x‖² ≤ M²*‖f‖² (for M ≥ 0)
  have hM : 0 ≤ max (spectralGap G₁) (spectralGap G₂) * ‖f‖ :=
    mul_nonneg (le_max_of_le_left (spectralGap_nonneg G₁)) (norm_nonneg f)
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hM]
  apply Real.sqrt_le_sqrt
  rw [mul_pow]
  exact kronecker_sq_norm_bound G₁ G₂ f

end
