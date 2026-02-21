/-
  # General Graphs (Half-Edge Representation)

  A general graph on `n` vertices, allowing irregular degree, multi-edges,
  and self-loops. Represented via half-edges with a rotation (pairing)
  involution, generalizing the `RegularGraph` rotation map.

  The key operation is `Graph.contract`: given a surjection `s : Fin n → Fin m`,
  relabel vertices while keeping half-edges and pairing unchanged. This produces
  an irregular multigraph whose spectral gap is at most that of the original.

  Used to reduce arbitrary-size expanders from the zig-zag family (which only
  produces graphs at sizes `D^(4(k+1))`) to any target size `m`.
-/

import AKS.Graph.Regular

open Finset BigOperators


/-! **General Graph** -/

/-- A graph on `n` vertices, represented by half-edges with a pairing involution.

    Each half-edge `e ∈ Fin halfs` has a source vertex `src e`.
    The rotation map `rot` pairs half-edges: if `rot e = e'`, then
    `{src e, src e'}` is an edge. The involution ensures each edge is
    seen from both sides.

    Compared to `RegularGraph n d` (which has exactly `n * d` half-edges,
    `d` per vertex), `Graph n` allows irregular degree. -/
structure Graph (n : ℕ) where
  /-- The total number of half-edges (= sum of degrees = 2 * number of edges). -/
  halfs : ℕ
  /-- The source vertex of each half-edge. -/
  src : Fin halfs → Fin n
  /-- The half-edge pairing: `rot e` is the other half of the edge containing `e`. -/
  rot : Fin halfs → Fin halfs
  /-- Pairing is an involution. -/
  rot_involution : ∀ e, rot (rot e) = e

/-- The target vertex of a half-edge: the vertex at the other end. -/
def Graph.target {n : ℕ} (G : Graph n) (e : Fin G.halfs) : Fin n :=
  G.src (G.rot e)

/-- The degree of a vertex: the number of half-edges sourced at it. -/
def Graph.deg {n : ℕ} (G : Graph n) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun e => G.src e = v)).card

/-- The rotation map as an equivalence (since it's an involution). -/
def Graph.rotEquiv {n : ℕ} (G : Graph n) :
    Fin G.halfs ≃ Fin G.halfs where
  toFun := G.rot
  invFun := G.rot
  left_inv := G.rot_involution
  right_inv := G.rot_involution


/-! **Contraction** -/

/-- Contract a graph by relabeling vertices via `s : Fin n → Fin m`.

    Half-edges and their pairing are unchanged; only vertex labels change.
    Self-loops arise when `s(src e) = s(target e)`. Multi-edges arise when
    multiple half-edge pairs map to the same vertex pair.

    This is the key construction for building expanders at arbitrary sizes:
    take an oversized zig-zag family member and contract to the target size. -/
def Graph.contract {n : ℕ} (G : Graph n) {m : ℕ} (s : Fin n → Fin m) : Graph m where
  halfs := G.halfs
  src e := s (G.src e)
  rot := G.rot
  rot_involution := G.rot_involution

@[simp]
theorem Graph.contract_halfs {n : ℕ} (G : Graph n) {m : ℕ} (s : Fin n → Fin m) :
    (G.contract s).halfs = G.halfs :=
  rfl

@[simp]
theorem Graph.contract_src {n : ℕ} (G : Graph n) {m : ℕ} (s : Fin n → Fin m)
    (e : Fin (G.contract s).halfs) :
    (G.contract s).src e = s (G.src e) :=
  rfl

@[simp]
theorem Graph.contract_rot {n : ℕ} (G : Graph n) {m : ℕ} (s : Fin n → Fin m)
    (e : Fin (G.contract s).halfs) :
    (G.contract s).rot e = G.rot e :=
  rfl

@[simp]
theorem Graph.contract_target {n : ℕ} (G : Graph n) {m : ℕ} (s : Fin n → Fin m)
    (e : Fin (G.contract s).halfs) :
    (G.contract s).target e = s (G.target e) :=
  rfl


/-! **Embedding Regular Graphs** -/

/-- Encode a `RegularGraph` rotation result as a half-edge index. -/
private def rgEncode {n d : ℕ} (r : Fin n × Fin d) : Fin (n * d) :=
  ⟨r.1.val * d + r.2.val, Fin.pair_lt r.1 r.2⟩

/-- Decode a half-edge index into vertex and port. -/
private def rgVertex {n d : ℕ} (hd : 0 < d) (e : Fin (n * d)) : Fin n :=
  ⟨e.val / d, (Nat.div_lt_iff_lt_mul hd).mpr e.isLt⟩

private def rgPort {n d : ℕ} (hd : 0 < d) (e : Fin (n * d)) : Fin d :=
  ⟨e.val % d, Nat.mod_lt _ hd⟩

private theorem rgEncode_val {n d : ℕ} (r : Fin n × Fin d) :
    (rgEncode r).val = r.1.val * d + r.2.val := rfl

private theorem rgDecode_encode {n d : ℕ} (hd : 0 < d) (e : Fin (n * d)) :
    rgEncode (rgVertex hd e, rgPort hd e) = e := by
  apply Fin.ext; simp only [rgEncode, rgVertex, rgPort]
  have := Nat.div_add_mod e.val d
  rw [Nat.mul_comm] at this; omega

private theorem rgVertex_encode {n d : ℕ} (hd : 0 < d) (r : Fin n × Fin d) :
    rgVertex hd (rgEncode r) = r.1 := by
  apply Fin.ext; simp only [rgVertex, rgEncode]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt r.2.isLt]; omega

private theorem rgPort_encode {n d : ℕ} (hd : 0 < d) (r : Fin n × Fin d) :
    rgPort hd (rgEncode r) = r.2 := by
  apply Fin.ext; simp only [rgPort, rgEncode]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r.2.isLt]

/-- The rotation map for `RegularGraph.toGraph`. -/
private def rgRot {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d)
    (e : Fin (n * d)) : Fin (n * d) :=
  rgEncode (G.rot (rgVertex hd e, rgPort hd e))

private theorem rgRot_involution {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d)
    (e : Fin (n * d)) : rgRot G hd (rgRot G hd e) = e := by
  simp only [rgRot, rgVertex_encode, rgPort_encode, Prod.mk.eta, G.rot_involution,
    rgDecode_encode]

/-- Convert a `RegularGraph n d` to a `Graph n`.

    The `n * d` half-edges are indexed by `Fin (n * d)`, encoding
    the pair `(v, p) : Fin n × Fin d` as `v.val * d + p.val`.
    The source of half-edge `e` is `e / d` (the vertex index). -/
def RegularGraph.toGraph {n d : ℕ} (G : RegularGraph n d) : Graph n where
  halfs := n * d
  src e := ⟨e.val / d, by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact absurd e.isLt (by simp)
    · exact (Nat.div_lt_iff_lt_mul hd).mpr e.isLt⟩
  rot e :=
    if hd : 0 < d then rgRot G hd e
    else absurd e.isLt (by simp [Nat.eq_zero_of_not_pos hd])
  rot_involution e := by
    show (if hd : 0 < d then _ else _) = e
    split
    · next hd => exact rgRot_involution G hd e
    · next hd => exact absurd e.isLt (by simp [Nat.eq_zero_of_not_pos hd])

@[simp]
theorem RegularGraph.toGraph_halfs {n d : ℕ} (G : RegularGraph n d) :
    G.toGraph.halfs = n * d :=
  rfl


/-! **Regular Graph Embedding Properties** -/

/-- Target vertex in `toGraph` expressed via the rotation map. -/
private theorem RegularGraph.toGraph_target_eq {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d)
    (e : Fin (n * d)) :
    G.toGraph.target e = G.neighbor (rgVertex hd e) (rgPort hd e) := by
  show G.toGraph.src (G.toGraph.rot e) = (G.rot (rgVertex hd e, rgPort hd e)).1
  rw [show G.toGraph.rot e = rgRot G hd e from dif_pos hd]
  simp only [rgRot]
  -- G.toGraph.src (rgEncode result) = result.1
  -- Both .val are result.1.val * d + result.2.val) / d = result.1.val
  apply Fin.ext
  show ((G.rot (rgVertex hd e, rgPort hd e)).1.val * d +
    (G.rot (rgVertex hd e, rgPort hd e)).2.val) / d = _
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt (G.rot _).2.isLt]
  omega

/-- Round-trip: rgEncode(v, rgPort(e)) = e when src(e) = v. -/
private theorem rgEncode_rgPort {n d : ℕ} (hd : 0 < d) (v : Fin n) (e : Fin (n * d))
    (hv : e.val / d = v.val) : rgEncode (v, rgPort hd e) = e := by
  apply Fin.ext; simp only [rgEncode, rgPort]
  show v.val * d + e.val % d = e.val
  have := Nat.div_add_mod e.val d; rw [hv] at this
  have := Nat.mul_comm d v.val; omega

/-- Each vertex of a regular graph has degree `d` in `toGraph`. -/
theorem RegularGraph.toGraph_deg {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d)
    (v : Fin n) : G.toGraph.deg v = d := by
  show (univ.filter (fun e => G.toGraph.src e = v)).card = d
  have heq : (univ.filter (fun e => G.toGraph.src e = v)).card = (univ (α := Fin d)).card :=
    Finset.card_nbij' (fun e ↦ rgPort hd e) (fun i ↦ rgEncode (v, i))
      -- Forward: filter → univ (trivial)
      (fun _ _ ↦ mem_coe.mpr (mem_univ _))
      -- Backward: univ → filter
      (fun i _ ↦ mem_coe.mpr (mem_filter.mpr ⟨mem_univ _,
        Fin.ext (congr_arg Fin.val (rgVertex_encode hd (v, i)))⟩))
      -- Left inverse: encode(v, port(e)) = e
      (fun e he ↦ rgEncode_rgPort hd v e
        (congr_arg Fin.val ((mem_filter.mp (mem_coe.mp he)).2)))
      -- Right inverse: port(encode(v, i)) = i
      (fun i _ ↦ rgPort_encode hd (v, i))
  rw [heq, card_univ, Fintype.card_fin]

/-- Summing over half-edges at vertex `v` in `toGraph` equals summing over ports. -/
theorem RegularGraph.toGraph_sum_target {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d)
    (v : Fin n) (f : Fin n → ℝ) :
    ∑ e ∈ univ.filter (G.toGraph.src · = v), f (G.toGraph.target e) =
      ∑ i : Fin d, f (G.neighbor v i) := by
  apply Finset.sum_nbij' (fun e ↦ rgPort hd e) (fun i ↦ rgEncode (v, i))
  -- Forward: filter → univ (trivial)
  · intro _ _; exact mem_univ _
  -- Backward: univ → filter
  · intro i _
    exact mem_filter.mpr ⟨mem_univ _, Fin.ext (congr_arg Fin.val (rgVertex_encode hd (v, i)))⟩
  -- Left inverse: encode(v, port(e)) = e
  · intro e he
    exact rgEncode_rgPort hd v e (congr_arg Fin.val (mem_filter.mp he).2)
  -- Right inverse: port(encode(v, i)) = i
  · intro i _; exact rgPort_encode hd (v, i)
  -- Function agrees: target(e) = neighbor(v, port(e))
  · intro e he
    have hv : e.val / d = v.val := congr_arg Fin.val (mem_filter.mp he).2
    rw [G.toGraph_target_eq hd, show rgVertex hd e = v from Fin.ext hv]


/-! **Double Counting** -/

/-- Double-counting via the rotation bijection: summing `g(target e)` over
    all half-edges equals summing `g(src e)` over all half-edges. -/
theorem Graph.sum_target_eq_sum_src {n : ℕ} (G : Graph n) (g : Fin n → ℝ) :
    ∑ e, g (G.target e) = ∑ e, g (G.src e) := by
  show ∑ e, g (G.src (G.rot e)) = ∑ e, g (G.src e)
  exact G.rotEquiv.sum_comp (fun e ↦ g (G.src e))

/-- The sum of degrees equals the number of half-edges. -/
theorem Graph.sum_deg {n : ℕ} (G : Graph n) :
    ∑ v, G.deg v = G.halfs := by
  simp only [Graph.deg]
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ (α := Fin G.halfs))
    (t := Finset.univ (α := Fin n)) (f := G.src)
    (fun e _ ↦ Finset.mem_univ (G.src e))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  linarith
