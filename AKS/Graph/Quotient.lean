/-
  # Graph Quotient (Vertex Merging)

  Given a `d`-regular graph on `n` vertices and a target size `m ≤ n`,
  merge vertices into `m` classes of size `⌈n/m⌉`, yielding a
  `(d * ⌈n/m⌉)`-regular multigraph on `m` vertices.

  When `m ∤ n`, some classes have fewer real vertices than others;
  excess ports act as self-loops.

  This is the key construction for building expander families at arbitrary
  sizes from the zig-zag family (which only produces graphs at sizes D^(4(k+1))).

  The spectral gap can only decrease: `spectralGap_quotient : spectralGap G.quotient ≤ spectralGap G`.
-/

import AKS.Graph.Regular

open Matrix BigOperators Finset


/-! **Ceiling Division** -/

/-- Ceiling division: `⌈n/m⌉ = (n + m - 1) / m`. -/
private abbrev ceilDiv (n m : ℕ) : ℕ := (n + m - 1) / m

private theorem ceilDiv_pos {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) : 0 < ceilDiv n m :=
  Nat.div_pos (by omega) hm

private theorem le_mul_ceilDiv {n m : ℕ} (hm : 0 < m) : n ≤ m * ceilDiv n m := by
  show n ≤ m * ((n + m - 1) / m)
  have h1 := Nat.div_add_mod (n + m - 1) m
  have h2 := Nat.mod_lt (n + m - 1) hm
  omega


/-! **Nat-Level Encode/Decode Helpers** -/

/-- Dividing `a * r + b` by `r` gives `a`, when `b < r`. -/
private theorem encode_div {r : ℕ} (a b : ℕ) (hr : 0 < r) (hb : b < r) :
    (a * r + b) / r = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hr, Nat.div_eq_of_lt hb]; omega

/-- Taking `a * r + b` mod `r` gives `b`, when `b < r`. -/
private theorem encode_mod {r : ℕ} (a b : ℕ) (hb : b < r) :
    (a * r + b) % r = b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]


/-! **Internal Quotient Machinery** -/

/-- The original vertex index recovered from a quotient vertex-port pair.
    Vertex `u ∈ Fin m` and port `j ∈ Fin (d * r)` decode to original vertex
    `u * r + j % r`. This may be `≥ n` for virtual vertices. -/
private def origVertex {m r d : ℕ} (x : Fin m × Fin (d * r)) : ℕ :=
  x.1.val * r + x.2.val % r

/-- Encode an original vertex-port pair into the quotient's vertex-port pair.
    Vertex v ∈ Fin n maps to quotient vertex v / r, with class member v % r.
    Port q ∈ Fin d and class member v % r encode as q * r + (v % r). -/
private def qEncode {n m r d : ℕ} (hr : 0 < r) (hmr : n ≤ m * r)
    (x : Fin n × Fin d) : Fin m × Fin (d * r) :=
  (⟨x.1.val / r, (Nat.div_lt_iff_lt_mul hr).mpr (lt_of_lt_of_le x.1.isLt hmr)⟩,
   ⟨x.2.val * r + x.1.val % r, Fin.pair_lt x.2 ⟨x.1.val % r, Nat.mod_lt _ hr⟩⟩)

/-- `origVertex` of an encoded pair recovers the original vertex value. -/
private theorem origVertex_qEncode {n m r d : ℕ} (hr : 0 < r) (hmr : n ≤ m * r)
    (x : Fin n × Fin d) : origVertex (qEncode hr hmr x) = x.1.val := by
  simp only [origVertex, qEncode]
  rw [encode_mod x.2.val (x.1.val % r) (Nat.mod_lt _ hr)]
  have := Nat.div_add_mod x.1.val r; rw [Nat.mul_comm] at this; omega

/-- The port division of an encoded pair recovers the original port value. -/
private theorem port_div_qEncode {n m r d : ℕ} (hr : 0 < r) (hmr : n ≤ m * r)
    (x : Fin n × Fin d) : (qEncode hr hmr x).2.val / r = x.2.val := by
  simp only [qEncode]
  exact encode_div x.2.val (x.1.val % r) hr (Nat.mod_lt _ hr)

/-- `origVertex` divided by `r` recovers the quotient vertex. -/
private theorem origVertex_div {m r d : ℕ} (hr : 0 < r)
    (x : Fin m × Fin (d * r)) : origVertex x / r = x.1.val :=
  encode_div x.1.val (x.2.val % r) hr (Nat.mod_lt _ hr)

/-- Port reconstruction: `(j / r) * r + origVertex % r = j`. -/
private theorem port_recon {m r d : ℕ} (hr : 0 < r)
    (x : Fin m × Fin (d * r)) :
    (x.2.val / r) * r + (origVertex x) % r = x.2.val := by
  simp only [origVertex]
  rw [encode_mod x.1.val (x.2.val % r) (Nat.mod_lt _ hr)]
  have := Nat.div_add_mod x.2.val r; rw [Nat.mul_comm] at this; omega

/-- The rotation map for the quotient graph.
    For real vertices (`origVertex < n`): decode → G.rot → encode.
    For virtual vertices (`origVertex ≥ n`): self-loop. -/
private def quotientRot {n d : ℕ} (G : RegularGraph n d) {m r : ℕ}
    (hr : 0 < r) (hmr : n ≤ m * r)
    (x : Fin m × Fin (d * r)) : Fin m × Fin (d * r) :=
  if h : origVertex x < n then
    qEncode hr hmr (G.rot (⟨origVertex x, h⟩,
      ⟨x.2.val / r, (Nat.div_lt_iff_lt_mul hr).mpr x.2.isLt⟩))
  else
    x

private theorem quotientRot_pos {n d : ℕ} (G : RegularGraph n d) {m r : ℕ}
    (hr : 0 < r) (hmr : n ≤ m * r) (x : Fin m × Fin (d * r))
    (h : origVertex x < n) :
    quotientRot G hr hmr x = qEncode hr hmr (G.rot (⟨origVertex x, h⟩,
      ⟨x.2.val / r, (Nat.div_lt_iff_lt_mul hr).mpr x.2.isLt⟩)) :=
  dif_pos h

private theorem quotientRot_neg {n d : ℕ} (G : RegularGraph n d) {m r : ℕ}
    (hr : 0 < r) (hmr : n ≤ m * r) (x : Fin m × Fin (d * r))
    (h : ¬ origVertex x < n) :
    quotientRot G hr hmr x = x :=
  dif_neg h

private theorem quotientRot_involution {n d : ℕ} (G : RegularGraph n d) {m r : ℕ}
    (hr : 0 < r) (hmr : n ≤ m * r)
    (x : Fin m × Fin (d * r)) :
    quotientRot G hr hmr (quotientRot G hr hmr x) = x := by
  by_cases h : origVertex x < n
  · -- Real vertex: inner call gives qEncode of G.rot result
    rw [quotientRot_pos G hr hmr x h]
    set result := G.rot (⟨origVertex x, h⟩,
      ⟨x.2.val / r, (Nat.div_lt_iff_lt_mul hr).mpr x.2.isLt⟩) with result_def
    -- Encoded result decodes to a real vertex
    have h2 : origVertex (qEncode hr hmr result) < n := by
      rw [origVertex_qEncode]; exact result.1.isLt
    rw [quotientRot_pos G hr hmr (qEncode hr hmr result) h2]
    -- The reconstructed pair fed to G.rot equals result
    have hv : (⟨origVertex (qEncode hr hmr result), h2⟩ : Fin n) = result.1 :=
      Fin.ext (origVertex_qEncode hr hmr result)
    have hp : (⟨(qEncode hr hmr result).2.val / r,
        (Nat.div_lt_iff_lt_mul hr).mpr (qEncode hr hmr result).2.isLt⟩ : Fin d) = result.2 :=
      Fin.ext (port_div_qEncode hr hmr result)
    -- G.rot(result.1, result.2) = G.rot(result) → unfold result → G.rot(G.rot(orig)) = orig
    simp only [hv, hp, Prod.mk.eta]
    rw [result_def, G.rot_involution]
    -- qEncode of original = x (round-trip)
    apply Prod.ext <;> apply Fin.ext <;> simp only [qEncode]
    · exact origVertex_div hr x
    · exact port_recon hr x
  · -- Virtual vertex: self-loop
    rw [quotientRot_neg G hr hmr x h, quotientRot_neg G hr hmr x h]


/-! **Graph Quotient** -/

/-- The quotient graph: given a `d`-regular graph on `n` vertices and a target
    size `m ≤ n`, produces a `(d * ⌈n/m⌉)`-regular multigraph on `m` vertices.

    Each quotient vertex `u ∈ Fin m` represents original vertices in the class
    `{u * r, ..., u * r + r - 1} ∩ {0, ..., n - 1}` where `r = ⌈n/m⌉`.
    When `m ∤ n`, some classes have fewer than `r` real vertices, and excess
    ports act as self-loops.

    Self-loops and multi-edges are allowed
    (which is fine: `RegularGraph` is defined via rotation maps, not simple graphs). -/
def RegularGraph.quotient {n d : ℕ} (G : RegularGraph n d)
    (m : ℕ) (hm : 0 < m) (hmn : m ≤ n) :
    RegularGraph m (d * ceilDiv n m) where
  rot := quotientRot G (ceilDiv_pos hm hmn) (le_mul_ceilDiv hm)
  rot_involution := quotientRot_involution G (ceilDiv_pos hm hmn) (le_mul_ceilDiv hm)

/-- The spectral gap can only decrease under quotient: λ(G/∼) ≤ λ(G).

    Proof sketch: Lift f : Fin m → ℝ to f̃ : Fin n → ℝ constant on classes
    (f̃(v) = f(v/r)). Then W_quotient f = Compress(W_G f̃) where Compress averages
    within each class. By Jensen's inequality on the per-class averaging,
    ‖(W_quotient - P) f‖² ≤ (1/r) ‖(W_G - P) f̃‖² ≤ (spectralGap G)² · ‖f‖². -/
theorem spectralGap_quotient {n d : ℕ} (G : RegularGraph n d)
    (m : ℕ) (hm : 0 < m) (hmn : m ≤ n) :
    spectralGap (G.quotient m hm hmn) ≤ spectralGap G := by
  sorry
