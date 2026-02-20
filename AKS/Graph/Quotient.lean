/-
  # Graph Quotient (Vertex Merging)

  Given a `d`-regular graph on `n * r` vertices, merge every `r` consecutive
  vertices into one, yielding a `(d * r)`-regular multigraph on `n` vertices.

  This is the key construction for building expander families at arbitrary
  sizes from the zig-zag family (which only produces graphs at sizes D^(4(k+1))).
  Given a zig-zag family graph at size M = n * r, the quotient produces an
  expander on n vertices with degree d * r (at most D⁶ when r ≤ D⁴).

  The spectral gap can only decrease: `spectralGap_quotient : spectralGap G.quotient ≤ spectralGap G`.
-/

import AKS.Graph.Regular

open Matrix BigOperators Finset


/-! **Nat-Level Encode/Decode Helpers** -/

/-- Dividing `a * r + b` by `r` gives `a`, when `b < r`. -/
private theorem encode_div {r : ℕ} (a b : ℕ) (hr : 0 < r) (hb : b < r) :
    (a * r + b) / r = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hr, Nat.div_eq_of_lt hb]; omega

/-- Taking `a * r + b` mod `r` gives `b`, when `b < r`. -/
private theorem encode_mod {r : ℕ} (a b : ℕ) (hb : b < r) :
    (a * r + b) % r = b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]


/-! **Graph Quotient** -/

/-- Decode a quotient vertex-port pair into the original graph's vertex-port pair.
    Port j ∈ Fin (d * r) encodes (original port i, class member p) via j = i * r + p.
    Vertex u ∈ Fin n encodes the equivalence class; the original vertex is u * r + p. -/
private def qDecode {n r d : ℕ} (hr : 0 < r)
    (x : Fin n × Fin (d * r)) : Fin (n * r) × Fin d :=
  (⟨x.1.val * r + x.2.val % r, Fin.pair_lt x.1 ⟨x.2.val % r, Nat.mod_lt _ hr⟩⟩,
   ⟨x.2.val / r, (Nat.div_lt_iff_lt_mul hr).mpr x.2.isLt⟩)

/-- Encode an original graph's vertex-port pair into the quotient's vertex-port pair.
    Vertex v ∈ Fin (n * r) maps to quotient vertex v / r, with class member v % r.
    Port q ∈ Fin d and class member v % r encode as q * r + (v % r). -/
private def qEncode {n r d : ℕ} (hr : 0 < r)
    (x : Fin (n * r) × Fin d) : Fin n × Fin (d * r) :=
  (⟨x.1.val / r, (Nat.div_lt_iff_lt_mul hr).mpr x.1.isLt⟩,
   ⟨x.2.val * r + x.1.val % r, Fin.pair_lt x.2 ⟨x.1.val % r, Nat.mod_lt _ hr⟩⟩)

private theorem qDecode_qEncode {n r d : ℕ} (hr : 0 < r)
    (x : Fin (n * r) × Fin d) : qDecode hr (qEncode hr x) = x := by
  obtain ⟨v, q⟩ := x
  apply Prod.ext <;> apply Fin.ext <;> simp only [qDecode, qEncode]
  · -- (v / r) * r + (q * r + v % r) % r = v
    rw [encode_mod q.val (v.val % r) (Nat.mod_lt _ hr)]
    have := Nat.div_add_mod v.val r; rw [Nat.mul_comm] at this; omega
  · -- (q * r + v % r) / r = q
    exact encode_div q.val (v.val % r) hr (Nat.mod_lt _ hr)

private theorem qEncode_qDecode {n r d : ℕ} (hr : 0 < r)
    (x : Fin n × Fin (d * r)) : qEncode hr (qDecode hr x) = x := by
  obtain ⟨u, j⟩ := x
  apply Prod.ext <;> apply Fin.ext <;> simp only [qDecode, qEncode]
  · -- (u * r + j % r) / r = u
    exact encode_div u.val (j.val % r) hr (Nat.mod_lt _ hr)
  · -- (j / r) * r + (u * r + j % r) % r = j
    rw [encode_mod u.val (j.val % r) (Nat.mod_lt _ hr)]
    have := Nat.div_add_mod j.val r; rw [Nat.mul_comm] at this; omega

/-- The rotation map for the quotient graph: decode → G.rot → encode. -/
private def quotient_rot {n r d : ℕ} (G : RegularGraph (n * r) d)
    (x : Fin n × Fin (d * r)) : Fin n × Fin (d * r) :=
  have hr : 0 < r := Nat.pos_of_ne_zero (fun h => by subst h; exact absurd x.2.isLt (by simp))
  qEncode hr (G.rot (qDecode hr x))

private theorem quotient_rot_involution {n r d : ℕ} (G : RegularGraph (n * r) d)
    (x : Fin n × Fin (d * r)) : quotient_rot G (quotient_rot G x) = x := by
  simp only [quotient_rot, qDecode_qEncode, G.rot_involution, qEncode_qDecode]

/-- The quotient graph: merge every `r` consecutive vertices into one.
    Given a `d`-regular graph on `n * r` vertices, produces a `(d * r)`-regular
    multigraph on `n` vertices. Self-loops and multi-edges are allowed
    (which is fine: `RegularGraph` is defined via rotation maps, not simple graphs). -/
def RegularGraph.quotient {n r d : ℕ} (G : RegularGraph (n * r) d) :
    RegularGraph n (d * r) where
  rot := quotient_rot G
  rot_involution := quotient_rot_involution G

/-- The spectral gap can only decrease under quotient: λ(G/r) ≤ λ(G).

    Proof sketch: Lift f : Fin n → ℝ to f̃ : Fin (n*r) → ℝ constant on classes
    (f̃(v) = f(v/r)). Then W_quotient f = Compress(W_G f̃) where Compress averages
    within each class. By Jensen's inequality on the per-class averaging,
    ‖(W_quotient - P) f‖² ≤ (1/r) ‖(W_G - P) f̃‖² ≤ (spectralGap G)² · ‖f‖². -/
theorem spectralGap_quotient {n r d : ℕ} (G : RegularGraph (n * r) d) :
    spectralGap G.quotient ≤ spectralGap G := by
  sorry
