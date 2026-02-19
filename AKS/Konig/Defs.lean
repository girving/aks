/-
  # König's Edge Coloring — Definitions

  Bipartite multigraph structures for König's edge coloring theorem.
  Used to prove depth bounds for expander-based halver networks.

  Main definitions:
  • `RegBipartite m d` — d-regular bipartite multigraph (m top, m bottom vertices)
  • `PerfectMatching`  — port selection giving injective bottom assignment
  • `RegBipartite.ofRegularGraph` — convert a `RegularGraph` to `RegBipartite`
-/

import AKS.Graph.Regular

open Finset BigOperators


/-! **Regular Bipartite Multigraph** -/

/-- A d-regular bipartite multigraph: m top vertices, m bottom vertices,
    d ports per top vertex, and each bottom vertex has exactly d incoming edges.

    The `edges` function maps each (top vertex, port) pair to a bottom vertex.
    Top-regularity (degree d) is structural. Bottom-regularity is an axiom. -/
structure RegBipartite (m d : ℕ) where
  edges : Fin m → Fin d → Fin m
  bot_regular : ∀ u : Fin m,
    ((univ ×ˢ univ).filter (fun vp : Fin m × Fin d ↦ edges vp.1 vp.2 = u)).card = d


/-! **Perfect Matching** -/

/-- A perfect matching in a `RegBipartite`: a port selection for each top vertex
    such that the induced bottom assignment is injective (no two top vertices
    share a bottom vertex). -/
structure PerfectMatching {m d : ℕ} (B : RegBipartite m d) where
  portOf : Fin m → Fin d
  injective : Function.Injective (fun v ↦ B.edges v (portOf v))


/-! **Conversion from RegularGraph** -/

/-- The rotation map involution implies: for every bottom vertex u, the set
    of (v, p) with `G.neighbor v p = u` has exactly d elements. -/
theorem RegularGraph.neighbor_fiber_card {m d : ℕ} (G : RegularGraph m d) (u : Fin m) :
    ((univ ×ˢ univ).filter (fun vp : Fin m × Fin d ↦ G.neighbor vp.1 vp.2 = u)).card = d := by
  -- Bijection: q ↦ G.rot (u, q) maps {q : Fin d} → fiber {(v,p) | neighbor v p = u}
  -- with inverse (v, p) ↦ G.reversePort v p
  have key : ((univ ×ˢ univ).filter
      (fun vp : Fin m × Fin d ↦ G.neighbor vp.1 vp.2 = u)).card =
      (univ : Finset (Fin d)).card :=
    Finset.card_nbij' (fun vp ↦ G.reversePort vp.1 vp.2)
      (fun q ↦ G.rot (u, q))
      -- Forward: fiber → Fin d (reversePort lands in univ)
      (fun _ h ↦ Finset.mem_coe.mpr (mem_univ _))
      -- Backward: Fin d → fiber (rot lands in the fiber)
      (by
        intro q hq
        refine Finset.mem_coe.mpr (mem_filter.mpr ⟨Finset.mem_product.mpr ⟨mem_univ _, mem_univ _⟩, ?_⟩)
        show G.neighbor (G.rot (u, q)).1 (G.rot (u, q)).2 = u
        unfold RegularGraph.neighbor
        rw [Prod.mk.eta, G.rot_involution])
      -- Left inverse: rot ∘ (u, reversePort) recovers the pair
      (by
        intro ⟨v, p⟩ hvp
        have hvp' := (mem_filter.mp (Finset.mem_coe.mp hvp)).2
        -- hvp' : G.neighbor (v, p).1 (v, p).2 = u, i.e. (G.rot (v, p)).1 = u
        show G.rot (u, G.reversePort (v, p).1 (v, p).2) = (v, p)
        simp only [RegularGraph.reversePort]
        -- Goal: G.rot (u, (G.rot (v, p)).2) = (v, p)
        have hfst : (G.rot (v, p)).1 = u := by
          exact hvp'
        conv_lhs => rw [show (u, (G.rot (v, p)).2) = G.rot (v, p) from
          Prod.ext hfst.symm rfl]
        exact G.rot_involution (v, p))
      -- Right inverse: reversePort ∘ rot = projection
      (by
        intro q _
        show G.reversePort (G.rot (u, q)).1 (G.rot (u, q)).2 = q
        simp only [RegularGraph.reversePort, Prod.mk.eta]
        exact congr_arg Prod.snd (G.rot_involution (u, q)))
  rw [key, card_univ, Fintype.card_fin]

/-- Convert a `RegularGraph` to a `RegBipartite`. The edges function is
    `G.neighbor` and bottom-regularity follows from the rotation involution. -/
def RegBipartite.ofRegularGraph {m d : ℕ} (G : RegularGraph m d) : RegBipartite m d where
  edges v p := G.neighbor v p
  bot_regular := G.neighbor_fiber_card
