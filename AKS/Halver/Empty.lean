module
/-
  # Empty Network is a Perfect Halver

  The empty comparator network on 0 wires is trivially an ε-halver
  for any ε: with 0 wires, `0/2 = 0` makes all `∀ k ≤ 0` conditions vacuous.
-/

public import AKS.Halver.Defs

@[expose] public section


/-- The empty network on 0 wires is an ε-halver for any ε. -/
theorem emptyNet_isEpsilonHalver (ε : ℝ) :
    IsEpsilonHalver (⟨[]⟩ : ComparatorNetwork 0) ε := by
  intro v
  constructor
  · intro k hk
    simp only [Fintype.card_fin, show 0 / 2 = 0 from rfl] at hk
    have : k = 0 := by omega
    subst this; simp
  · intro k hk
    simp only [Fintype.card_orderDual, Fintype.card_fin, show 0 / 2 = 0 from rfl] at hk
    have : k = 0 := by omega
    subst this; simp

/-- The empty network on 0 wires has depth 0. -/
theorem emptyNet_depth : (⟨[]⟩ : ComparatorNetwork 0).depth = 0 := by
  simp [ComparatorNetwork.depth]

end
