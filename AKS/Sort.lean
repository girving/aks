/-
  # Sorting Networks

  Re-exports all sorting network infrastructure:
  • `Sort/Defs.lean` — `Comparator`, `ComparatorNetwork`, `exec`, `shiftEmbed`, injectivity
  • `Sort/Monotone.lean` — monotonicity preservation, `IsSortingNetwork`
  • `Sort/ZeroOne.lean` — the 0-1 principle
  • `Sort/Depth.lean` — network depth and parallel decomposition
-/

import AKS.Sort.Defs
import AKS.Sort.Monotone
import AKS.Sort.ZeroOne
import AKS.Sort.Depth
