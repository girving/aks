/-
  # AKS Sorting Network — Root Module

  Imports all modules. For the main results, see:
  • `AKS/AKSNetwork.lean` — parameterized construction and `zigzag_implies_aks_network`
  • `AKS/Main.lean` — concrete instantiation with zig-zag expander family
-/

import AKS.Sort.Defs
import AKS.Sort.Monotone
import AKS.Sort.ZeroOne
import AKS.Sort.Depth
import AKS.Misc.Fin
import AKS.Tree.AKSNetwork
import AKS.Nearsort.Defs
import AKS.Halver.Defs
import AKS.Halver.Tanner
import AKS.Halver.ExpanderToHalver
import AKS.Nearsort.HalverToNearsort
import AKS.Tree.Sorting
import AKS.Tree.DamageStability
import AKS.Tree.DamageImprovement
import AKS.Graph.Regular
import AKS.Graph.Square
import AKS.Graph.Complete
import AKS.Halver.Mixing
import AKS.ZigZag.Operators
import AKS.ZigZag.Spectral
import AKS.ZigZag.RVWInequality
import AKS.ZigZag.RVWBound
import AKS.ZigZag.Expanders
import AKS.Cert.Defs
import AKS.Cert.Read
import AKS.Cert.WalkBound
import AKS.Cert.DiagDominant
import AKS.Cert.SpectralMatrix
import AKS.Cert.Bridge
import AKS.Cert.ColumnNormBridge
import AKS.Misc.ForLoop
import AKS.Random.Random16
import AKS.Random.Random1728
import AKS.Random.Random20736
import AKS.Main
