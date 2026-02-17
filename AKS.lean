/-
  # AKS Sorting Network — Root Module

  Imports all modules. For the main results, see:
  • `AKS/AKSNetwork.lean` — parameterized construction and `zigzag_implies_aks_network`
  • `AKS/Main.lean` — concrete instantiation with zig-zag expander family
-/

import AKS.ComparatorNetwork
import AKS.Depth
import AKS.Fin
import AKS.AKSNetwork
import AKS.Nearsort
import AKS.Halver
import AKS.Halver.Tanner
import AKS.Halver.ExpanderToHalver
import AKS.HalverToNearsort
import AKS.TreeSorting
import AKS.TreeDamageStability
import AKS.TreeDamageImprovement
import AKS.Graph.Regular
import AKS.Graph.Square
import AKS.Graph.Complete
import AKS.Mixing
import AKS.ZigZag.Operators
import AKS.ZigZag.Spectral
import AKS.ZigZag.RVWInequality
import AKS.ZigZag.RVWBound
import AKS.ZigZag
import AKS.Random
import AKS.Certificate
import AKS.WalkBound
import AKS.DiagDominant
import AKS.SpectralMatrix
import AKS.CertificateBridge
import AKS.NpyReader
import AKS.Random16
import AKS.Random1728
import AKS.Random20736
import AKS.Main
