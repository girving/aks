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
import AKS.Halver
import AKS.TreeSorting
import AKS.RegularGraph
import AKS.Square
import AKS.CompleteGraph
import AKS.Mixing
import AKS.ZigZagOperators
import AKS.ZigZagSpectral
import AKS.RVWBound
import AKS.ZigZag
import AKS.Random
import AKS.Certificate
import AKS.WalkBound
import AKS.CertificateBridge
import AKS.NpyReader
import AKS.Main
