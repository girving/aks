/-
  # AKS Sorting Network — Root Module

  Imports all modules. For the main results, see:
  • `AKS/Seiferas.lean` — Seiferas (2009) separator-based O(n log n) sorting networks
-/

import AKS.Sort.Defs
import AKS.Sort.Monotone
import AKS.Sort.ZeroOne
import AKS.Sort.Depth
import AKS.Sort.Shrink
import AKS.Sort.Perm
import AKS.Sort.Displaced
import AKS.Sort.Bipartite
import AKS.Bitonic.Defs
import AKS.Bitonic.Depth
import AKS.Bitonic.LayerExec
import AKS.Bitonic.Bitonic01
import AKS.Bitonic.CompareLayer
import AKS.Bitonic.Correctness
import AKS.Bitonic.Shrink
import AKS.Misc.Fin
import AKS.Misc.Floor
import AKS.Halver.Defs
import AKS.Halver.Empty
import AKS.Halver.Mono
import AKS.Halver.Tanner
import AKS.Halver.FromExpander
import AKS.Konig.Defs
import AKS.Konig.Hall
import AKS.Konig.Coloring
import AKS.Konig.ContractedBipartite
import AKS.Konig.Matching
import AKS.Separator.Defs
import AKS.Separator.Family
import AKS.Separator.FromHalverDefs
import AKS.Separator.FromHalver
import AKS.Separator.General
import AKS.Separator.SepProof
import AKS.Separator.Axioms
import AKS.Halver.Quotient
import AKS.Halver.General
import AKS.Halver.Axioms
import AKS.Bags.Params
import AKS.Bags.Defs
import AKS.Bags.Network
import AKS.Bags.SplitCard
import AKS.Bags.Sizes
import AKS.Bags.Filter
import AKS.Bags.SepBridge
import AKS.Bags.Subtree
import AKS.Bags.Source3
import AKS.Bags.Strange
import AKS.Bags.Sorts
import AKS.Bags.Depth
import AKS.MGG.Defs
import AKS.MGG.DFT
import AKS.MGG.WalkExpansion
import AKS.MGG.YoungDefs
import AKS.MGG.Young
import AKS.MGG.YoungAssembly
import AKS.MGG.Spectral
import AKS.MGG.Axioms
import AKS.Graph.Regular
import AKS.Graph.Square
import AKS.Graph.Complete
import AKS.Graph.Graph
import AKS.Graph.Walk
import AKS.Graph.Contract
import AKS.Graph.Kronecker
import AKS.Halver.Mixing
import AKS.ZigZag.Operators
import AKS.ZigZag.Spectral
import AKS.ZigZag.RVWInequality
import AKS.ZigZag.RVWBound
import AKS.ZigZag.Expanders
import AKS.Seiferas
