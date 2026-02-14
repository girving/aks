/-
  # AKS Main Assembly

  Assembles the concrete zig-zag expander family with the parameterized
  AKS construction to produce the final unparameterized results.

  The key chain:
  1. `explicit_expanders_exist_zigzag` (ZigZag.lean): concrete expander family
  2. `zigzag_implies_aks_network` (AKSNetwork.lean): expander family → sorting networks
  3. This file: plug them together

  Currently a stub — requires `explicit_expanders_exist_zigzag` to be proved
  and the spectral gap to be < 1/2 (needs a base expander with sufficiently
  small gap, or larger degree D).
-/

import AKS.AKSNetwork
import AKS.ZigZag
