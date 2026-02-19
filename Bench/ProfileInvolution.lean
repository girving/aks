/-
  Profile just the rot_involution native_decide for n=1728.
  This isolates whether involution checking or PSD checking is the bottleneck.
-/

import AKS.Cert.Bridge
import AKS.Cert.Read

namespace ProfileInvolution

def rotData : String := bin_base85% "data/1728/rot_map.b85"

def graph : RegularGraph 1728 12 where
  rot := rotFun rotData 1728 12 (by decide) (by decide)
  rot_involution := by native_decide

end ProfileInvolution
