/-
  Benchmark: break down where time goes in #eval
-/

import AKS.Certificate
import AKS.NpyReader

def rotData1728 : String := bin_base85% "data/1728/rot_map.bin"
def certData1728 : String := bin_base85% "data/1728/cert_z.bin"

-- Just force the string to exist
#eval rotData1728.length
#eval certData1728.length
