/-
  Benchmark: break down where time goes in #eval
-/

import CertCheck
import AKS.Cert.Read

def rotData1728 : String := bin_base85% "data/1728/rot_map.b85"
def certData1728 : String := bin_base85% "data/1728/cert_z.b85"

-- Just force the string to exist
#eval rotData1728.length
#eval certData1728.length
