/-
  Profile just the certificate_passes native_decide for n=1728.
  This isolates whether involution checking or PSD checking is the bottleneck.
-/

import CertCheck
import AKS.Cert.Read

namespace ProfilePSD

def rotData : String := bin_base85% "data/1728/rot_map.bin"
def certData : String := bin_base85% "data/1728/cert_z.bin"

theorem certificate_passes :
    checkCertificateSlow rotData certData 1728 12 792 9 2 = true := by
  native_decide

end ProfilePSD
