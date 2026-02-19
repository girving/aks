/-
  Profile just checkPSDCertificate (not checkInvolution) via native_decide.
-/

import CertCheck
import AKS.Cert.Read

namespace ProfilePSDOnly

def rotData : String := bin_base85% "data/1728/rot_map.b85"
def certData : String := bin_base85% "data/1728/cert_z.b85"

theorem psd_passes :
    checkPSDCertificate rotData.toUTF8 certData.toUTF8 1728 12 792 9 2 = true := by
  native_decide

end ProfilePSDOnly
