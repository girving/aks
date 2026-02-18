/-
  Profile just checkPSDCertificate (not checkInvolution) via native_decide.
-/

import AKS.Certificate
import AKS.NpyReader

namespace ProfilePSDOnly

def rotData : String := bin_base85% "data/1728/rot_map.bin"
def certData : String := bin_base85% "data/1728/cert_z.bin"

theorem psd_passes :
    checkPSDCertificate rotData.toUTF8 certData.toUTF8 1728 12 792 9 2 = true := by
  native_decide

end ProfilePSDOnly
