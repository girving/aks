/-
  Profile checkPSDCertificate via `decide +kernel` instead of `native_decide`.
  This tests whether the kernel evaluator is faster than the native_decide pipeline.
-/

import CertCheck
import AKS.Cert.Read

namespace ProfileDecideKernel

def rotData : String := bin_base85% "data/1728/rot_map.bin"
def certData : String := bin_base85% "data/1728/cert_z.bin"

theorem psd_passes :
    checkPSDCertificate rotData.toUTF8 certData.toUTF8 1728 12 792 9 2 = true := by
  decide +kernel

end ProfileDecideKernel
