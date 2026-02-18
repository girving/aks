/-
  Test: new checkCertificateSlow (involution + PSD + columnNormBound) via native_decide.
-/
import AKS.Certificate
import AKS.NpyReader

#eval ensureCertificateData 16 4
#eval ensureCertificateData 1728 12

def rotData16t : String := bin_base85% "data/16/rot_map.bin"
def certData16t : String := bin_base85% "data/16/cert_z.bin"
def rotData1728t : String := bin_base85% "data/1728/rot_map.bin"
def certData1728t : String := bin_base85% "data/1728/cert_z.bin"

-- n=16
theorem cert16 : checkCertificateSlow rotData16t certData16t 16 4 216 9 1 = true := by
  native_decide

-- n=1728
theorem cert1728 : checkCertificateSlow rotData1728t certData1728t 1728 12 792 9 2 = true := by
  native_decide
