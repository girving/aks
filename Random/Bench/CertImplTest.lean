module
/-
  Test: new checkCertificateSlow (involution + PSD + columnNormBound) via native_decide.
-/
public import Random.Cert
public import Random.Bridge.Read

@[expose] public section


#eval ensureCertificateData 16 4
#eval ensureCertificateData 1728 12

def rotData16t : String := ascii_file% "data/16/rot_map.b85"
def certData16t : String := ascii_file% "data/16/cert_z.b85"
def rotData1728t : String := ascii_file% "data/1728/rot_map.b85"
def certData1728t : String := ascii_file% "data/1728/cert_z.b85"

-- n=16
theorem cert16 : checkCertificateSlow rotData16t certData16t 16 4 216 9 1 = true := by
  native_decide

-- n=1728
theorem cert1728 : checkCertificateSlow rotData1728t certData1728t 1728 12 792 9 2 = true := by
  native_decide

end
