module
/-
  Profile just checkPSDCertificate (not checkInvolution) via native_decide.
-/

public import Random.Cert
public import Random.Bridge.Read

@[expose] public section


namespace ProfilePSDOnly

def rotData : String := ascii_file% "data/1728/rot_map.b85"
def certData : String := ascii_file% "data/1728/cert_z.b85"

theorem psd_passes :
    checkPSDCertificate rotData (b85entry certData) 1728 12 792 9 2 = true := by
  native_decide

end ProfilePSDOnly

end
