module
/-
  Profile just the certificate_passes native_decide for n=1728.
  This isolates whether involution checking or PSD checking is the bottleneck.
-/

public import Random.Cert
public import Random.Bridge.Read

@[expose] public section


namespace ProfilePSD

def rotData : String := ascii_file% "data/1728/rot_map.b85"
def certData : String := ascii_file% "data/1728/cert_z.b85"

theorem certificate_passes :
    checkCertificateSlow rotData certData 1728 12 792 9 2 = true := by
  native_decide

end ProfilePSD

end
