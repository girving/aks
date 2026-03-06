module
/-
  # Prototype: lazy-loaded certificate data via cachedString

  Tests that `cachedString` (pure @[extern] with lazy mmap) avoids
  embedding certificate data in the .ir file while still supporting
  `native_decide` proofs.

  The key idea: `rotData := cachedString "path"` generates tiny IR
  (just a function call with a small string argument), instead of
  embedding the entire certificate file as a string literal.
-/

public import Random.Bridge.Bridge
public import Random.Bridge.Read

namespace TestOpaqueData

#eval ensureCertificateData 16 4

def rotData : String := cachedString "data/16/rot_map.b85"
def certData : String := cachedString "data/16/cert_z.b85"

theorem involution_check : checkInvolutionSpec rotData 16 4 = true := by
  native_decide

public def graph : RegularGraph 16 4 where
  rot := rotFun rotData 16 4 (by decide) (by decide)
  rot_involution :=
    checkInvolutionSpec_implies_rotFun_involution rotData 16 4 (by decide) (by decide)
      involution_check

theorem certificate_passes :
    checkCertificate rotData certData 16 4 216 9 1 = true := by
  native_decide

public theorem gap : spectralGap graph ≤ 5 / (1 * 4) := by
  have h : checkCertificateSlow rotData certData 16 4 216 9 1 = true := by
    rw [← checkCertificate_eq_slow]; exact certificate_passes
  exact_mod_cast certificate_bridge_b85 16 4 (by decide) (by decide) graph
    rotData certData 216 9 1 h involution_check
    5 1 (by decide) (by decide) (by decide) (by decide) (fun _ => rfl)

end TestOpaqueData
