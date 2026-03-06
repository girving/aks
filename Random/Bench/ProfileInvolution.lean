module
/-
  Profile just the rot_involution native_decide for n=1728.
  This isolates whether involution checking or PSD checking is the bottleneck.
-/

public import Random.Bridge.Bridge
public import Random.Bridge.Read

@[expose] public section


namespace ProfileInvolution

def rotData : String := ascii_file% "data/1728/rot_map.b85"

theorem involution_check : checkInvolutionSpec rotData 1728 12 = true := by
  native_decide

def graph : RegularGraph 1728 12 where
  rot := rotFun rotData 1728 12 (by decide) (by decide)
  rot_involution :=
    checkInvolutionSpec_implies_rotFun_involution rotData 1728 12 (by decide) (by decide)
      involution_check

end ProfileInvolution

end
