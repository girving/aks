module
/-
  Benchmark: break down where time goes in #eval
-/

public import Random.Cert
public import Random.Bridge.Read

@[expose] public section


def rotData1728 : String := ascii_file% "data/1728/rot_map.b85"
def certData1728 : String := ascii_file% "data/1728/cert_z.b85"

-- Just force the string to exist
#eval rotData1728.length
#eval certData1728.length

end
