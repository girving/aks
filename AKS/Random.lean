/-
  # Base Expander for the Zig-Zag Construction

  Imports the concrete base expander graph. Change the import below to
  switch graph sizes:
  - `Random16` — 4-regular on 16 vertices (fast, for development)
  - `Random1728` — 12-regular on 1728 vertices (medium test)
  - `Random20736` — 12-regular on 20736 = 12⁴ vertices (production)

  Data files live in `data/{n}/` (binary, not committed). Regenerate with:
    `cargo run --release -p compute-certificate -- <n> <d> <seed> <scale_exp>`
-/

import AKS.Random20736
