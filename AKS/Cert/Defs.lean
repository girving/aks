/-
  # Pure functional definitions for certificate bridge proofs

  These definitions mirror the imperative checkers in `CertCheck.lean` but use
  pure recursive functions amenable to formal reasoning. They are used only in
  bridge proofs (`Bridge.lean`, `ColumnNormBridge.lean`), never at runtime.

  Shared helpers (`sumTo`, `certEntryInt`, `intAbs`, `zColNormPure`) live in
  `CertCheck.lean` since the runtime `checkColumnNormBound` also uses them.
  This file adds only the proof-only definitions on top.

  Imports only `CertCheck` (no Mathlib) so it can be part of the precompiled
  dependency chain without pulling in heavy imports.
-/

import CertCheck


/-! **Pure recursive helpers for PSD diagonal dominance** -/

/-- Unnormalized adjacency-vector product: `(B·z)[v] = ∑_{p<d} z[neighbor(v,p) % n]`. -/
def adjMulPure (rotBytes : ByteArray) (z : Nat → Int) (n d v : Nat) : Int :=
  sumTo (fun p => z (decodeBase85Nat rotBytes (2 * (v * d + p)) % n)) d

/-- `P = M · Z` entry at `(k, j)` in integers. -/
def pEntryPure (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (k j : Nat) : Int :=
  let zj : Nat → Int := fun i => certEntryInt certBytes i j
  let b2zj_k := adjMulPure rotBytes (fun v => adjMulPure rotBytes zj n d v) n d k
  let colSum := sumTo (fun l => certEntryInt certBytes l j) n
  c₁ * certEntryInt certBytes k j - c₂ * b2zj_k + c₃ * colSum

/-- `K = Zᵀ · M · Z` entry at `(i, j)` in integers. -/
def kEntryPure (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (i j : Nat) : Int :=
  sumTo (fun k => certEntryInt certBytes k i *
    pEntryPure rotBytes certBytes n d c₁ c₂ c₃ k j) n

/-- Check diagonal dominance for row `i` (pure functional). -/
def checkRowDomPure (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (i : Nat) : Bool :=
  let diag := kEntryPure rotBytes certBytes n d c₁ c₂ c₃ i i
  let offDiag := sumTo (fun j =>
    if j == i then 0
    else let v := kEntryPure rotBytes certBytes n d c₁ c₂ c₃ i j
         if v >= 0 then v else -v) n
  decide (offDiag < diag)

/-- Check diagonal dominance for all rows `0..m-1` (pure functional). -/
def checkAllRowsDomPure (rotBytes certBytes : ByteArray) (n d : Nat)
    (c₁ c₂ c₃ : Int) : Nat → Bool
  | 0 => true
  | m + 1 => checkAllRowsDomPure rotBytes certBytes n d c₁ c₂ c₃ m &&
              checkRowDomPure rotBytes certBytes n d c₁ c₂ c₃ m


/-! **Pure recursive helpers for column-norm bound** -/

/-- Column sum of certificate column `j`: `∑_{l<n} Z[l,j]`.
    Pre-computed and threaded through `epsMaxCol` to avoid O(n) recomputation
    per `pEntryPure` call, keeping total complexity O(n²d²) instead of O(n²d²+n³). -/
def colSumZ (certBytes : ByteArray) (n j : Nat) : Int :=
  sumTo (fun l ↦ certEntryInt certBytes l j) n

/-- Maximum `|P[k,j]|` for `k < bound`, with pre-computed column sum.
    The inlined P entry computation equals `pEntryPure k j` when
    `colSum = colSumZ certBytes n j`. -/
def epsMaxCol (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int)
    (j : Nat) (colSum : Int) : Nat → Int
  | 0 => 0
  | k + 1 =>
    let zj : Nat → Int := fun i ↦ certEntryInt certBytes i j
    let b2zj_k := adjMulPure rotBytes (fun v ↦ adjMulPure rotBytes zj n d v) n d k
    let pij := c₁ * certEntryInt certBytes k j - c₂ * b2zj_k + c₃ * colSum
    max (epsMaxCol rotBytes certBytes n d c₁ c₂ c₃ j colSum k) (intAbs pij)

/-- Maximum off-diagonal `|P[k,j]|` over `k < j`, for all `j < bound`. -/
def epsMaxVal (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int) : Nat → Int
  | 0 => 0
  | j + 1 =>
    max (epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ j)
        (epsMaxCol rotBytes certBytes n d c₁ c₂ c₃ j (colSumZ certBytes n j) j)

/-- Minimum diagonal `P[j,j]` over `j < bound`. Returns `0` for `bound = 0`. -/
def minDiagVal (rotBytes certBytes : ByteArray) (n d : Nat) (c₁ c₂ c₃ : Int) : Nat → Int
  | 0 => 0
  | 1 => pEntryPure rotBytes certBytes n d c₁ c₂ c₃ 0 0
  | m + 2 => min (minDiagVal rotBytes certBytes n d c₁ c₂ c₃ (m + 1))
                  (pEntryPure rotBytes certBytes n d c₁ c₂ c₃ (m + 1) (m + 1))

/-- Pure recursive version of `checkColumnNormBound` for formal reasoning.
    Uses `epsMaxVal`/`minDiagVal` (pure recursive) instead of imperative `checkPSDColumns`.
    Equivalent to the imperative version but trivially amenable to spec proofs. -/
def checkColumnNormBoundPure (rotBytes certBytes : ByteArray) (n d : Nat)
    (c₁ c₂ c₃ : Int) : Bool :=
  if n == 0 then false
  else
    let ε := epsMaxVal rotBytes certBytes n d c₁ c₂ c₃ n
    let δ := minDiagVal rotBytes certBytes n d c₁ c₂ c₃ n
    checkPerRow certBytes n ε (δ + ε) n 0 0
