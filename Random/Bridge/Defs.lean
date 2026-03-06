module
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

public import Random.Cert

@[expose] public section


/-! **Valid partition predicate** -/

/-- A valid partition covers every column in `[0, n)`. -/
def ValidPartition {n : Nat} (partition : Array (Array (Fin n))) : Prop :=
  ∀ j : Fin n, ∃ ci, ci < partition.size ∧ j ∈ partition[ci]!.toList

/-! **Pure recursive helpers for PSD diagonal dominance** -/

/-- Unnormalized adjacency-vector product: `(B·z)[v] = ∑_{p<d} z[neighbor(v,p) % n]`. -/
def adjMulPure (rotBytes : String) (z : Nat → Int) (n d v : Nat) : Int :=
  sumTo (fun p => z (decodeBase85Nat rotBytes (2 * (v * d + p)) % n)) d

/-- `P = M · Z` entry at `(k, j)` in integers. -/
def pEntryPure (rotBytes : String) (entry : Nat → Nat → Int) (n d : Nat) (c₁ c₂ c₃ : Int)
    (k j : Nat) : Int :=
  let zj : Nat → Int := fun i => certEntryInt entry i j
  let b2zj_k := adjMulPure rotBytes (fun v => adjMulPure rotBytes zj n d v) n d k
  let colSum := sumTo (fun l => certEntryInt entry l j) n
  c₁ * certEntryInt entry k j - c₂ * b2zj_k + c₃ * colSum

/-- `K = Zᵀ · M · Z` entry at `(i, j)` in integers. -/
def kEntryPure (rotBytes : String) (entry : Nat → Nat → Int) (n d : Nat) (c₁ c₂ c₃ : Int)
    (i j : Nat) : Int :=
  sumTo (fun k => certEntryInt entry k i *
    pEntryPure rotBytes entry n d c₁ c₂ c₃ k j) n

/-- Check diagonal dominance for row `i` (pure functional). -/
def checkRowDomPure (rotBytes : String) (entry : Nat → Nat → Int) (n d : Nat) (c₁ c₂ c₃ : Int)
    (i : Nat) : Bool :=
  let diag := kEntryPure rotBytes entry n d c₁ c₂ c₃ i i
  let offDiag := sumTo (fun j =>
    if j == i then 0
    else let v := kEntryPure rotBytes entry n d c₁ c₂ c₃ i j
         if v >= 0 then v else -v) n
  decide (offDiag < diag)

/-- Check diagonal dominance for all rows `0..m-1` (pure functional). -/
def checkAllRowsDomPure (rotBytes : String) (entry : Nat → Nat → Int) (n d : Nat)
    (c₁ c₂ c₃ : Int) : Nat → Bool
  | 0 => true
  | m + 1 => checkAllRowsDomPure rotBytes entry n d c₁ c₂ c₃ m &&
              checkRowDomPure rotBytes entry n d c₁ c₂ c₃ m


/-! **Pure recursive helpers for column-norm bound** -/

/-- Column sum of certificate column `j`: `∑_{l<n} Z[l,j]`.
    Pre-computed and threaded through `epsMaxCol` to avoid O(n) recomputation
    per `pEntryPure` call, keeping total complexity O(n²d²) instead of O(n²d²+n³). -/
def colSumZ (entry : Nat → Nat → Int) (n j : Nat) : Int :=
  sumTo (fun l ↦ certEntryInt entry l j) n

/-- Maximum `|P[k,j]|` for `k < bound`, with pre-computed column sum.
    The inlined P entry computation equals `pEntryPure k j` when
    `colSum = colSumZ entry n j`. -/
def epsMaxCol (rotBytes : String) (entry : Nat → Nat → Int) (n d : Nat) (c₁ c₂ c₃ : Int)
    (j : Nat) (colSum : Int) : Nat → Int
  | 0 => 0
  | k + 1 =>
    let zj : Nat → Int := fun i ↦ certEntryInt entry i j
    let b2zj_k := adjMulPure rotBytes (fun v ↦ adjMulPure rotBytes zj n d v) n d k
    let pij := c₁ * certEntryInt entry k j - c₂ * b2zj_k + c₃ * colSum
    max (epsMaxCol rotBytes entry n d c₁ c₂ c₃ j colSum k) (intAbs pij)

/-- Maximum off-diagonal `|P[k,j]|` over `k < j`, for all `j < bound`. -/
def epsMaxVal (rotBytes : String) (entry : Nat → Nat → Int) (n d : Nat) (c₁ c₂ c₃ : Int) : Nat → Int
  | 0 => 0
  | j + 1 =>
    max (epsMaxVal rotBytes entry n d c₁ c₂ c₃ j)
        (epsMaxCol rotBytes entry n d c₁ c₂ c₃ j (colSumZ entry n j) j)

/-- Minimum diagonal `P[j,j]` over `j < bound`. Returns `0` for `bound = 0`. -/
def minDiagVal (rotBytes : String) (entry : Nat → Nat → Int) (n d : Nat) (c₁ c₂ c₃ : Int) : Nat → Int
  | 0 => 0
  | 1 => pEntryPure rotBytes entry n d c₁ c₂ c₃ 0 0
  | m + 2 => min (minDiagVal rotBytes entry n d c₁ c₂ c₃ (m + 1))
                  (pEntryPure rotBytes entry n d c₁ c₂ c₃ (m + 1) (m + 1))

/-- Pure recursive version of `checkColumnNormBound` for formal reasoning.
    Uses `epsMaxVal`/`minDiagVal` (pure recursive) instead of imperative `checkPSDColumns`.
    Equivalent to the imperative version but trivially amenable to spec proofs. -/
def checkColumnNormBoundPure (rotBytes : String) (entry : Nat → Nat → Int) (n d : Nat)
    (c₁ c₂ c₃ : Int) : Bool :=
  if n == 0 then false
  else
    let ε := epsMaxVal rotBytes entry n d c₁ c₂ c₃ n
    let δ := minDiagVal rotBytes entry n d c₁ c₂ c₃ n
    checkPerRow entry n ε (δ + ε) n 0 0

end
