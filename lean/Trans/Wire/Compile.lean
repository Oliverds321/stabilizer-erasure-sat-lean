import Trans.Wire.Init
import Trans.Control.StepMain
import Trans.Control.Rank
import Trans.Query.Main

/-!
# Trans.Wire.Compile: the external FnSigs of the controller

The controller transcription (`Trans/Control`) takes two external signatures on its context
data `X : TX = (n, rows, C, q, SB, coins)`:

* `compileF Q H : FnSig (TX × TKey) (list bool)`: for a base key `(false, side, j, …)` it
  calls the query function `Q` (e.g. `Query.queryFnF stdIx`) at the base argument
  `(false, n, n, rows, C, side, j, ([], []), [], [], D)`; for a cell key
  `(true, side, j, rep, scale, pre)` it slices the seed bits
  `take SB (drop (rep·SB) coins)` (`sliceF`), runs the hash program function `H`
  (e.g. `Hash.hashF …`) at `(base, den, q, scale, slice)` (`hashWF`) and calls `Q` at the cell
  argument `(true, n, n, rows, C, side, j, H(…), replicate scale false, pre, D)`.
* `endpointWF : FnSig (TX × bool) TR`: `Control.endpointF` at `((n, n, rows, C), side)`.

All are `bodySig`s; `compile_valid`, `endpointW_valid` (every argument, from the callees'
validity), `compileF_den_base`, `compileF_den_cell`, `endpointWF_den` (meaning on plain data).
The instance-level agreement with `macroExternal` is in `Trans/Wire/Agree.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.Trans.Wire
open QecReliability.FL QecReliability.FL.Lib Tm
open QecReliability.Trans.Control (bodySig bodySig_den bodySig_valid TKey TR encKey IxR endpointF
  endpointF_correct LibR endpoint_valid)
open QecReliability.Trans.Hash (THashArg)
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate
open QecReliability.SharedCircuit QecReliability.SharedCircuit.LatentEncoding

/-! ## Types and projections -/

/-- The argument type of `Query.queryFnF` (`TQueryArg`):
`(isCell, n, r, rows, C, side, j, H, target, pre, D)`. -/
abbrev WQArg : Ty :=
  .prod .bool (.prod .nat (.prod .nat (.prod TRowsW (.prod WProg (.prod .bool (.prod .nat
    (.prod WProg (.prod (.list .bool) (.prod (.list .bool) .nat)))))))))

section Proj
variable {Γ : List Ty} (x : Tm Γ TX) (k : Tm Γ TKey)
abbrev Xn : Tm Γ .nat := .fst x
abbrev Xrows : Tm Γ TRowsW := .fst (.snd x)
abbrev XC : Tm Γ WProg := .fst (.snd (.snd x))
abbrev Xq : Tm Γ .nat := .fst (.snd (.snd (.snd x)))
abbrev XSB : Tm Γ .nat := .fst (.snd (.snd (.snd (.snd x))))
abbrev Xcoins : Tm Γ (.list .bool) := .snd (.snd (.snd (.snd (.snd x))))
abbrev Kcell : Tm Γ .bool := .fst k
abbrev Kgood : Tm Γ .bool := .fst (.snd k)
abbrev Kcoef : Tm Γ .nat := .fst (.snd (.snd k))
abbrev Krep : Tm Γ .nat := .fst (.snd (.snd (.snd k)))
abbrev Kscale : Tm Γ .nat := .fst (.snd (.snd (.snd (.snd k))))
abbrev Kpre : Tm Γ (.list .bool) := .snd (.snd (.snd (.snd (.snd k))))
end Proj

/-! ## Bodies -/

/-- Indices of the wrapper functions. -/
structure CIx where
  slice : ℕ
  hashW : ℕ
  cellQ : ℕ
  baseQ : ℕ
  compile : ℕ
  endpointW : ℕ

variable (L : Lib) (c : CIx) (Q : FnSig WQArg (.list .bool)) (H : FnSig THashArg WProg)
  (base den D : ℕ) (y : IxR)

/-- `(X, key) ↦ take SB (drop (rep·SB) coins)`. -/
def sliceBody : Tm [.prod TX TKey] (.list .bool) :=
  .app (takeF .bool L.take) (.pair (XSB (.fst v0))
    (.app (dropF .bool L.drop) (.pair
      (.app (mulF L.mul) (.pair (Krep (.snd v0)) (XSB (.fst v0)))) (Xcoins (.fst v0)))))
def sliceF : FnSig (.prod TX TKey) (.list .bool) := bodySig c.slice (sliceBody L)

/-- `(X, key) ↦ H (base, den, q, scale, slice)`. -/
def hashWBody : Tm [.prod TX TKey] WProg :=
  .app H (.pair (.lit base) (.pair (.lit den) (.pair (Xq (.fst v0))
    (.pair (Kscale (.snd v0)) (.app (sliceF L c) v0)))))
def hashWF : FnSig (.prod TX TKey) WProg := bodySig c.hashW (hashWBody L c H base den)

/-- The cell query. -/
def cellQBody : Tm [.prod TX TKey] (.list .bool) :=
  .app Q (.pair .tt (.pair (Xn (.fst v0)) (.pair (Xn (.fst v0)) (.pair (Xrows (.fst v0))
    (.pair (XC (.fst v0)) (.pair (Kgood (.snd v0)) (.pair (Kcoef (.snd v0))
      (.pair (.app (hashWF L c H base den) v0)
        (.pair (.app (replicateF .bool L.rep) (.pair (Kscale (.snd v0)) .ff))
          (.pair (Kpre (.snd v0)) (.lit D)))))))))))
def cellQF : FnSig (.prod TX TKey) (.list .bool) := bodySig c.cellQ (cellQBody L c Q H base den D)

/-- The base query. -/
def baseQBody : Tm [.prod TX TKey] (.list .bool) :=
  .app Q (.pair .ff (.pair (Xn (.fst v0)) (.pair (Xn (.fst v0)) (.pair (Xrows (.fst v0))
    (.pair (XC (.fst v0)) (.pair (Kgood (.snd v0)) (.pair (Kcoef (.snd v0))
      (.pair (.lit ([], [])) (.pair .lnil (.pair .lnil (.lit D)))))))))))
def baseQF : FnSig (.prod TX TKey) (.list .bool) := bodySig c.baseQ (baseQBody Q D)

/-- **The compile wrapper** `(X, key) ↦ query bits`. -/
def compileBody : Tm [.prod TX TKey] (.list .bool) :=
  .ite (Kcell (.snd v0)) (.app (cellQF L c Q H base den D) v0) (.app (baseQF c Q D) v0)
def compileF : FnSig (.prod TX TKey) (.list .bool) :=
  bodySig c.compile (compileBody L c Q H base den D)

/-- **The endpoint wrapper** `(X, side) ↦ endpointF ((n, n, rows, C), side)`. -/
def endpointWBody : Tm [.prod TX .bool] TR :=
  .app (endpointF y) (.pair (.pair (Xn (.fst v0)) (.pair (Xn (.fst v0)) (.pair (Xrows (.fst v0))
    (XC (.fst v0))))) (.snd v0))
def endpointWF : FnSig (.prod TX .bool) TR := bodySig c.endpointW (endpointWBody y)

/-! ## Meaning -/

section Den
variable (n : ℕ) (rows : List (List (Bool × ℕ))) (C : Query.Plain.ProgP) (q SB : ℕ)
  (coins : List Bool)

theorem sliceF_den (key : TKey.den) :
    (sliceF L c).den ((n, rows, C, q, SB, coins), key) =
      (coins.drop (key.2.2.2.1 * SB)).take SB := by
  simp [sliceF, bodySig_den, sliceBody, tm_simp]

theorem compileF_den_base (side : Bool) (j rep : ℕ) :
    (compileF L c Q H base den D).den ((n, rows, C, q, SB, coins), encKey (.base side j rep)) =
      Q.den (false, n, n, rows, C, side, j, ([], []), [], [], D) := by
  simp [compileF, bodySig_den, compileBody, baseQF, baseQBody, tm_simp, encKey]

theorem compileF_den_cell (side : Bool) (j rep scale : ℕ) (pre : List Bool) :
    (compileF L c Q H base den D).den
        ((n, rows, C, q, SB, coins), encKey (.cell side j rep scale pre)) =
      Q.den (true, n, n, rows, C, side, j,
        H.den (base, den, q, scale, (coins.drop (rep * SB)).take SB),
        List.replicate scale false, pre, D) := by
  simp [compileF, bodySig_den, compileBody, cellQF, cellQBody, hashWF, hashWBody, sliceF,
    sliceBody, tm_simp, encKey]

end Den

theorem endpointWF_den {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program n n) (q SB : ℕ) (coins : List Bool) (side : Bool) :
    (endpointWF c y).den ((n, Query.encRows rows, Query.encProg C, q, SB, coins), side) =
      Control.toR (Final.concreteEndpoint rows C side).value := by
  simp only [endpointWF, bodySig_den, endpointWBody, tm_simp]
  exact endpointF_correct y rows C side

/-! ## Validity -/

/-- The wrapper bodies are installed at their indices. -/
structure CIx.OK (P : Program) : Prop where
  slice : P[c.slice]? = some (sliceBody L).compile
  hashW : P[c.hashW]? = some (hashWBody L c H base den).compile
  cellQ : P[c.cellQ]? = some (cellQBody L c Q H base den D).compile
  baseQ : P[c.baseQ]? = some (baseQBody Q D).compile
  compile : P[c.compile]? = some (compileBody L c Q H base den D).compile
  endpointW : P[c.endpointW]? = some (endpointWBody y).compile

section Valid
variable {L c Q H base den D y} {P : Program} (hL : L.OK P) (hQ : ∀ x, Q.ValidAt P x)
  (hH : ∀ x, H.ValidAt P x) (hC : c.OK L Q H base den D y P)
include hL hQ hH hC

theorem slice_valid : ∀ x, (sliceF L c).ValidAt P x := fun x =>
  bodySig_valid hC.slice (by simp [tm_simp, sliceBody, hL.take, hL.drop, hL.mul])

theorem hashW_valid : ∀ x, (hashWF L c H base den).ValidAt P x := fun x =>
  bodySig_valid hC.hashW (by simp [tm_simp, hashWBody, hH, slice_valid hL hQ hH hC])

theorem cellQ_valid : ∀ x, (cellQF L c Q H base den D).ValidAt P x := fun x =>
  bodySig_valid hC.cellQ (by
    simp [tm_simp, cellQBody, hQ, hashW_valid hL hQ hH hC, hL.rep])

theorem baseQ_valid : ∀ x, (baseQF c Q D).ValidAt P x := fun x =>
  bodySig_valid hC.baseQ (by simp [tm_simp, baseQBody, hQ])

/-- **Validity of the compile wrapper** at every argument. -/
theorem compile_valid : ∀ x, (compileF L c Q H base den D).ValidAt P x := fun x =>
  bodySig_valid hC.compile (by
    simp [tm_simp, compileBody, cellQ_valid hL hQ hH hC, baseQ_valid hL hQ hH hC])

end Valid

/-- **Validity of the endpoint wrapper** at every argument. -/
theorem endpointW_valid {c : CIx} {y : IxR} {P : Program} (hR : LibR y P)
    (hE : P[c.endpointW]? = some (endpointWBody y).compile) :
    ∀ x, (endpointWF c y).ValidAt P x := fun x =>
  bodySig_valid hE (by simp [tm_simp, endpointWBody, endpoint_valid hR])

end QecReliability.Trans.Wire
