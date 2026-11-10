import LatentContextFL
import Trans.Wire.Compile

/-! Actual latent query/endpoint wrappers. The existing TX keeps q rather than
r; recover r by natural subtraction q-(n+n). On canonical externalData this is
exact, including n=0 or r=0. Malformed TX has total truncated-subtraction behavior.
No machine installation or all-tape bound is asserted by this module. -/
set_option autoImplicit false
namespace QecReliability.LatentMachine.WrappersFL
open FL FL.Lib FL.Tm Trans.Wire
open Trans.Control (bodySig bodySig_den bodySig_valid TKey TR encKey IxR endpointF
  endpointF_correct LibR endpoint_valid)
open SharedCircuit SharedCircuit.LatentEncoding

def Xr (L : Lib) {Γ : List Ty} (x : Tm Γ TX) : Tm Γ .nat :=
  .app (subF L.sub) (.pair (Xq x) (.app (addF L.add) (.pair (Xn x) (Xn x))))

variable (L : Lib) (c : CIx) (Q : FnSig WQArg (.list .bool))
  (H : FnSig Trans.Hash.THashArg WProg) (base den D : ℕ) (y : IxR)

/-- The cell query. -/
def cellQBody : Tm [.prod TX TKey] (.list .bool) :=
  .app Q (.pair .tt (.pair (Xn (.fst v0)) (.pair (Xr L (.fst v0)) (.pair (Xrows (.fst v0))
    (.pair (XC (.fst v0)) (.pair (Kgood (.snd v0)) (.pair (Kcoef (.snd v0))
      (.pair (.app (hashWF L c H base den) v0)
        (.pair (.app (replicateF .bool L.rep) (.pair (Kscale (.snd v0)) .ff))
          (.pair (Kpre (.snd v0)) (.lit D)))))))))))
def cellQF : FnSig (.prod TX TKey) (.list .bool) := bodySig c.cellQ (cellQBody L c Q H base den D)

/-- The base query. -/
def baseQBody : Tm [.prod TX TKey] (.list .bool) :=
  .app Q (.pair .ff (.pair (Xn (.fst v0)) (.pair (Xr L (.fst v0)) (.pair (Xrows (.fst v0))
    (.pair (XC (.fst v0)) (.pair (Kgood (.snd v0)) (.pair (Kcoef (.snd v0))
      (.pair (.lit ([], [])) (.pair .lnil (.pair .lnil (.lit D)))))))))))
def baseQF : FnSig (.prod TX TKey) (.list .bool) := bodySig c.baseQ (baseQBody L Q D)

/-- **The compile wrapper** `(X, key) ↦ query bits`. -/
def compileBody : Tm [.prod TX TKey] (.list .bool) :=
  .ite (Kcell (.snd v0)) (.app (cellQF L c Q H base den D) v0) (.app (baseQF L c Q D) v0)
def compileF : FnSig (.prod TX TKey) (.list .bool) :=
  bodySig c.compile (compileBody L c Q H base den D)

/-- **The endpoint wrapper** `(X, side) ↦ endpointF ((n, r, rows, C), side)`. -/
def endpointWBody : Tm [.prod TX .bool] TR :=
  .app (endpointF y) (.pair (.pair (Xn (.fst v0)) (.pair (Xr L (.fst v0)) (.pair (Xrows (.fst v0))
    (XC (.fst v0))))) (.snd v0))
def endpointWF : FnSig (.prod TX .bool) TR := bodySig c.endpointW (endpointWBody L y)

section Den
variable (n : ℕ) (rows : List (List (Bool × ℕ))) (C : Trans.Query.Plain.ProgP) (r SB : ℕ)
  (coins : List Bool)

theorem compileF_den_base (side : Bool) (j rep : ℕ) :
    (compileF L c Q H base den D).den ((n, rows, C, keySize n r, SB, coins), encKey (.base side j rep)) =
      Q.den (false, n, r, rows, C, side, j, ([], []), [], [], D) := by
  simp [compileF, bodySig_den, compileBody, baseQF, baseQBody, tm_simp, encKey, Xr, keySize, subF_den, addF_den]

theorem compileF_den_cell (side : Bool) (j rep scale : ℕ) (pre : List Bool) :
    (compileF L c Q H base den D).den
        ((n, rows, C, keySize n r, SB, coins), encKey (.cell side j rep scale pre)) =
      Q.den (true, n, r, rows, C, side, j,
        H.den (base, den, keySize n r, scale, (coins.drop (rep * SB)).take SB),
        List.replicate scale false, pre, D) := by
  simp [compileF, bodySig_den, compileBody, cellQF, cellQBody, hashWF, hashWBody, sliceF,
    sliceBody, tm_simp, encKey, Xr, keySize, subF_den, addF_den]

end Den

theorem endpointWF_den {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program r n) (SB : ℕ) (coins : List Bool) (side : Bool) :
    (endpointWF L c y).den ((n, Trans.Query.encRows rows, Trans.Query.encProg C, keySize n r, SB, coins), side) =
      Trans.Control.toR (Final.concreteEndpoint rows C side).value := by
  simp only [endpointWF, bodySig_den, endpointWBody, tm_simp, Xr, keySize, subF_den, addF_den, Nat.add_sub_cancel]
  exact endpointF_correct y rows C side


/-- Only the new concrete bodies occupy these slots; existing hash slicing is reused. -/
structure Slots (P : FL.Program) : Prop where
  cellQ : P[c.cellQ]? = some (cellQBody L c Q H base den D).compile
  baseQ : P[c.baseQ]? = some (baseQBody L Q D).compile
  compile : P[c.compile]? = some (compileBody L c Q H base den D).compile
  endpointW : P[c.endpointW]? = some (endpointWBody L y).compile

theorem compile_valid {P : FL.Program} (hL : L.OK P)
    (hQ : ∀ x, Q.ValidAt P x)
    (hHash : ∀ x, (hashWF L c H base den).ValidAt P x)
    (hs : Slots L c Q H base den D y P) :
    ∀ x, (compileF L c Q H base den D).ValidAt P x := by
  have hc : ∀ x, (cellQF L c Q H base den D).ValidAt P x := fun x =>
    bodySig_valid hs.cellQ (by simp [tm_simp,cellQBody,Xr,hQ,hHash,hL.rep,hL.add,hL.sub])
  have hb : ∀ x, (baseQF L c Q D).ValidAt P x := fun x =>
    bodySig_valid hs.baseQ (by simp [tm_simp,baseQBody,Xr,hQ,hL.add,hL.sub])
  intro x
  exact bodySig_valid hs.compile (by simp [tm_simp,compileBody,hc,hb])

theorem endpoint_valid {P : FL.Program} (hL : L.OK P) (hR : LibR y P)
    (hs : P[c.endpointW]? = some (endpointWBody L y).compile) :
    ∀ x, (endpointWF L c y).ValidAt P x := fun x =>
  bodySig_valid hs (by simp [tm_simp,endpointWBody,Xr,hL.add,hL.sub,Trans.Control.endpoint_valid hR])

end QecReliability.LatentMachine.WrappersFL

