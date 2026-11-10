import LatentInputParserBounds
import Trans.Wire.Init

/-! Fixed FL context construction for the general latent instance. In contrast
to the installed iid context, it copies the parsed program and latent dimension;
it never reconstructs a pure identity program or substitutes r=n.
-/
set_option autoImplicit false
namespace QecReliability.LatentMachine.ContextFL
open FL FL.Lib FL.Tm Trans.Wire
open ParserFL
open Trans.Control (bodySig bodySig_den bodySig_valid TCtx encCtx)
open SharedCircuit SharedCircuit.LatentEncoding

abbrev pN {Γ : List Ty} (x : Tm Γ ParsedTy) : Tm Γ .nat := .fst x
abbrev pR {Γ : List Ty} (x : Tm Γ ParsedTy) : Tm Γ .nat := .fst (.snd x)
abbrev pRows {Γ : List Ty} (x : Tm Γ ParsedTy) : Tm Γ TRowsW := .fst (.snd (.snd x))
abbrev pProgram {Γ : List Ty} (x : Tm Γ ParsedTy) : Tm Γ ProgramTy := .fst (.snd (.snd (.snd x)))
abbrev pA {Γ : List Ty} (x : Tm Γ ParsedTy) : Tm Γ .nat := .fst (.snd (.snd (.snd (.snd x))))
abbrev pB {Γ : List Ty} (x : Tm Γ ParsedTy) : Tm Γ .nat := .fst (.snd (.snd (.snd (.snd (.snd x)))))
abbrev pC {Γ : List Ty} (x : Tm Γ ParsedTy) : Tm Γ .nat := .fst (.snd (.snd (.snd (.snd (.snd (.snd x))))))
abbrev pD {Γ : List Ty} (x : Tm Γ ParsedTy) : Tm Γ .nat := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd x)))))))
abbrev pCoins {Γ : List Ty} (x : Tm Γ ParsedTy) : Tm Γ (.list .bool) := .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd x)))))))

variable (L : Lib) (a : AIx)
  (Fp : FnSig (.prod .nat (.prod .nat .nat)) Trans.Hash.TParams) (base den idx : ℕ)

def externalData {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program r n) (coins : List Bool) : TX.den :=
  (n,Trans.Query.encRows rows,Trans.Query.encProg C,keySize n r,
    seedB base den (keySize n r),coins)

def contextBody : Tm [ParsedTy] (TCtx TX) :=
  .letE (.app (addF L.add) (.pair (pR v0)
    (.app (addF L.add) (.pair (pN v0) (pN v0))))) <|
    .pair
      (.pair v0 (.pair (pR v1)
        (.pair (.app (cellBF L a) (.pair (pA v1) (pB v1)))
          (.app (repBF L a) (.pair (pR v1) (.pair (pC v1) (pD v1)))))))
      (.pair (pN v1) (.pair (pRows v1) (.pair (pProgram v1)
        (.pair v0 (.pair (.app (seedBF L a Fp base den) v0) (pCoins v1))))))

def contextF := bodySig idx (contextBody L a Fp base den)

theorem context_den
    (hFp : ∀ x, Fp.den x = (Trans.Hash.params x.1 x.2.1 x.2.2).tuple)
    {n r : ℕ} (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (x z c d : ℕ) (coins : List Bool) :
    (contextF L a Fp base den idx).den
      (n,r,Trans.Query.encRows rows,Trans.Query.encProg C,x,z,c,d,coins) =
      encCtx (keySize n r) r (rationalCellBudget x z)
        (rationalRepetitionBudget (2*(r+1)) c d) (externalData base den rows C coins) := by
  simp only [contextF,bodySig_den,contextBody,pN,pR,pRows,pProgram,pA,pB,pC,pD,pCoins,
    tm_simp,addF_den]
  rw [cellBF_den,repBF_den,seedBF_den L a Fp base den hFp]
  simp [encCtx,externalData,keySize,two_mul,Nat.add_assoc]

/-- The literal parsed circuit survives into the controller's external data. -/
theorem context_parse
    (hFp : ∀ x, Fp.den x = (Trans.Hash.params x.1 x.2.1 x.2.2).tuple)
    (h : HIx) (p : PIx) (i : ParserFL.Indices)
    {n r : ℕ} (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (x z c d : ℕ) (coins : List Bool) :
    (contextF L a Fp base den idx).den
      ((ParserFL.parseF L h p i).den (input rows C x z c d coins)) =
      encCtx (keySize n r) r (rationalCellBudget x z)
        (rationalRepetitionBudget (2*(r+1)) c d) (externalData base den rows C coins) := by
  change (contextF L a Fp base den idx).den
    ((ParserFL.parseF L h p i).den
      (OracleCost.WholeWrapperCandidate.InputEncoding.problemBits rows C x z c d ++ coins)) = _
  rw [ParserFL.parseF_problemBits,context_den L a Fp base den idx hFp]

/-- All callees are concrete existing compiled arithmetic functions. Their
validity can be reused from the installed library, not assumed for new syntax. -/
theorem context_valid {P : FL.Program} (hL : L.OK P)
    (hcell : ∀ x, (cellBF L a).ValidAt P x)
    (hrep : ∀ x, (repBF L a).ValidAt P x)
    (hseed : ∀ x, (seedBF L a Fp base den).ValidAt P x)
    (hi : P[idx]? = some (contextBody L a Fp base den).compile) :
    ∀ x, (contextF L a Fp base den idx).ValidAt P x := by
  intro x
  apply bodySig_valid hi
  simp [tm_simp,contextBody,pN,pR,pRows,pProgram,pA,pB,pC,pD,pCoins,
    hL.add,hcell,hrep,hseed]

end QecReliability.LatentMachine.ContextFL
