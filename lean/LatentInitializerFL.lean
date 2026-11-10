import LatentContextFL
import LatentZeroBranch
import Trans.Control.Rank

/-! Concrete general initializer. Dispatch is on latent r, not physical n.
The r=0 branch calls exact endpoint rank evaluation and returns its one ratio;
it never invokes the SAT controller. Positive r uses the existing generic
controller initializer, including when n=0. Installation and tape bounds remain
separate from the FL denotation and compiled-body validity proved here. -/
set_option autoImplicit false
namespace QecReliability.LatentMachine.InitializerFL
open FL FL.Lib FL.Tm Trans.Wire
open Trans.Control
open OracleCost.WholeWrapperCandidate
open ParserFL ContextFL
open SharedCircuit SharedCircuit.LatentEncoding

/-- Terminal singleton configuration, not the iid constant-one configuration. -/
def terminal (v : RationalOutput.Ratio) : Config := { pc := .done, output := [v] }

def terminalBody : Tm [TR] TCfg :=
  .letE (.lit (encCfg ({ pc := .done } : Config))) <|
    F.cfgWith v0 (g5 := F.g5With v0 (output := .lcons v1 .lnil))

def terminalF (idx : ℕ) := bodySig idx terminalBody

theorem terminal_den (idx : ℕ) (v : RationalOutput.Ratio) :
    (terminalF idx).den (toR v) = encCfg (terminal v) := by
  simp [terminalF,bodySig_den,terminalBody,tm_simp,encCfg,terminal]

variable (L : Lib) (h : HIx) (p : PIx) (i : ParserFL.Indices) (a : AIx)
  (y : IxI) (z : IxR)
  (Fp : FnSig (.prod .nat (.prod .nat .nat)) Trans.Hash.TParams)
  (base den ctxIdx terminalIdx topIdx : ℕ)

def initialBody : Tm [.list .bool] (TArg TX) :=
  .letE (.app (ParserFL.parseF L h p i) v0) <|
  .letE (.app (contextF L a Fp base den ctxIdx) v0) <|
  .pair v0 (.ite (.isZero (pR v1))
    (.app (terminalF terminalIdx)
      (.app (endpointF z) (.pair
        (.pair (pN v1) (.pair (pR v1) (.pair (pRows v1) (pProgram v1)))) .ff)))
    (.app (initF y) (.pair (.fst (.fst v0))
      (.pair (pR v1) (.snd (.snd (.snd (.fst v0))))))))

def initialF := bodySig topIdx (initialBody L h p i a y z Fp base den ctxIdx terminalIdx)

theorem initial_pos
    (hFp : ∀ x, Fp.den x = (Trans.Hash.params x.1 x.2.1 x.2.2).tuple)
    {n r : ℕ} (hr : r ≠ 0) (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program r n) (x b c d : ℕ) (coins : List Bool) :
    (initialF L h p i a y z Fp base den ctxIdx terminalIdx topIdx).den
        (input rows C x b c d coins) =
      (encCtx (keySize n r) r (rationalCellBudget x b)
          (rationalRepetitionBudget (2*(r+1)) c d) (externalData base den rows C coins),
       encCfg (initial (keySize n r) r (rationalRepetitionBudget (2*(r+1)) c d))) := by
  change (initialF L h p i a y z Fp base den ctxIdx terminalIdx topIdx).den
    (OracleCost.WholeWrapperCandidate.InputEncoding.problemBits rows C x b c d ++ coins) = _
  simp only [initialF,bodySig_den,initialBody,tm_simp]
  rw [ParserFL.parseF_problemBits,context_den L a Fp base den ctxIdx hFp]
  simp only [pR,tm_simp,encCtx,hr,Bool.false_eq_true,↓reduceIte]
  rw [initF_den]

theorem initial_zero
    (hFp : ∀ x, Fp.den x = (Trans.Hash.params x.1 x.2.1 x.2.2).tuple)
    {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program 0 n) (x b c d : ℕ) (coins : List Bool) :
    (initialF L h p i a y z Fp base den ctxIdx terminalIdx topIdx).den
        (input rows C x b c d coins) =
      (encCtx (keySize n 0) 0 (rationalCellBudget x b)
          (rationalRepetitionBudget (2*(0+1)) c d) (externalData base den rows C coins),
       encCfg (terminal (RationalOutput.Ratio.dyadic rows (circuitMap C ∅)))) := by
  change (initialF L h p i a y z Fp base den ctxIdx terminalIdx topIdx).den
    (OracleCost.WholeWrapperCandidate.InputEncoding.problemBits rows C x b c d ++ coins) = _
  simp only [initialF,bodySig_den,initialBody,tm_simp]
  rw [ParserFL.parseF_problemBits,context_den L a Fp base den ctxIdx hFp]
  simp only [pN,pR,pRows,pProgram,tm_simp,encCtx,↓reduceIte]
  rw [endpointF_correct,terminal_den]
  rfl

/-- The zero branch's ratio equals the previously specified degree-zero output. -/
theorem terminal_zero_output {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program 0 n) :
    (terminal (RationalOutput.Ratio.dyadic rows (circuitMap C ∅))).output =
      [(zeroLatentOutput rows C).get ⟨0,by omega⟩] := by
  rw [zeroLatentOutput_entry]
  rfl

theorem initial_valid {P : FL.Program}
    (hp : ∀ w, (ParserFL.parseF L h p i).ValidAt P w)
    (hc : ∀ x, (contextF L a Fp base den ctxIdx).ValidAt P x)
    (hy : LibI y P) (hz : LibR z P)
    (ht : P[terminalIdx]? = some terminalBody.compile)
    (hi : P[topIdx]? = some
      (initialBody L h p i a y z Fp base den ctxIdx terminalIdx).compile) :
    ∀ w, (initialF L h p i a y z Fp base den ctxIdx terminalIdx topIdx).ValidAt P w := by
  have hv : ∀ v, (terminalF terminalIdx).ValidAt P v := fun v =>
    bodySig_valid ht (by simp [terminalBody,tm_simp])
  intro w
  apply bodySig_valid hi
  simp only [initialBody,tm_simp,hp,hc,endpoint_valid hz,init_valid hy,hv,true_and]
  split_ifs <;> trivial

end QecReliability.LatentMachine.InitializerFL
