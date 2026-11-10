import TensorMachineInstalled
import LatentContextFL

/-! The tensor controller context keeps the complete degree list, cached grid,
and old circuit/hash data. Its coefficient counter is Q-1, independently of
the number of latent causes. Repetition precision is computed for 2Q jobs. -/

set_option autoImplicit false

namespace QecReliability.TensorMachine.ContextFL

open FL FL.Lib FL.Tm Trans.Wire
open Trans.Control (bodySig bodySig_den bodySig_valid TCtx encCtx)
open SharedCircuit SharedCircuit.LatentEncoding

abbrev TX : Ty := .prod (.list .nat) (.prod GridFL.Table Trans.Wire.TX)

def externalData (base den : ℕ) (ds : List ℕ) {n : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (coins : List Bool) : TX.den :=
  (ds, grid ds, LatentMachine.ContextFL.externalData base den rows C coins)

variable (L : Lib) (a : AIx) (gi : GridFL.Indices)
  (Fp : FnSig (.prod .nat (.prod .nat .nat)) Trans.Hash.TParams)
  (base den oldCtx lengthIdx ctxIdx : ℕ)

def contextBody : Tm [ParserFL.ParsedTy] (TCtx TX) :=
  .letE (.app (GridFL.gridF L gi) (.fst v0)) <|
  .letE (.app (predF L.pred) (.app (lengthF GridFL.Row lengthIdx) v0)) <|
  .letE (.app (LatentMachine.ContextFL.contextF L a Fp base den oldCtx) (.snd v2)) <|
  .pair
    (.pair (.fst (.fst v0)) (.pair v1
      (.pair (.fst (.snd (.snd (.fst v0))))
        (.app (repBF L a) (.pair v1
          (.pair (LatentMachine.ContextFL.pC (.snd v3))
            (LatentMachine.ContextFL.pD (.snd v3))))))))
    (.pair (.fst v3) (.pair v2 (.snd v0)))

def contextF := bodySig ctxIdx (contextBody L a gi Fp base den oldCtx lengthIdx)

theorem context_den
    (hFp : ∀ x, Fp.den x = (Trans.Hash.params x.1 x.2.1 x.2.2).tuple)
    (ds : List ℕ) {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program ds.sum n) (x z c d : ℕ) (coins : List Bool) :
    (contextF L a gi Fp base den oldCtx lengthIdx ctxIdx).den
      (ds,n,ds.sum,Trans.Query.encRows rows,Trans.Query.encProg C,x,z,c,d,coins) =
      encCtx (keySize n ds.sum) (slots ds - 1) (rationalCellBudget x z)
        (rationalRepetitionBudget (2 * slots ds) c d)
        (externalData base den ds rows C coins) := by
  have hslots : slots ds - 1 + 1 = slots ds := by have := slots_pos ds; omega
  simp only [contextF, bodySig_den, contextBody, tm_simp,
    LatentMachine.ContextFL.pC, LatentMachine.ContextFL.pD]
  rw [GridFL.gridF_den, lengthF_den, grid_length, predF_den,
    LatentMachine.ContextFL.context_den L a Fp base den oldCtx hFp]
  simp only [encCtx]
  rw [repBF_den, hslots]
  rfl

theorem context_valid {P : FL.Program} (hL : L.OK P)
    (hg : ∀ ds, (GridFL.gridF L gi).ValidAt P ds)
    (hl : ∀ xs, (lengthF GridFL.Row lengthIdx).ValidAt P xs)
    (hc : ∀ p, (LatentMachine.ContextFL.contextF L a Fp base den oldCtx).ValidAt P p)
    (hr : ∀ p, (repBF L a).ValidAt P p)
    (hi : P[ctxIdx]? = some (contextBody L a gi Fp base den oldCtx lengthIdx).compile) :
    ∀ p, (contextF L a gi Fp base den oldCtx lengthIdx ctxIdx).ValidAt P p := by
  intro p
  apply bodySig_valid hi
  simp [contextBody, tm_simp, LatentMachine.ContextFL.pC, LatentMachine.ContextFL.pD,
    hg, hl, hc, hr, hL.pred]

end QecReliability.TensorMachine.ContextFL
