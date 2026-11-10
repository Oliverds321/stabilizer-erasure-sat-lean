import TensorMachineGrid
import LatentMachineInput
import LatentProgramParserFL

/-! Tensor input extends the existing complete circuit encoding with a
self-delimiting degree list. The parser preserves the literal random suffix.
The circuit has one input for each cause across all classes. -/

set_option autoImplicit false

namespace QecReliability.TensorMachine

open SharedCircuit
open OracleCost.WholeWrapperCandidate.InputEncoding

def input (ds : List ℕ) {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program ds.sum n) (a b c d : ℕ) (coins : List Bool) : List Bool :=
  degreesBits ds ++ LatentMachine.input rows C a b c d coins

def parse (bs : List Bool) : List ℕ × LatentMachine.Parser.Parsed :=
  let h := degreesR bs
  (h.1, LatentMachine.Parser.parse h.2)

theorem parse_input (ds : List ℕ) {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program ds.sum n) (a b c d : ℕ) (coins : List Bool) :
    parse (input ds rows C a b c d coins) =
      (ds, n, ds.sum, Trans.Query.encRows rows, Trans.Query.encProg C, a, b, c, d, coins) := by
  simp only [parse, input, degreesR_degreesBits, LatentMachine.input,
    LatentMachine.Parser.parse_problemBits]

theorem input_length (ds : List ℕ) {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program ds.sum n) (a b c d : ℕ) (coins : List Bool) :
    (input ds rows C a b c d coins).length =
      (degreesBits ds).length + (problemBits rows C a b c d).length + coins.length := by
  simp [input, LatentMachine.input, List.length_append, Nat.add_assoc]

namespace ParserFL

open FL FL.Lib FL.Tm Trans.Wire
open Trans.Control (bodySig bodySig_den bodySig_valid)

abbrev ParsedTy : Ty := .prod (.list .nat) LatentMachine.ParserFL.ParsedTy

def degreesBody (L : Lib) (h : HIx) (p : LatentMachine.ParserFL.Indices) :
    Tm [.list .bool] (.prod (.list .nat) (.list .bool)) :=
  .app (LatentMachine.ParserFL.outputsF L h p) (.app (hdrF L h) v0)

def degreesF (L : Lib) (h : HIx) (p : LatentMachine.ParserFL.Indices) (idx : ℕ) :=
  bodySig idx (degreesBody L h p)

def parseBody (L : Lib) (h : HIx) (wp : PIx)
    (p : LatentMachine.ParserFL.Indices) (di : ℕ) : Tm [.list .bool] ParsedTy :=
  .letE (.app (degreesF L h p di) v0) <|
    .pair (.fst v0) (.app (LatentMachine.ParserFL.parseF L h wp p) (.snd v0))

def parseF (L : Lib) (h : HIx) (wp : PIx)
    (p : LatentMachine.ParserFL.Indices) (di pi : ℕ) :=
  bodySig pi (parseBody L h wp p di)

theorem degreesF_den (L : Lib) (h : HIx) (p : LatentMachine.ParserFL.Indices)
    (idx : ℕ) (bs : List Bool) : (degreesF L h p idx).den bs = degreesR bs := by
  have hh : (hdrF L h).den = hdr := funext (hdrF_den L h)
  simp only [degreesF, bodySig_den, degreesBody, tm_simp,
    LatentMachine.ParserFL.outputsF, hh, degreesR]
  change (manyF L (hdrF L h) p.outputStep p.outputFold p.outputMany).den
    ((hdr bs).1, (hdr bs).2) = _
  rw [manyF_den, hh]

theorem parseF_den (L : Lib) (h : HIx) (wp : PIx)
    (p : LatentMachine.ParserFL.Indices) (di pi : ℕ) (bs : List Bool) :
    (parseF L h wp p di pi).den bs = TensorMachine.parse bs := by
  simp only [parseF, bodySig_den, parseBody, tm_simp, degreesF_den,
    LatentMachine.ParserFL.parseF_den, TensorMachine.parse]

theorem degrees_valid {L : Lib} {h : HIx} {wp : PIx}
    {p : LatentMachine.ParserFL.Indices} {idx : ℕ} {P : FL.Program}
    (hL : L.OK P) (hh : h.OK L P) (hp : p.OK L h wp P)
    (hi : P[idx]? = some (degreesBody L h p).compile) :
    ∀ bs, (degreesF L h p idx).ValidAt P bs := by
  have ho := many_valid hL (hdr_valid hL hh) hp.outputStep hp.outputFold hp.outputMany
  intro bs
  apply bodySig_valid hi
  simp [degreesBody, LatentMachine.ParserFL.outputsF, tm_simp, ho, hdr_valid hL hh]

theorem parse_valid {L : Lib} {h : HIx} {wp : PIx}
    {p : LatentMachine.ParserFL.Indices} {di pi : ℕ} {P : FL.Program}
    (hd : ∀ bs, (degreesF L h p di).ValidAt P bs)
    (hp : ∀ bs, (LatentMachine.ParserFL.parseF L h wp p).ValidAt P bs)
    (hi : P[pi]? = some (parseBody L h wp p di).compile) :
    ∀ bs, (parseF L h wp p di pi).ValidAt P bs := by
  intro bs
  apply bodySig_valid hi
  simp [parseBody, tm_simp, hd, hp]

end ParserFL
end QecReliability.TensorMachine
