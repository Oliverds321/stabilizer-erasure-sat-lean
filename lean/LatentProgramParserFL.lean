import LatentGateParserFL

/-! Fixed FL bodies for the general circuit/program and full input parser.
The existing `manyF` implements both count-controlled loops; no machine is
chosen after seeing C. Validity and exact denotation are separated from the
remaining cost/depth/msize and installation work.
-/
set_option autoImplicit false
namespace QecReliability.LatentMachine.ParserFL
open FL FL.Lib FL.Tm Trans.Wire
open Trans.Control (bodySig bodySig_den bodySig_valid)

abbrev ProgramTy : Ty := .prod (.list GateTy) (.list .nat)
abbrev ParsedTy : Ty := .prod .nat (.prod .nat (.prod TRowsW (.prod ProgramTy
  (.prod .nat (.prod .nat (.prod .nat (.prod .nat (.list .bool))))))))

structure Indices where
  gate : ℕ
  gateStep : ℕ
  gateFold : ℕ
  gateMany : ℕ
  outputStep : ℕ
  outputFold : ℕ
  outputMany : ℕ
  program : ℕ
  parse : ℕ

variable (L : Lib) (h : HIx) (p : PIx) (i : Indices)

def gatesF := manyF L (gateF L h i.gate) i.gateStep i.gateFold i.gateMany
def outputsF := manyF L (hdrF L h) i.outputStep i.outputFold i.outputMany

def programBody : Tm [.prod .nat (.list .bool)] (.prod ProgramTy (.list .bool)) :=
  .letE (.app (hdrF L h) (.snd v0)) <|
    .letE (.app (gatesF L h i) v0) <|
      .letE (.app (outputsF L h i) (.pair (.fst v2) (.snd v0))) <|
        .pair (.pair (.fst v1) (.fst v0)) (.snd v0)

def programF := bodySig i.program (programBody L h i)

def parseBody : Tm [.list .bool] ParsedTy :=
  .letE (.app (hdrF L h) v0) <|
    .letE (.app (hdrF L h) (.snd v0)) <|
      .letE (.app (rowsF L h p) (.snd v0)) <|
        .letE (.app (programF L h i) (.pair (.fst v2) (.snd v0))) <|
          .pair (.fst v3) (.pair (.fst v2) (.pair (.fst v1)
            (.pair (.fst v0) (.app (precF L h p) (.snd v0)))))

def parseF := bodySig i.parse (parseBody L h p i)

theorem programF_den (n : ℕ) (bs : List Bool) :
    (programF L h i).den (n,bs) = Parser.programR n bs := by
  have hg : (gateF L h i.gate).den = Parser.gateR := funext (gateF_den L h i.gate)
  have hh : (hdrF L h).den = hdr := funext (hdrF_den L h)
  have hgs : (gatesF L h i).den = fun x => many Parser.gateR x.1 x.2 := by
    funext x
    rcases x with ⟨k, bs⟩
    change (manyF L (gateF L h i.gate) i.gateStep i.gateFold i.gateMany).den (k,bs) = _
    rw [manyF_den, hg]
  have hos : (outputsF L h i).den = fun x => many hdr x.1 x.2 := by
    funext x
    rcases x with ⟨k, bs⟩
    change (manyF L (hdrF L h) i.outputStep i.outputFold i.outputMany).den (k,bs) = _
    rw [manyF_den, hh]
  simp only [programF, bodySig_den, programBody, tm_simp, hdrF_den,
    hgs, hos, Parser.programR]

theorem parseF_den (bs : List Bool) :
    (parseF L h p i).den bs = Parser.parse bs := by
  have hprog : (programF L h i).den = fun x => Parser.programR x.1 x.2 := by
    funext x
    rcases x with ⟨n, bs⟩
    exact programF_den L h i n bs
  simp only [parseF, bodySig_den, parseBody, tm_simp, hdrF_den, rowsF_den,
    hprog, precF_den, Parser.parse]

theorem parseF_problemBits {n r : ℕ}
    (rows : List (List (SharedCircuit.PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ) (coins : List Bool) :
    (parseF L h p i).den
      (OracleCost.WholeWrapperCandidate.InputEncoding.problemBits rows C a b c d ++ coins) =
      (n,r,Trans.Query.encRows rows,Trans.Query.encProg C,a,b,c,d,coins) := by
  rw [parseF_den, Parser.parse_problemBits]

structure Indices.OK (P : FL.Program) : Prop where
  gate : P[i.gate]? = some (gateBody L h).compile
  gateStep : P[i.gateStep]? = some (manyStepBody (gateF L h i.gate)).compile
  gateFold : P[i.gateFold]? = some (foldlBody
    (manyStepF (gateF L h i.gate) i.gateStep) i.gateFold).compile
  gateMany : P[i.gateMany]? = some (manyBody L (gateF L h i.gate) i.gateStep i.gateFold).compile
  outputStep : P[i.outputStep]? = some (manyStepBody (hdrF L h)).compile
  outputFold : P[i.outputFold]? = some (foldlBody
    (manyStepF (hdrF L h) i.outputStep) i.outputFold).compile
  outputMany : P[i.outputMany]? = some (manyBody L (hdrF L h) i.outputStep i.outputFold).compile
  program : P[i.program]? = some (programBody L h i).compile
  parse : P[i.parse]? = some (parseBody L h p i).compile

theorem program_valid {P : FL.Program} (hL : L.OK P) (hH : h.OK L P)
    (hi : i.OK L h p P) : ∀ x, (programF L h i).ValidAt P x := by
  have hg := many_valid hL (gate_valid L h i.gate hL hH hi.gate)
    hi.gateStep hi.gateFold hi.gateMany
  have ho := many_valid hL (hdr_valid hL hH) hi.outputStep hi.outputFold hi.outputMany
  intro x
  apply bodySig_valid hi.program
  simp [tm_simp, programBody, gatesF, outputsF, hg, ho, hdr_valid hL hH]

theorem parse_valid {P : FL.Program} (hL : L.OK P) (hH : h.OK L P)
    (hp : p.OK L h P) (hi : i.OK L h p P) :
    ∀ bs, (parseF L h p i).ValidAt P bs := by
  intro bs
  apply bodySig_valid hi.parse
  simp [tm_simp, parseBody, hdr_valid hL hH, rows_valid hL hH hp,
    program_valid L h p i hL hH hi, prec_valid hL hH hp]

end QecReliability.LatentMachine.ParserFL
