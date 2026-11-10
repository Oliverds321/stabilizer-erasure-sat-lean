import Trans.Wire.Header
import PhysicalBridge.ZeroLengthDispatchCandidate

/-!
# Trans.Wire.Parse: parsing the problem encoding

Plain parser `parse : List Bool → ℕ × rows × ℕ × ℕ × ℕ × ℕ × coins` and its FL transcription
`parseF` (all `bodySig`s over `hdrF`, `coordF`, `manyF`).

`parse_problemBits`: on `problemBits rows (iidProgram n) a b c d ++ coins` (the machine input
`Final.machineInput rows a b c d coins`) the parse returns `(n, encRows rows, a, b, c, d, coins)`.
The circuit header (`r`) and the program encoding of the fixed `iidProgram n` are skipped
(`1 + (n + 1)` headers); the program itself is rebuilt from `n` later.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.Trans.Wire
open QecReliability.FL QecReliability.FL.Lib Tm
open QecReliability.Trans.Control (bodySig bodySig_den bodySig_valid)
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate
open QecReliability.SharedCircuit

/-! ## Plain parser -/

/-- One row: a length header, then that many coordinates. -/
def rowR (bs : List Bool) : List (Bool × ℕ) × List Bool := many coordR (hdr bs).1 (hdr bs).2

/-- All rows: a count header, then that many rows. -/
def rowsR (bs : List Bool) : List (List (Bool × ℕ)) × List Bool := many rowR (hdr bs).1 (hdr bs).2

/-- The precision `a b c d` and the remaining coins. -/
def precR (bs : List Bool) : ℕ × ℕ × ℕ × ℕ × List Bool :=
  ((hdr bs).1, (hdr (hdr bs).2).1, (hdr (hdr (hdr bs).2).2).1,
    (hdr (hdr (hdr (hdr bs).2).2).2).1, (hdr (hdr (hdr (hdr bs).2).2).2).2)

/-- The whole input: `(n, rows, a, b, c, d, coins)`. -/
def parse (bs : List Bool) : ℕ × List (List (Bool × ℕ)) × ℕ × ℕ × ℕ × ℕ × List Bool :=
  ((hdr bs).1, (rowsR (hdr (hdr bs).2).2).1,
    precR (many hdr ((hdr bs).1 + 1) (rowsR (hdr (hdr bs).2).2).2).2)

theorem rowR_rowBits {n : ℕ} (row : List (PauliCoord n)) (rest : List Bool) :
    rowR (InputEncoding.rowBits row ++ rest) = (row.map Query.encCoord, rest) := by
  unfold rowR
  simp only [InputEncoding.rowBits, List.append_assoc, hdr_natHeader]
  exact many_flatMap coordR InputEncoding.coordBits Query.encCoord coordR_coordBits row rest

theorem rowsR_rowsBits {n : ℕ} (rows : List (List (PauliCoord n))) (rest : List Bool) :
    rowsR (InputEncoding.rowsBits rows ++ rest) = (Query.encRows rows, rest) := by
  unfold rowsR
  simp only [InputEncoding.rowsBits, List.append_assoc, hdr_natHeader]
  exact many_flatMap rowR InputEncoding.rowBits (fun row => row.map Query.encCoord) rowR_rowBits
    rows rest

theorem programBits_iid (n : ℕ) :
    InputEncoding.programBits (ZeroLengthDispatch.iidProgram n) =
      (0 :: List.ofFn (fun i : Fin n => i.val)).flatMap QueryCodec.natHeader := by
  simp only [InputEncoding.programBits, InputEncoding.outputBits, ZeroLengthDispatch.iidProgram_gates,
    List.flatMap_cons]
  have hc : InputEncoding.circuitBits (ZeroLengthDispatch.iidProgram n).circuit = [] := rfl
  rw [hc, List.append_nil]
  congr 1
  simp only [List.flatMap, List.map_ofFn]
  rfl

theorem skip_programBits (n : ℕ) (rest : List Bool) :
    (many hdr (n + 1) (InputEncoding.programBits (ZeroLengthDispatch.iidProgram n) ++ rest)).2 =
      rest := by
  rw [programBits_iid]
  have h := many_flatMap hdr QueryCodec.natHeader id hdr_natHeader
    (0 :: List.ofFn (fun i : Fin n => i.val)) rest
  simp only [List.length_cons, List.length_ofFn] at h
  rw [h]

theorem precR_precisionBits (a b c d : ℕ) (rest : List Bool) :
    precR (InputEncoding.precisionBits a b c d ++ rest) = (a, b, c, d, rest) := by
  simp only [precR, InputEncoding.precisionBits, List.append_assoc, hdr_natHeader]

/-- **Parsing the machine input.** -/
theorem parse_problemBits {n : ℕ} (rows : List (List (PauliCoord n))) (a b c d : ℕ)
    (coins : List Bool) :
    parse (InputEncoding.problemBits rows (ZeroLengthDispatch.iidProgram n) a b c d ++ coins) =
      (n, Query.encRows rows, a, b, c, d, coins) := by
  simp only [parse, InputEncoding.problemBits, List.append_assoc, hdr_natHeader, rowsR_rowsBits,
    skip_programBits, precR_precisionBits]

/-! ## FL -/

abbrev TCoordW : Ty := .prod .bool .nat
abbrev TRowsW : Ty := .list (.list TCoordW)
/-- `(n, rows, a, b, c, d, coins)`. -/
abbrev TParsed : Ty :=
  .prod .nat (.prod TRowsW (.prod .nat (.prod .nat (.prod .nat (.prod .nat (.list .bool))))))

/-- Indices of the parser. -/
structure PIx where
  cStep : ℕ
  cFold : ℕ
  cMany : ℕ
  row : ℕ
  rStep : ℕ
  rFold : ℕ
  rMany : ℕ
  rows : ℕ
  hStep : ℕ
  hFold : ℕ
  hMany : ℕ
  prec : ℕ
  parse : ℕ

variable (L : Lib) (h : HIx) (p : PIx)

def rowBody : Tm [.list .bool] (.prod (.list TCoordW) (.list .bool)) :=
  .app (manyF L (coordF L h) p.cStep p.cFold p.cMany) (.app (hdrF L h) v0)
def rowF : FnSig (.list .bool) (.prod (.list TCoordW) (.list .bool)) := bodySig p.row (rowBody L h p)

def rowsBody : Tm [.list .bool] (.prod TRowsW (.list .bool)) :=
  .app (manyF L (rowF L h p) p.rStep p.rFold p.rMany) (.app (hdrF L h) v0)
def rowsF : FnSig (.list .bool) (.prod TRowsW (.list .bool)) := bodySig p.rows (rowsBody L h p)

/-- `manyF hdrF`: skip headers. -/
abbrev hdrsF : FnSig (.prod .nat (.list .bool)) (.prod (.list .nat) (.list .bool)) :=
  manyF L (hdrF L h) p.hStep p.hFold p.hMany

def precBody : Tm [.list .bool] (.prod .nat (.prod .nat (.prod .nat (.prod .nat (.list .bool))))) :=
  .letE (.app (hdrF L h) v0) <|
  .letE (.app (hdrF L h) (.snd v0)) <|
  .letE (.app (hdrF L h) (.snd v0)) <|
  .letE (.app (hdrF L h) (.snd v0)) <|
  .pair (.fst v3) (.pair (.fst v2) (.pair (.fst v1) (.pair (.fst v0) (.snd v0))))
def precF : FnSig (.list .bool) (.prod .nat (.prod .nat (.prod .nat (.prod .nat (.list .bool))))) :=
  bodySig p.prec (precBody L h)

def parseBody : Tm [.list .bool] TParsed :=
  .letE (.app (hdrF L h) v0) <|
  .letE (.app (rowsF L h p) (.snd (.app (hdrF L h) (.snd v0)))) <|
  .letE (.app (hdrsF L h p) (.pair (.app (succF L.succ) (.fst v1)) (.snd v0))) <|
  .pair (.fst v2) (.pair (.fst v1) (.app (precF L h p) (.snd v0)))
def parseF : FnSig (.list .bool) TParsed := bodySig p.parse (parseBody L h p)

/-! ### Meaning -/

theorem rowF_den (bs : List Bool) : (rowF L h p).den bs = rowR bs := by
  simp only [rowF, bodySig_den, rowBody, tm_simp, hdrF_den]
  rw [manyF_den, show (coordF L h).den = coordR from funext (coordF_den L h)]
  rfl

theorem rowsF_den (bs : List Bool) : (rowsF L h p).den bs = rowsR bs := by
  simp only [rowsF, bodySig_den, rowsBody, tm_simp, hdrF_den]
  rw [manyF_den, show (rowF L h p).den = rowR from funext (rowF_den L h p)]
  rfl

theorem hdrsF_den (k : ℕ) (bs : List Bool) : (hdrsF L h p).den (k, bs) = many hdr k bs := by
  rw [manyF_den, show (hdrF L h).den = hdr from funext (hdrF_den L h)]

theorem precF_den (bs : List Bool) : (precF L h p).den bs = precR bs := by
  simp only [precF, bodySig_den, precBody, tm_simp, hdrF_den]
  rfl

theorem parseF_den (bs : List Bool) : (parseF L h p).den bs = parse bs := by
  simp only [parseF, bodySig_den, parseBody, tm_simp, hdrF_den, rowsF_den, succF_den]
  rw [hdrsF_den, precF_den]
  rfl

/-- **The FL parser on the machine input.** -/
theorem parseF_problemBits {n : ℕ} (rows : List (List (PauliCoord n))) (a b c d : ℕ)
    (coins : List Bool) :
    (parseF L h p).den
        (InputEncoding.problemBits rows (ZeroLengthDispatch.iidProgram n) a b c d ++ coins) =
      (n, Query.encRows rows, a, b, c, d, coins) := by
  rw [parseF_den, parse_problemBits]

/-! ### Validity -/

/-- The parser bodies are installed at their indices. -/
structure PIx.OK (P : Program) : Prop where
  cStep : P[p.cStep]? = some (manyStepBody (coordF L h)).compile
  cFold : P[p.cFold]? = some (foldlBody (manyStepF (coordF L h) p.cStep) p.cFold).compile
  cMany : P[p.cMany]? = some (manyBody L (coordF L h) p.cStep p.cFold).compile
  row : P[p.row]? = some (rowBody L h p).compile
  rStep : P[p.rStep]? = some (manyStepBody (rowF L h p)).compile
  rFold : P[p.rFold]? = some (foldlBody (manyStepF (rowF L h p) p.rStep) p.rFold).compile
  rMany : P[p.rMany]? = some (manyBody L (rowF L h p) p.rStep p.rFold).compile
  rows : P[p.rows]? = some (rowsBody L h p).compile
  hStep : P[p.hStep]? = some (manyStepBody (hdrF L h)).compile
  hFold : P[p.hFold]? = some (foldlBody (manyStepF (hdrF L h) p.hStep) p.hFold).compile
  hMany : P[p.hMany]? = some (manyBody L (hdrF L h) p.hStep p.hFold).compile
  prec : P[p.prec]? = some (precBody L h).compile
  parse : P[p.parse]? = some (parseBody L h p).compile

section Valid
variable {L h p} {P : Program} (hL : L.OK P) (hH : h.OK L P) (hp : p.OK L h P)
include hL hH hp

theorem row_valid : ∀ x, (rowF L h p).ValidAt P x := fun x => by
  have hm := many_valid hL (coord_valid hL hH) hp.cStep hp.cFold hp.cMany
  exact bodySig_valid hp.row (by simp [tm_simp, rowBody, hm, hdr_valid hL hH])

theorem rows_valid : ∀ x, (rowsF L h p).ValidAt P x := fun x => by
  have hm := many_valid hL (row_valid hL hH hp) hp.rStep hp.rFold hp.rMany
  exact bodySig_valid hp.rows (by simp [tm_simp, rowsBody, hm, hdr_valid hL hH])

theorem hdrs_valid : ∀ x, (hdrsF L h p).ValidAt P x :=
  many_valid hL (hdr_valid hL hH) hp.hStep hp.hFold hp.hMany

theorem prec_valid : ∀ x, (precF L h p).ValidAt P x := fun x =>
  bodySig_valid hp.prec (by simp [tm_simp, precBody, hdr_valid hL hH])

theorem parse_valid : ∀ x, (parseF L h p).ValidAt P x := fun x =>
  bodySig_valid hp.parse (by
    simp [tm_simp, parseBody, hdr_valid hL hH, rows_valid hL hH hp, hdrs_valid hL hH hp,
      prec_valid hL hH hp, hL.succ])

end Valid

end QecReliability.Trans.Wire
