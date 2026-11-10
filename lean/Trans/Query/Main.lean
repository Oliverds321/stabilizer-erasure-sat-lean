import Trans.Query.FLLayer
import Trans.Query.CorrLayer

/-!
# Trans.Query.Main: the query bits as one FL function

* `queryFnF stdIx : FnSig TQueryArg (list bool)`: `(false, args) ↦ Plain.baseQuery …`,
  `(true, args) ↦ Plain.cellQuery …` (`queryBits`).
* `queryProg : Program`, `stdIx : Ix`: the concrete program (95 bodies) and its index table;
  `hP_*` check every body is at its index (`rfl`).
* `queryFn_valid : ∀ p, (queryFnF stdIx).ValidAt queryProg p`.
* `queryFn_base`, `queryFn_cell`: on the encoded inputs, `(queryFnF stdIx).den` is the controller's
  `Final.concreteQuery` (the cell query takes the hash program `K.program s ω` as input).

The cost/depth/msize of `queryFnF` are the exact compositional bounds of the bodies
(`FnSig.exact`) and of the recursive signatures; closed-form bounds: `Trans/Query/Bounds.lean`.

-/

set_option autoImplicit false

namespace QecReliability.Trans.Query
open QecReliability.FL QecReliability.FL.Lib Tm NatSize

/-- Argument of `queryFn`: `(isCell, (n, (r, (rows, (C, (side, (j, (H, (target, (pre, D))))))))))`;
for a base query `H` and `target` are ignored. -/
scoped notation "TQueryArg" => Ty.prod Ty.bool TCellQArg

/-- The query bits on plain data. -/
def queryBits (p : (TQueryArg).den) : List Bool :=
  if p.1 then
    Plain.cellQuery p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1
      p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2
  else
    Plain.baseQuery p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1
      p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2

def queryFnBody (x : Ix) : Tm [TQueryArg] TBits :=
  .ite (.fst v0) (.app (cellQueryF x) (.snd v0))
    (.app (baseQueryF x)
      (.pair (.fst (.snd v0)) (.pair (.fst (.snd (.snd v0))) (.pair (.fst (.snd (.snd (.snd v0))))
        (.pair (.fst (.snd (.snd (.snd (.snd v0))))) (.pair (.fst (.snd (.snd (.snd (.snd (.snd v0))))))
          (.pair (.fst (.snd (.snd (.snd (.snd (.snd (.snd v0)))))))
            (.pair (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd v0))))))))))
              (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd v0))))))))))))))))))

def queryFnF (x : Ix) : FnSig TQueryArg TBits := FnSig.exact x.queryFn (queryFnBody x) queryBits

@[simp] theorem queryFnF_den (x : Ix) (p : (TQueryArg).den) : (queryFnF x).den p = queryBits p := rfl

theorem queryFn_body_valid {P : Program} {x : Ix} (hc : ∀ p, (cellQueryF x).ValidAt P p)
    (hb : ∀ p, (baseQueryF x).ValidAt P p)
    (hP : P[x.queryFn]? = some (queryFnBody x).compile) : ∀ p, (queryFnF x).ValidAt P p :=
  FnSig.exact_valid hP
    (fun p => by obtain ⟨c, q⟩ := p; cases c <;> simp [tm_simp, queryFnBody, hc, hb])
    (fun p => by obtain ⟨c, q⟩ := p; cases c <;> simp [tm_simp, queryFnBody, queryBits])

/-! ## The concrete program -/

/-- The concrete index assignment (index = position in `queryProg`). -/
def stdIx : Ix where
  succ := 0
  pred := 1
  addc := 2
  add := 3
  subb := 4
  sub := 5
  le := 6
  lt := 7
  eq := 8
  max := 9
  mul := 10
  bitLen := 11
  div2 := 12
  length := 13
  append := 14
  replicate := 15
  getD := 16
  take := 17
  drop := 18
  rangeFrom := 19
  range := 20
  word := 21
  natHeader := 22
  literal := 23
  literals := 24
  clause := 25
  body := 26
  encode := 27
  shiftWire := 28
  litS := 29
  clauseS := 30
  formS := 31
  tableWire := 32
  litT := 33
  clauseT := 34
  formT := 35
  gateS := 36
  gatesS := 37
  wiresS := 38
  gateClauses := 39
  compileAt := 40
  blockAnd := 41
  blockMerge := 42
  outputUnits := 43
  matchBlock := 44
  coordWire := 45
  rowWires := 46
  rowsWires := 47
  parityGates := 48
  rowBlock := 49
  rowBlocks := 50
  nonempty := 51
  filterNonempty := 52
  filterNonemptyC := 53
  normalizer := 54
  productParityGates := 55
  offsetPair := 56
  offsetPairs := 57
  pairingPairs := 58
  supportPairs := 59
  supportClause := 60
  supportClauses := 61
  pairingBlock := 62
  badBlock := 63
  set := 64
  recZero := 65
  recAddInc := 66
  recAddRow := 67
  synthesize := 68
  condEq := 69
  condEqs := 70
  cleaning := 71
  goodBlock := 72
  adderGates := 73
  ripple := 74
  countTree := 75
  treeCombine := 76
  treeSplit := 77
  pow2Size := 78
  paddedWires := 79
  population := 80
  weightBlock := 81
  pullback := 82
  layerBlock := 83
  witness := 84
  quantumBlock := 85
  quantumLayer := 86
  hashCell := 87
  quantumCell := 88
  units := 89
  request := 90
  query := 91
  baseQuery := 92
  cellQuery := 93
  queryFn := 94

/-- The FL program of the query transcription. -/
def queryProg : Program := [
  (succBody stdIx.succ).compile,
  (predBody stdIx.pred).compile,
  (addcBody stdIx.succ stdIx.addc).compile,
  (addBody stdIx.addc).compile,
  (subbBody stdIx.pred stdIx.subb).compile,
  (subBody stdIx.subb).compile,
  (leBody stdIx.subb).compile,
  (ltBody stdIx.subb).compile,
  (eqBody stdIx.subb).compile,
  (maxBody stdIx.subb).compile,
  (mulBody stdIx.add stdIx.mul).compile,
  (bitLenBody stdIx.succ stdIx.bitLen).compile,
  (div2Body).compile,
  (lengthBody .nat stdIx.succ stdIx.length).compile,
  (appendBody .nat stdIx.append).compile,
  (replicateBody .nat stdIx.pred stdIx.replicate).compile,
  (getDBody .nat stdIx.pred stdIx.getD).compile,
  (takeBody .nat stdIx.pred stdIx.take).compile,
  (dropBody .nat stdIx.pred stdIx.drop).compile,
  (rangeFromBody stdIx.succ stdIx.pred stdIx.rangeFrom).compile,
  (rangeBody stdIx.rangeFrom).compile,
  (wordBody stdIx.pred stdIx.word).compile,
  (natHeaderBody stdIx.bitLen stdIx.replicate stdIx.append stdIx.word).compile,
  (literalBody stdIx.word).compile,
  (flatMapEnvBody (literalF stdIx.literal) stdIx.append stdIx.literals).compile,
  (clauseBody stdIx.literal stdIx.literals stdIx.length stdIx.word stdIx.append).compile,
  (flatMapEnvBody (clauseF stdIx.literal stdIx.literals stdIx.clause) stdIx.append stdIx.body).compile,
  (encodeBody stdIx.literal stdIx.literals stdIx.clause stdIx.body stdIx.natHeader stdIx.length stdIx.bitLen stdIx.append).compile,
  (shiftWireBody stdIx).compile,
  (litSBody stdIx).compile,
  (mapEnvBody (litSF stdIx) stdIx.clauseS).compile,
  (mapEnvBody (clauseSF stdIx) stdIx.formS).compile,
  (tableWireBody stdIx).compile,
  (litTBody stdIx).compile,
  (mapEnvBody (litTF stdIx) stdIx.clauseT).compile,
  (mapEnvBody (clauseTF stdIx) stdIx.formT).compile,
  (gateSBody stdIx).compile,
  (mapEnvBody (gateSF stdIx) stdIx.gatesS).compile,
  (mapEnvBody (shiftWireF stdIx) stdIx.wiresS).compile,
  (gateClausesBody).compile,
  (compileAtBody stdIx).compile,
  (blockAndBody stdIx).compile,
  (blockMergeBody stdIx).compile,
  (outputUnitsBody stdIx).compile,
  (matchBlockBody stdIx).compile,
  (coordWireBody stdIx).compile,
  (mapEnvBody (coordWireF stdIx) stdIx.rowWires).compile,
  (mapEnvBody (rowWiresF stdIx) stdIx.rowsWires).compile,
  (parityGatesBody stdIx).compile,
  (rowBlockBody stdIx).compile,
  (mapEnvBody (rowBlockF stdIx) stdIx.rowBlocks).compile,
  (nonemptyBody .nat).compile,
  (filterBody (nonemptyF .nat stdIx) stdIx.filterNonempty).compile,
  (filterBody (nonemptyF TCoord stdIx) stdIx.filterNonemptyC).compile,
  (normalizerBody stdIx).compile,
  (productParityGatesBody stdIx).compile,
  (offsetPairBody stdIx).compile,
  (mapEnvBody (offsetPairF stdIx) stdIx.offsetPairs).compile,
  (pairingPairsBody stdIx).compile,
  (supportPairsBody stdIx).compile,
  (supportClauseBody).compile,
  (mapBody (supportClauseF stdIx) stdIx.supportClauses).compile,
  (pairingBlockBody stdIx).compile,
  (badBlockBody stdIx).compile,
  (setBody stdIx).compile,
  (recZeroBody stdIx).compile,
  (recAddIncBody stdIx).compile,
  (recAddRowBody stdIx).compile,
  (synthesizeBody stdIx).compile,
  (condEqBody).compile,
  (condEqsBody stdIx).compile,
  (cleaningBody stdIx).compile,
  (goodBlockBody stdIx).compile,
  (adderGatesBody stdIx).compile,
  (rippleBody stdIx).compile,
  (countTreeBody stdIx).compile,
  (treeCombineBody stdIx).compile,
  (treeSplitBody stdIx).compile,
  (pow2SizeBody stdIx).compile,
  (paddedWiresBody stdIx).compile,
  (populationBody stdIx).compile,
  (weightBlockBody stdIx).compile,
  (pullbackBody stdIx).compile,
  (layerBlockBody stdIx).compile,
  (witnessBody stdIx).compile,
  (quantumBlockBody stdIx).compile,
  (quantumLayerBody stdIx).compile,
  (hashCellBody stdIx).compile,
  (quantumCellBody stdIx).compile,
  (unitsBody stdIx).compile,
  (requestBody stdIx).compile,
  (queryBody stdIx).compile,
  (baseQueryBody stdIx).compile,
  (cellQueryBody stdIx).compile,
  (queryFnBody stdIx).compile]

theorem hP_succ : queryProg[stdIx.succ]? = some (succBody stdIx.succ).compile := rfl
theorem hP_pred : queryProg[stdIx.pred]? = some (predBody stdIx.pred).compile := rfl
theorem hP_addc : queryProg[stdIx.addc]? = some (addcBody stdIx.succ stdIx.addc).compile := rfl
theorem hP_add : queryProg[stdIx.add]? = some (addBody stdIx.addc).compile := rfl
theorem hP_subb : queryProg[stdIx.subb]? = some (subbBody stdIx.pred stdIx.subb).compile := rfl
theorem hP_sub : queryProg[stdIx.sub]? = some (subBody stdIx.subb).compile := rfl
theorem hP_le : queryProg[stdIx.le]? = some (leBody stdIx.subb).compile := rfl
theorem hP_lt : queryProg[stdIx.lt]? = some (ltBody stdIx.subb).compile := rfl
theorem hP_eq : queryProg[stdIx.eq]? = some (eqBody stdIx.subb).compile := rfl
theorem hP_max : queryProg[stdIx.max]? = some (maxBody stdIx.subb).compile := rfl
theorem hP_mul : queryProg[stdIx.mul]? = some (mulBody stdIx.add stdIx.mul).compile := rfl
theorem hP_bitLen : queryProg[stdIx.bitLen]? = some (bitLenBody stdIx.succ stdIx.bitLen).compile := rfl
theorem hP_div2 : queryProg[stdIx.div2]? = some (div2Body).compile := rfl
theorem hP_length : queryProg[stdIx.length]? = some (lengthBody .nat stdIx.succ stdIx.length).compile := rfl
theorem hP_append : queryProg[stdIx.append]? = some (appendBody .nat stdIx.append).compile := rfl
theorem hP_replicate : queryProg[stdIx.replicate]? = some (replicateBody .nat stdIx.pred stdIx.replicate).compile := rfl
theorem hP_getD : queryProg[stdIx.getD]? = some (getDBody .nat stdIx.pred stdIx.getD).compile := rfl
theorem hP_take : queryProg[stdIx.take]? = some (takeBody .nat stdIx.pred stdIx.take).compile := rfl
theorem hP_drop : queryProg[stdIx.drop]? = some (dropBody .nat stdIx.pred stdIx.drop).compile := rfl
theorem hP_rangeFrom : queryProg[stdIx.rangeFrom]? = some (rangeFromBody stdIx.succ stdIx.pred stdIx.rangeFrom).compile := rfl
theorem hP_range : queryProg[stdIx.range]? = some (rangeBody stdIx.rangeFrom).compile := rfl
theorem hP_word : queryProg[stdIx.word]? = some (wordBody stdIx.pred stdIx.word).compile := rfl
theorem hP_natHeader : queryProg[stdIx.natHeader]? = some (natHeaderBody stdIx.bitLen stdIx.replicate stdIx.append stdIx.word).compile := rfl
theorem hP_literal : queryProg[stdIx.literal]? = some (literalBody stdIx.word).compile := rfl
theorem hP_literals : queryProg[stdIx.literals]? = some (flatMapEnvBody (literalF stdIx.literal) stdIx.append stdIx.literals).compile := rfl
theorem hP_clause : queryProg[stdIx.clause]? = some (clauseBody stdIx.literal stdIx.literals stdIx.length stdIx.word stdIx.append).compile := rfl
theorem hP_body : queryProg[stdIx.body]? = some (flatMapEnvBody (clauseF stdIx.literal stdIx.literals stdIx.clause) stdIx.append stdIx.body).compile := rfl
theorem hP_encode : queryProg[stdIx.encode]? = some (encodeBody stdIx.literal stdIx.literals stdIx.clause stdIx.body stdIx.natHeader stdIx.length stdIx.bitLen stdIx.append).compile := rfl
theorem hP_shiftWire : queryProg[stdIx.shiftWire]? = some (shiftWireBody stdIx).compile := rfl
theorem hP_litS : queryProg[stdIx.litS]? = some (litSBody stdIx).compile := rfl
theorem hP_clauseS : queryProg[stdIx.clauseS]? = some (mapEnvBody (litSF stdIx) stdIx.clauseS).compile := rfl
theorem hP_formS : queryProg[stdIx.formS]? = some (mapEnvBody (clauseSF stdIx) stdIx.formS).compile := rfl
theorem hP_tableWire : queryProg[stdIx.tableWire]? = some (tableWireBody stdIx).compile := rfl
theorem hP_litT : queryProg[stdIx.litT]? = some (litTBody stdIx).compile := rfl
theorem hP_clauseT : queryProg[stdIx.clauseT]? = some (mapEnvBody (litTF stdIx) stdIx.clauseT).compile := rfl
theorem hP_formT : queryProg[stdIx.formT]? = some (mapEnvBody (clauseTF stdIx) stdIx.formT).compile := rfl
theorem hP_gateS : queryProg[stdIx.gateS]? = some (gateSBody stdIx).compile := rfl
theorem hP_gatesS : queryProg[stdIx.gatesS]? = some (mapEnvBody (gateSF stdIx) stdIx.gatesS).compile := rfl
theorem hP_wiresS : queryProg[stdIx.wiresS]? = some (mapEnvBody (shiftWireF stdIx) stdIx.wiresS).compile := rfl
theorem hP_gateClauses : queryProg[stdIx.gateClauses]? = some (gateClausesBody).compile := rfl
theorem hP_compileAt : queryProg[stdIx.compileAt]? = some (compileAtBody stdIx).compile := rfl
theorem hP_blockAnd : queryProg[stdIx.blockAnd]? = some (blockAndBody stdIx).compile := rfl
theorem hP_blockMerge : queryProg[stdIx.blockMerge]? = some (blockMergeBody stdIx).compile := rfl
theorem hP_outputUnits : queryProg[stdIx.outputUnits]? = some (outputUnitsBody stdIx).compile := rfl
theorem hP_matchBlock : queryProg[stdIx.matchBlock]? = some (matchBlockBody stdIx).compile := rfl
theorem hP_coordWire : queryProg[stdIx.coordWire]? = some (coordWireBody stdIx).compile := rfl
theorem hP_rowWires : queryProg[stdIx.rowWires]? = some (mapEnvBody (coordWireF stdIx) stdIx.rowWires).compile := rfl
theorem hP_rowsWires : queryProg[stdIx.rowsWires]? = some (mapEnvBody (rowWiresF stdIx) stdIx.rowsWires).compile := rfl
theorem hP_parityGates : queryProg[stdIx.parityGates]? = some (parityGatesBody stdIx).compile := rfl
theorem hP_rowBlock : queryProg[stdIx.rowBlock]? = some (rowBlockBody stdIx).compile := rfl
theorem hP_rowBlocks : queryProg[stdIx.rowBlocks]? = some (mapEnvBody (rowBlockF stdIx) stdIx.rowBlocks).compile := rfl
theorem hP_nonempty : queryProg[stdIx.nonempty]? = some (nonemptyBody .nat).compile := rfl
theorem hP_filterNonempty : queryProg[stdIx.filterNonempty]? = some (filterBody (nonemptyF .nat stdIx) stdIx.filterNonempty).compile := rfl
theorem hP_filterNonemptyC : queryProg[stdIx.filterNonemptyC]? = some (filterBody (nonemptyF TCoord stdIx) stdIx.filterNonemptyC).compile := rfl
theorem hP_normalizer : queryProg[stdIx.normalizer]? = some (normalizerBody stdIx).compile := rfl
theorem hP_productParityGates : queryProg[stdIx.productParityGates]? = some (productParityGatesBody stdIx).compile := rfl
theorem hP_offsetPair : queryProg[stdIx.offsetPair]? = some (offsetPairBody stdIx).compile := rfl
theorem hP_offsetPairs : queryProg[stdIx.offsetPairs]? = some (mapEnvBody (offsetPairF stdIx) stdIx.offsetPairs).compile := rfl
theorem hP_pairingPairs : queryProg[stdIx.pairingPairs]? = some (pairingPairsBody stdIx).compile := rfl
theorem hP_supportPairs : queryProg[stdIx.supportPairs]? = some (supportPairsBody stdIx).compile := rfl
theorem hP_supportClause : queryProg[stdIx.supportClause]? = some (supportClauseBody).compile := rfl
theorem hP_supportClauses : queryProg[stdIx.supportClauses]? = some (mapBody (supportClauseF stdIx) stdIx.supportClauses).compile := rfl
theorem hP_pairingBlock : queryProg[stdIx.pairingBlock]? = some (pairingBlockBody stdIx).compile := rfl
theorem hP_badBlock : queryProg[stdIx.badBlock]? = some (badBlockBody stdIx).compile := rfl
theorem hP_set : queryProg[stdIx.set]? = some (setBody stdIx).compile := rfl
theorem hP_recZero : queryProg[stdIx.recZero]? = some (recZeroBody stdIx).compile := rfl
theorem hP_recAddInc : queryProg[stdIx.recAddInc]? = some (recAddIncBody stdIx).compile := rfl
theorem hP_recAddRow : queryProg[stdIx.recAddRow]? = some (recAddRowBody stdIx).compile := rfl
theorem hP_synthesize : queryProg[stdIx.synthesize]? = some (synthesizeBody stdIx).compile := rfl
theorem hP_condEq : queryProg[stdIx.condEq]? = some (condEqBody).compile := rfl
theorem hP_condEqs : queryProg[stdIx.condEqs]? = some (condEqsBody stdIx).compile := rfl
theorem hP_cleaning : queryProg[stdIx.cleaning]? = some (cleaningBody stdIx).compile := rfl
theorem hP_goodBlock : queryProg[stdIx.goodBlock]? = some (goodBlockBody stdIx).compile := rfl
theorem hP_adderGates : queryProg[stdIx.adderGates]? = some (adderGatesBody stdIx).compile := rfl
theorem hP_ripple : queryProg[stdIx.ripple]? = some (rippleBody stdIx).compile := rfl
theorem hP_countTree : queryProg[stdIx.countTree]? = some (countTreeBody stdIx).compile := rfl
theorem hP_treeCombine : queryProg[stdIx.treeCombine]? = some (treeCombineBody stdIx).compile := rfl
theorem hP_treeSplit : queryProg[stdIx.treeSplit]? = some (treeSplitBody stdIx).compile := rfl
theorem hP_pow2Size : queryProg[stdIx.pow2Size]? = some (pow2SizeBody stdIx).compile := rfl
theorem hP_paddedWires : queryProg[stdIx.paddedWires]? = some (paddedWiresBody stdIx).compile := rfl
theorem hP_population : queryProg[stdIx.population]? = some (populationBody stdIx).compile := rfl
theorem hP_weightBlock : queryProg[stdIx.weightBlock]? = some (weightBlockBody stdIx).compile := rfl
theorem hP_pullback : queryProg[stdIx.pullback]? = some (pullbackBody stdIx).compile := rfl
theorem hP_layerBlock : queryProg[stdIx.layerBlock]? = some (layerBlockBody stdIx).compile := rfl
theorem hP_witness : queryProg[stdIx.witness]? = some (witnessBody stdIx).compile := rfl
theorem hP_quantumBlock : queryProg[stdIx.quantumBlock]? = some (quantumBlockBody stdIx).compile := rfl
theorem hP_quantumLayer : queryProg[stdIx.quantumLayer]? = some (quantumLayerBody stdIx).compile := rfl
theorem hP_hashCell : queryProg[stdIx.hashCell]? = some (hashCellBody stdIx).compile := rfl
theorem hP_quantumCell : queryProg[stdIx.quantumCell]? = some (quantumCellBody stdIx).compile := rfl
theorem hP_units : queryProg[stdIx.units]? = some (unitsBody stdIx).compile := rfl
theorem hP_request : queryProg[stdIx.request]? = some (requestBody stdIx).compile := rfl
theorem hP_query : queryProg[stdIx.query]? = some (queryBody stdIx).compile := rfl
theorem hP_baseQuery : queryProg[stdIx.baseQuery]? = some (baseQueryBody stdIx).compile := rfl
theorem hP_cellQuery : queryProg[stdIx.cellQuery]? = some (cellQueryBody stdIx).compile := rfl
theorem hP_queryFn : queryProg[stdIx.queryFn]? = some (queryFnBody stdIx).compile := rfl

/-! ## Validity of every function of `queryProg` -/

theorem stdLib_valid : LibOK queryProg stdIx := by
  have hsucc := succ_valid (P := queryProg) hP_succ
  have hpred := pred_valid (P := queryProg) hP_pred
  have haddc := addc_valid hsucc hP_addc
  have hadd := add_valid haddc hP_add
  have hsubb := subb_valid hpred hP_subb
  exact ⟨hsucc, hpred, hadd, sub_valid hsubb hP_sub, le_valid hsubb hP_le, lt_valid hsubb hP_lt,
    eq_valid hsubb hP_eq, max_valid hsubb hP_max, mul_valid hadd hP_mul,
    bitLen_valid hsucc hP_bitLen, div2_valid hP_div2,
    fun _ => length_valid hsucc hP_length, fun _ => append_valid hP_append,
    fun _ => replicate_valid hpred hP_replicate, fun _ => getD_valid hpred hP_getD,
    fun _ => take_valid hpred hP_take, fun _ => drop_valid hpred hP_drop,
    rangeFrom_valid hsucc hpred hP_rangeFrom,
    range_valid (rangeFrom_valid hsucc hpred hP_rangeFrom) hP_range⟩

/-- The building blocks shared by the base and cell queries. -/
theorem std_core_valid :
    (∀ p, (encodeX stdIx).ValidAt queryProg p) ∧ (∀ p, (quantumLayerF stdIx).ValidAt queryProg p) ∧
    (∀ p, (quantumCellF stdIx).ValidAt queryProg p) ∧ (∀ p, (witnessF stdIx).ValidAt queryProg p) ∧
    (∀ p, (requestF stdIx).ValidAt queryProg p) := by
  have hL := stdLib_valid
  -- serialization
  have hword := word_valid hL.pred hP_word
  have hnatHeader := natHeader_valid hL.bitLen (hL.replicate .bool) (hL.append .bool) hword hP_natHeader
  have hliteral := literal_valid hword hP_literal
  have hliterals := literals_valid hliteral (hL.append .bool) hP_literals
  have hclause := clause_valid hliterals (hL.length _) hword (hL.append .bool) hP_clause
  have hbody := body_valid hclause (hL.append .bool) hP_body
  have hencode := encode_valid hbody hnatHeader (hL.length _) hL.bitLen (hL.append .bool) hP_encode
  -- circuits and blocks
  have hshiftWire := shiftWire_valid hL hP_shiftWire
  have hlitS := litS_valid hshiftWire hP_litS
  have hclauseS := clauseS_valid hlitS hP_clauseS
  have hformS := formS_valid hclauseS hP_formS
  have htableWire := tableWire_valid hL hP_tableWire
  have hlitT := litT_valid htableWire hP_litT
  have hclauseT := clauseT_valid hlitT hP_clauseT
  have hformT := formT_valid hclauseT hP_formT
  have hgateS := gateS_valid hshiftWire hP_gateS
  have hgatesS := gatesS_valid hgateS hP_gatesS
  have hwiresS := wiresS_valid hshiftWire hP_wiresS
  have hgateClauses := gateClauses_valid hP_gateClauses
  have hcompileAt := compileAt_valid hL hgateClauses hP_compileAt
  have hblockAnd := blockAnd_valid hL hformS hP_blockAnd
  have hblockMerge := blockMerge_valid hblockAnd hP_blockMerge
  have houtputUnits := outputUnits_valid hP_outputUnits
  have hmatchBlock := matchBlock_valid hL hcompileAt houtputUnits hP_matchBlock
  -- Bad block
  have hcoordWire := coordWire_valid hL hP_coordWire
  have hrowWires := rowWires_valid hcoordWire hP_rowWires
  have hrowsWires := rowsWires_valid hrowWires hP_rowsWires
  have hparity := parityGates_valid hL hP_parityGates
  have hrowBlock := rowBlock_valid hL hcompileAt hparity hP_rowBlock
  have hrowBlocks := rowBlocks_valid hrowBlock hP_rowBlocks
  have hnonemptyN := nonempty_valid (t := .nat) hP_nonempty
  have hnonemptyC := nonempty_valid (t := TCoord) hP_nonempty
  have hfilterNonempty := filterNonempty_valid hnonemptyN hP_filterNonempty
  have hnormalizer := normalizer_valid hblockMerge hrowBlocks hfilterNonempty hrowsWires hP_normalizer
  have hpp := productParityGates_valid hL hP_productParityGates
  have hoffsetPair := offsetPair_valid hL hP_offsetPair
  have hoffsetPairs := offsetPairs_valid hoffsetPair hP_offsetPairs
  have hpairingPairs := pairingPairs_valid hL hoffsetPairs hP_pairingPairs
  have hsupportPairs := supportPairs_valid hL hoffsetPairs hP_supportPairs
  have hsupportClause := supportClause_valid hP_supportClause
  have hsupportClauses := supportClauses_valid hsupportClause hP_supportClauses
  have hpairingBlock := pairingBlock_valid hL hcompileAt hpp hP_pairingBlock
  have hbad := badBlock_valid hL hblockAnd hnormalizer hsupportClauses hsupportPairs hpairingBlock
    hpairingPairs hP_badBlock
  -- Good block
  have hset := set_valid hL hP_set
  have hrecZero := recZero_valid hL hP_recZero
  have hrecAddInc := recAddInc_valid hL hset hP_recAddInc
  have hrecAddRow := recAddRow_valid hrecAddInc hP_recAddRow
  have hsynth := synthesize_valid hL hrecZero hrecAddRow hP_synthesize
  have hcondEq := condEq_valid hP_condEq
  have hcondEqs := condEqs_valid hL hcondEq hP_condEqs
  have hcleaning := cleaning_valid hL hcompileAt hcondEqs hP_cleaning
  have hfilterC := filterNonemptyC_valid hnonemptyC hP_filterNonemptyC
  have hgood := goodBlock_valid hL hblockAnd hnormalizer hcleaning hsynth hfilterC hP_goodBlock
  -- population counter
  have hadder := adderGates_valid hL hP_adderGates
  have hripple := ripple_valid hL hadder hP_ripple
  have hsplit := treeSplit_valid hL hP_treeSplit
  have hcombine := treeCombine_valid hL hgatesS hwiresS hripple hP_treeCombine
  have hcount := countTree_valid hsplit hcombine hP_countTree
  have hpow := pow2Size_valid hP_pow2Size
  have hpadded := paddedWires_valid hL hpow hP_paddedWires
  have hpop := population_valid hL hcount hpadded hP_population
  have hweight := weightBlock_valid hL hpop hmatchBlock hgatesS hwiresS hword hP_weightBlock
  -- layer, cell, request
  have hpull := pullback_valid hL hgatesS hwiresS hcompileAt hformT hP_pullback
  have hlayer := layerBlock_valid hL hblockAnd hpull hweight hP_layerBlock
  have hwit := witness_valid hL hfilterC hP_witness
  have hqb := quantumBlock_valid hgood hbad hP_quantumBlock
  have hql := quantumLayer_valid hlayer hwit hqb hP_quantumLayer
  have hhash := hashCell_valid hL hblockAnd hmatchBlock hgatesS hwiresS hP_hashCell
  have hqc := quantumCell_valid hL hhash hwit hql hP_quantumCell
  have hunits := units_valid hL hP_units
  have hreq := request_valid hL hunits hP_request
  exact ⟨hencode, hql, hqc, hwit, hreq⟩

/-- **Validity of the query transcription**: every call of `queryFnF stdIx` in `queryProg`
evaluates to the encoded `queryBits` within its bounds. -/
theorem queryFn_valid : ∀ p, (queryFnF stdIx).ValidAt queryProg p := by
  have hL := stdLib_valid
  obtain ⟨hencode, hql, hqc, hwit, hreq⟩ := std_core_valid
  have hquery := query_valid hL hencode hP_query
  have hbase := baseQuery_valid hL hquery hreq hwit hql hP_baseQuery
  have hcell := cellQuery_valid hL hquery hreq hwit hqc hP_cellQuery
  exact queryFn_body_valid hcell hbase hP_queryFn

/-! ## The controller's query bits -/

section Final
open QecReliability.SharedCircuit QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate
open QecReliability.SharedCircuit.LatentEncoding

variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (H : HashStages Ω (Binary.CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r))
    (m : ℕ) (ω : Fin (2 * m + 1) → Ω) (D : ℕ)

/-- The FL argument of a base request key (`H`, `target` unused). -/
def baseArg (side : Bool) (j : ℕ) : (TQueryArg).den :=
  (false, n, r, encRows rows, encProg C, side, j, ([], []), [], [], D)

/-- The FL argument of a cell request key, with the already computed hash program. -/
def cellArg (side : Bool) (j : ℕ) (Hs : Plain.ProgP) (scale : ℕ) (pre : List Bool) : (TQueryArg).den :=
  (true, n, r, encRows rows, encProg C, side, j, Hs, List.replicate scale false, pre, D)

theorem queryFn_base (side : Bool) (j rep : ℕ) (valid : ValidKey (keySize n r) r m (.base side j rep)) :
    (queryFnF stdIx).den (baseArg rows C D side j) =
      Final.concreteQuery rows C H K m ω D (.base side j rep) := by
  rw [concreteQuery_base rows C H K m ω D side j rep valid]
  rfl

theorem queryFn_cell (side : Bool) (j rep scale : ℕ) (pre : List Bool)
    (valid : ValidKey (keySize n r) r m (.cell side j rep scale pre)) :
    (queryFnF stdIx).den (cellArg rows C D side j
        (encProg (K.program ⟨scale, valid.2.2.1⟩ (ω ⟨rep, valid.2.1⟩))) scale pre) =
      Final.concreteQuery rows C H K m ω D (.cell side j rep scale pre) := by
  rw [concreteQuery_cell rows C H K m ω D side j rep scale pre valid]
  rfl

/-- The register-level contract (`FL.Computes`) of the base query: the FL program `queryProg`,
called at index `stdIx.queryFn` on the encoded key data, returns the encoded query bits. -/
theorem queryFn_computes_base (side : Bool) (j rep : ℕ)
    (valid : ValidKey (keySize n r) r m (.base side j rep)) {mm : ℕ}
    (hm : (queryFnF stdIx).msize (baseArg rows C D side j) ≤ mm)
    (harg : (Ty.enc TQueryArg (baseArg rows C D side j)).size ≤ mm) :
    Computes queryProg stdIx.queryFn (Ty.enc TQueryArg (baseArg rows C D side j))
      (Ty.enc TBits (Final.concreteQuery rows C H K m ω D (.base side j rep))) mm
      ((queryFnF stdIx).cost (baseArg rows C D side j))
      ((queryFnF stdIx).depth (baseArg rows C D side j)) := by
  rw [← queryFn_base rows C H K m ω D side j rep valid]
  exact (queryFn_valid _).computes hm harg

theorem queryFn_computes_cell (side : Bool) (j rep scale : ℕ) (pre : List Bool)
    (valid : ValidKey (keySize n r) r m (.cell side j rep scale pre)) {mm : ℕ}
    (hm : (queryFnF stdIx).msize (cellArg rows C D side j
        (encProg (K.program ⟨scale, valid.2.2.1⟩ (ω ⟨rep, valid.2.1⟩))) scale pre) ≤ mm)
    (harg : (Ty.enc TQueryArg (cellArg rows C D side j
        (encProg (K.program ⟨scale, valid.2.2.1⟩ (ω ⟨rep, valid.2.1⟩))) scale pre)).size ≤ mm) :
    Computes queryProg stdIx.queryFn (Ty.enc TQueryArg (cellArg rows C D side j
        (encProg (K.program ⟨scale, valid.2.2.1⟩ (ω ⟨rep, valid.2.1⟩))) scale pre))
      (Ty.enc TBits (Final.concreteQuery rows C H K m ω D (.cell side j rep scale pre))) mm
      ((queryFnF stdIx).cost (cellArg rows C D side j
        (encProg (K.program ⟨scale, valid.2.2.1⟩ (ω ⟨rep, valid.2.1⟩))) scale pre))
      ((queryFnF stdIx).depth (cellArg rows C D side j
        (encProg (K.program ⟨scale, valid.2.2.1⟩ (ω ⟨rep, valid.2.1⟩))) scale pre)) := by
  rw [← queryFn_cell rows C H K m ω D side j rep scale pre valid]
  exact (queryFn_valid _).computes hm harg

end Final

end QecReliability.Trans.Query
