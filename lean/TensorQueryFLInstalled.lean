import TensorQueryFLValidity
import TensorRepairFLFullInstalled

/-! A fixed installation of the multiclass SAT query compiler, following the
full tensor repair callback. All 373 bodies precede runtime input. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

namespace QecReliability.TensorQuery.FLCompiler
open FL FL.Lib Trans.Query

/-- Every reused query-library component is proved from its installed body.
This exports the full dependency bundle rather than assuming callback meanings. -/
theorem std_dependencies : Dependencies stdIx Trans.Query.queryProg := by
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
  exact ⟨hL,hpop,hgatesS,hwiresS,hword,hmatchBlock,hblockAnd,hwit,hqb,hpull,hhash,hreq,
    Trans.Query.query_valid hL hencode hP_query⟩

 theorem Dependencies.extend {x : Ix} {P P' : FL.Program} (h : Dependencies x P)
    (he : Install.Extends P P') : Dependencies x P' where
  lib := {
    succ := fun p => Install.ValidAt.extend he (h.lib.succ p)
    pred := fun p => Install.ValidAt.extend he (h.lib.pred p)
    add := fun p => Install.ValidAt.extend he (h.lib.add p)
    sub := fun p => Install.ValidAt.extend he (h.lib.sub p)
    le := fun p => Install.ValidAt.extend he (h.lib.le p)
    lt := fun p => Install.ValidAt.extend he (h.lib.lt p)
    eq := fun p => Install.ValidAt.extend he (h.lib.eq p)
    max := fun p => Install.ValidAt.extend he (h.lib.max p)
    mul := fun p => Install.ValidAt.extend he (h.lib.mul p)
    bitLen := fun p => Install.ValidAt.extend he (h.lib.bitLen p)
    div2 := fun p => Install.ValidAt.extend he (h.lib.div2 p)
    length := fun t p => Install.ValidAt.extend he (h.lib.length t p)
    append := fun t p => Install.ValidAt.extend he (h.lib.append t p)
    replicate := fun t p => Install.ValidAt.extend he (h.lib.replicate t p)
    getD := fun t p => Install.ValidAt.extend he (h.lib.getD t p)
    take := fun t p => Install.ValidAt.extend he (h.lib.take t p)
    drop := fun t p => Install.ValidAt.extend he (h.lib.drop t p)
    rangeFrom := fun p => Install.ValidAt.extend he (h.lib.rangeFrom p)
    range := fun p => Install.ValidAt.extend he (h.lib.range p) }
  population := fun p => Install.ValidAt.extend he (h.population p)
  gates := fun p => Install.ValidAt.extend he (h.gates p)
  wires := fun p => Install.ValidAt.extend he (h.wires p)
  word := fun p => Install.ValidAt.extend he (h.word p)
  matchBlock := fun p => Install.ValidAt.extend he (h.matchBlock p)
  blockAnd := fun p => Install.ValidAt.extend he (h.blockAnd p)
  witness := fun p => Install.ValidAt.extend he (h.witness p)
  quantumBlock := fun p => Install.ValidAt.extend he (h.quantumBlock p)
  pullback := fun p => Install.ValidAt.extend he (h.pullback p)
  hashCell := fun p => Install.ValidAt.extend he (h.hashCell p)
  request := fun p => Install.ValidAt.extend he (h.request p)
  serialize := fun p => Install.ValidAt.extend he (h.serialize p)

end QecReliability.TensorQuery.FLCompiler

namespace QecReliability.TensorMachine.QueryInstalled
open FL FL.Lib
open Trans.Query (stdIx)
open Trans.Query.Plain (ProgP)

abbrev indices : TensorQuery.FLCompiler.Indices := TensorQuery.FLCompiler.indices 361
abbrev queryIdx : ℕ := 372
abbrev query := TensorQuery.FLCompiler.queryF stdIx indices

def segment : FL.Program := TensorQuery.FLCompiler.bodies stdIx 361

variable (base den density : ℕ) (E : ℕ × ℕ × ℕ)
  (pg : ℕ → ProgP) (nb : ℕ → ℕ → ℕ → ℕ)

def program : FL.Program := FullRepairInstalled.program base den density E pg nb ++ segment
local notation "PP" => program base den density E pg nb

theorem program_length : (PP).length = 373 := by
  simp only [program,List.length_append,FullRepairInstalled.program_length,segment,TensorQuery.FLCompiler.bodies_length]

theorem extends_repair : Install.Extends
    (FullRepairInstalled.program base den density E pg nb) PP := Install.extends_append _ _

theorem extends_tensor : Install.Extends (Installed.program base den density E pg nb) PP := by
  intro k b hb
  exact extends_repair base den density E pg nb k b
    (FullRepairInstalled.extends_tensor base den density E pg nb k b hb)

theorem extends_prefix : Install.Extends (Install.prog base den density E pg nb) PP := by
  intro k b hb
  exact extends_repair base den density E pg nb k b
    (FullRepairInstalled.extends_prefix base den density E pg nb k b hb)

theorem extends_query : Install.Extends Trans.Query.queryProg PP := by
  intro k b hb
  exact extends_prefix base den density E pg nb k b
    (Install.ext_query base den density E pg nb k b hb)

theorem dependencies : TensorQuery.FLCompiler.Dependencies stdIx PP :=
  TensorQuery.FLCompiler.std_dependencies.extend (extends_query base den density E pg nb)

theorem slots : indices.OK stdIx PP := by
  change (TensorQuery.FLCompiler.indices 361).OK stdIx
    (FullRepairInstalled.program base den density E pg nb ++ TensorQuery.FLCompiler.bodies stdIx 361)
  have h := TensorQuery.FLCompiler.appended_ok stdIx (FullRepairInstalled.program base den density E pg nb)
  simpa only [FullRepairInstalled.program_length] using h

theorem query_valid : ∀ p, query.ValidAt PP p :=
  TensorQuery.FLCompiler.query_valid (dependencies base den density E pg nb) (slots base den density E pg nb)

theorem repair_valid : ∀ p, FullRepairInstalled.callback.ValidAt PP p := fun p =>
  Install.ValidAt.extend (extends_repair base den density E pg nb)
    (FullRepairInstalled.callback_valid base den density E pg nb p)

end QecReliability.TensorMachine.QueryInstalled
