import TensorQueryFLInstalled
import GeneralRepairFL

/-! Fixed installation of the general-circuit callback. Three bodies are appended
after the 373 bodies of `QueryInstalled.program` (indices 373, 374, 375); all are
chosen before any runtime input. The full repair callback remains installed but
is not used by the general controller. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

namespace QecReliability.TensorMachine.GeneralInstalled
open FL FL.Lib TensorMachine.RepairFL TensorMachine.GeneralRepairFL
open Trans.Query.Plain (ProgP)

abbrev ri := FullRepairInstalled.ri
abbrev ci := FullRepairInstalled.ci
abbrev ai := FullRepairInstalled.ai
abbrev wi := FullRepairInstalled.wi
abbrev gi : GeneralIndices := ⟨373,374,375⟩

def segment : FL.Program :=
  [sndStepBody.compile,
   (foldrBody (sndStepF gi) gi.sndFold).compile,
   (generalBody Install.wL ri ci Install.yR ai wi gi).compile]

variable (base den density : ℕ) (E : ℕ × ℕ × ℕ)
  (pg : ℕ → ProgP) (nb : ℕ → ℕ → ℕ → ℕ)

def program : FL.Program := QueryInstalled.program base den density E pg nb ++ segment
local notation "PP" => program base den density E pg nb

theorem program_length : (PP).length = 376 := by
  simp only [program,List.length_append,QueryInstalled.program_length]
  rfl

theorem extends_query : Install.Extends (QueryInstalled.program base den density E pg nb) PP :=
  Install.extends_append _ _

theorem extends_full : Install.Extends (FullRepairInstalled.program base den density E pg nb) PP := by
  intro k b h
  exact extends_query base den density E pg nb k b
    (QueryInstalled.extends_repair base den density E pg nb k b h)

theorem extends_tensor : Install.Extends (Installed.program base den density E pg nb) PP := by
  intro k b h
  exact extends_query base den density E pg nb k b
    (QueryInstalled.extends_tensor base den density E pg nb k b h)

theorem query_valid : ∀ p, QueryInstalled.query.ValidAt PP p := fun p =>
  Install.ValidAt.extend (extends_query base den density E pg nb)
    (QueryInstalled.query_valid base den density E pg nb p)

theorem library_valid : Install.wL.OK PP := by
  have h := FullRepairInstalled.library_valid base den density E pg nb
  have he := extends_full base den density E pg nb
  exact {
    succ := fun x => Install.ValidAt.extend he (h.succ x)
    pred := fun x => Install.ValidAt.extend he (h.pred x)
    add := fun x => Install.ValidAt.extend he (h.add x)
    sub := fun x => Install.ValidAt.extend he (h.sub x)
    le := fun x => Install.ValidAt.extend he (h.le x)
    eq := fun x => Install.ValidAt.extend he (h.eq x)
    mul := fun x => Install.ValidAt.extend he (h.mul x)
    bitLen := fun x => Install.ValidAt.extend he (h.bitLen x)
    dm := fun x hx => Install.ValidAt.extend he (h.dm x hx)
    take := fun t x => Install.ValidAt.extend he (h.take t x)
    drop := fun t x => Install.ValidAt.extend he (h.drop t x)
    rev := fun t x => Install.ValidAt.extend he (h.rev t x)
    rep := fun t x => Install.ValidAt.extend he (h.rep t x)
    range := fun x => Install.ValidAt.extend he (h.range x) }

theorem rank_library_valid : Trans.Control.LibR Install.yR PP := by
  have h := FullRepairInstalled.rank_library_valid base den density E pg nb
  have he := extends_full base den density E pg nb
  exact {
    succ := fun x => Install.ValidAt.extend he (h.succ x)
    add := fun x => Install.ValidAt.extend he (h.add x)
    sub := fun x => Install.ValidAt.extend he (h.sub x)
    eq := fun x => Install.ValidAt.extend he (h.eq x)
    range := fun x => Install.ValidAt.extend he (h.range x)
    length := fun x => Install.ValidAt.extend he (h.length x)
    getD := fun x => Install.ValidAt.extend he (h.getD x)
    replicate := fun x => Install.ValidAt.extend he (h.replicate x)
    append := fun x => Install.ValidAt.extend he (h.append x)
    xorL := he _ _ h.xorL
    gateVal := he _ _ h.gateVal
    runStep := he _ _ h.runStep
    run := he _ _ h.run
    look := he _ _ h.look
    mapLook := he _ _ h.mapLook
    maskOf := he _ _ h.maskOf
    parStep := he _ _ h.parStep
    parFold := he _ _ h.parFold
    par := he _ _ h.par
    bit := he _ _ h.bit
    mapBit := he _ _ h.mapBit
    dense := he _ _ h.dense
    mapDense := he _ _ h.mapDense
    headT := he _ _ h.headT
    tailB := he _ _ h.tailB
    filterHead := he _ _ h.filterHead
    mapTail := he _ _ h.mapTail
    clear := he _ _ h.clear
    mapClear := he _ _ h.mapClear
    rankStep := he _ _ h.rankStep
    rankFold := he _ _ h.rankFold
    rank := he _ _ h.rank
    idB := he _ _ h.idB
    filterId := he _ _ h.filterId
    notB := he _ _ h.notB
    mapNot := he _ _ h.mapNot
    dbl := he _ _ h.dbl
    dblFold := he _ _ h.dblFold
    amb := he _ _ h.amb
    endpoint := he _ _ h.endpoint }

theorem repair_slots : Indices.OK Install.wL ri PP := by
  have h := FullRepairInstalled.repair_slots base den density E pg nb
  have he := extends_full base den density E pg nb
  exact {
    lesser := he _ _ h.lesser
    greater := he _ _ h.greater
    keyStep := he _ _ h.keyStep
    keyFold := he _ _ h.keyFold
    keyLe := he _ _ h.keyLe
    keyEq := he _ _ h.keyEq
    lowerStep := he _ _ h.lowerStep
    lowerFold := he _ _ h.lowerFold
    lower := he _ _ h.lower
    upperStep := he _ _ h.upperStep
    upperFold := he _ _ h.upperFold
    upper := he _ _ h.upper
    anchorStep := he _ _ h.anchorStep
    anchorFold := he _ _ h.anchorFold
    anchor := he _ _ h.anchor
    substStep := he _ _ h.substStep
    substFold := he _ _ h.substFold
    subst := he _ _ h.subst
    point := he _ _ h.point
    outStep := he _ _ h.outStep
    outFold := he _ _ h.outFold
    repair := he _ _ h.repair }

theorem canonical_slots : CanonicalIndices.OK Install.wL ci Install.yR.append PP := by
  have h := FullRepairInstalled.canonical_slots base den density E pg nb
  have he := extends_full base den density E pg nb
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  exact ⟨he _ _ h1,he _ _ h2,he _ _ h3,he _ _ h4,he _ _ h5,he _ _ h6,he _ _ h7,he _ _ h8,
    he _ _ h9⟩

theorem anchor_slots : AnchorIndices.OK Install.wL ci Install.yR ai PP := by
  have h := FullRepairInstalled.anchor_slots base den density E pg nb
  have he := extends_full base den density E pg nb
  rcases h with ⟨h1,h2,h3,h4,h5⟩
  exact ⟨he _ _ h1,he _ _ h2,he _ _ h3,he _ _ h4,he _ _ h5⟩

theorem wrapper_slots : WrapperIndices.OK Install.wL ri ci Install.yR ai wi PP := by
  have h := FullRepairInstalled.wrapper_slots base den density E pg nb
  have he := extends_full base den density E pg nb
  rcases h with ⟨h1,h2,h3,h4,h5⟩
  exact ⟨he _ _ h1,he _ _ h2,he _ _ h3,he _ _ h4,he _ _ h5⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem general_slots : GeneralIndices.OK Install.wL ri ci Install.yR ai wi gi PP := by
  refine ⟨?_,?_,?_⟩ <;>
    simp only [program,List.getElem?_append_right,QueryInstalled.program_length] <;> rfl

abbrev callback := generalF Install.wL ri ci Install.yR ai wi gi

theorem callback_valid : ∀ x, callback.ValidAt PP x :=
  general_valid (library_valid base den density E pg nb)
    (rank_library_valid base den density E pg nb)
    (repair_slots base den density E pg nb) (canonical_slots base den density E pg nb)
    (anchor_slots base den density E pg nb) (wrapper_slots base den density E pg nb)
    (general_slots base den density E pg nb)

theorem callback_computes (x : TTensorX.den) (gs bs : List RawRatio) :
    FL.Computes PP gi.general (TFullArg.enc (x,gs,bs)) (TOutput.enc (generalR x gs bs))
      (max (callback.msize (x,gs,bs)) (TFullArg.enc (x,gs,bs)).size)
      (callback.cost (x,gs,bs)) (callback.depth (x,gs,bs)) :=
  general_computes (library_valid base den density E pg nb)
    (rank_library_valid base den density E pg nb)
    (repair_slots base den density E pg nb) (canonical_slots base den density E pg nb)
    (anchor_slots base den density E pg nb) (wrapper_slots base den density E pg nb)
    (general_slots base den density E pg nb) x gs bs

end QecReliability.TensorMachine.GeneralInstalled

#print axioms QecReliability.TensorMachine.GeneralInstalled.callback_valid
