import TensorRepairFLWrapper
import TensorRepairFLInstalled

/-! Fixed installation of the full tensor repair callback. All 361 program
bodies are chosen before the degree list, observations, or circuit arrives. -/
set_option autoImplicit false

namespace QecReliability.TensorMachine.FullRepairInstalled
open FL FL.Lib TensorMachine.RepairFL
open Trans.Query.Plain (ProgP)

abbrev ri := RepairInstalled.indices
abbrev ci : CanonicalIndices := ⟨342,343,344,345,346,347,348,349,350⟩
abbrev ai : AnchorIndices := ⟨351,352,353,354,355⟩
abbrev wi : WrapperIndices := ⟨356,357,358,359,360⟩

def segment : FL.Program :=
  [(canonicalBitBody Install.wL).compile,
   (Trans.Hash.mapEnvBody (canonicalBitF Install.wL ci) ci.blockMap).compile,
   (blockBody Install.wL ci).compile,
   (bitsStepBody Install.wL ci Install.yR.append).compile,
   (foldlBody (bitsStepF Install.wL ci Install.yR.append) ci.bitsFold).compile,
   (bitsBody Install.wL ci Install.yR.append).compile,
   (cornerStepBody Install.wL).compile,
   (foldlBody (cornerStepF Install.wL ci) ci.cornerFold).compile,
   (cornerBody Install.wL ci).compile,
   (maskFromBitsBody Install.yR).compile,
   (dyadicBody Install.wL ci Install.yR ai).compile,
   (anchorDataStepBody Install.wL ci Install.yR ai).compile,
   (foldrBody (anchorDataStepF Install.wL ci Install.yR ai) ai.fold).compile,
   (anchorDataBody Install.wL ci Install.yR ai).compile,
   (LinearRepairFL.countsBody Install.wL.add).compile,
   (countsStepBody wi).compile,
   (foldlBody (countsStepF wi) wi.countsFold).compile,
   (countDataBody Install.wL wi).compile,
   (fullBody Install.wL ri ci Install.yR ai wi).compile]

variable (base den density : ℕ) (E : ℕ × ℕ × ℕ)
  (pg : ℕ → ProgP) (nb : ℕ → ℕ → ℕ → ℕ)

def program : FL.Program := RepairInstalled.program base den density E pg nb ++ segment
local notation "PP" => program base den density E pg nb

theorem program_length : (PP).length = 361 := by
  simp only [program,List.length_append,RepairInstalled.program_length]
  rfl

theorem extends_repair : Install.Extends
    (RepairInstalled.program base den density E pg nb) PP := Install.extends_append _ _

theorem extends_tensor : Install.Extends
    (Installed.program base den density E pg nb) PP := by
  intro k b h
  exact extends_repair base den density E pg nb k b
    (RepairInstalled.extends_tensor base den density E pg nb k b h)

theorem extends_prefix : Install.Extends (Install.prog base den density E pg nb) PP := by
  intro k b h
  exact extends_tensor base den density E pg nb k b
    (Installed.extends_prefix base den density E pg nb k b h)

theorem library_valid : Install.wL.OK PP := by
  have h := RepairInstalled.library_valid base den density E pg nb
  have he := extends_repair base den density E pg nb
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
  have h := Install.yR_ok (base := base) (den := den) (density := density)
    (E := E) (pg := pg) (nb := nb)
  have he := extends_prefix base den density E pg nb
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
  have h := RepairInstalled.slots base den density E pg nb
  have he := extends_repair base den density E pg nb
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

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem canonical_slots : CanonicalIndices.OK Install.wL ci Install.yR.append PP :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem anchor_slots : AnchorIndices.OK Install.wL ci Install.yR ai PP :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem wrapper_slots : WrapperIndices.OK Install.wL ri ci Install.yR ai wi PP :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

abbrev callback := fullF Install.wL ri ci Install.yR ai wi

theorem callback_valid : ∀ x, callback.ValidAt PP x :=
  full_valid (library_valid base den density E pg nb) (rank_library_valid base den density E pg nb)
    (repair_slots base den density E pg nb) (canonical_slots base den density E pg nb)
    (anchor_slots base den density E pg nb) (wrapper_slots base den density E pg nb)

theorem callback_computes (x : TTensorX.den) (gs bs : List RawRatio) :
    FL.Computes PP wi.full (TFullArg.enc (x,gs,bs)) (TOutput.enc (fullR x gs bs))
      (max (callback.msize (x,gs,bs)) (TFullArg.enc (x,gs,bs)).size)
      (callback.cost (x,gs,bs)) (callback.depth (x,gs,bs)) :=
  full_computes (library_valid base den density E pg nb) (rank_library_valid base den density E pg nb)
    (repair_slots base den density E pg nb) (canonical_slots base den density E pg nb)
    (anchor_slots base den density E pg nb) (wrapper_slots base den density E pg nb) x gs bs

end QecReliability.TensorMachine.FullRepairInstalled
