import TensorMachineControllerFL

/-! Reuse of the installed counting phases at the tensor context type. The FL
compiler erases the external-data type; unchanged bodies are recovered from
literal inherited slots. Only query/endpoint callers and dispatch need new
slots when their callee indices change. -/

set_option autoImplicit false

namespace QecReliability.TensorMachine.ControlLibrary

open FL FL.Lib Trans.Control
open Trans.Query.Plain (ProgP)

abbrev TX := ContextFL.TX

def indices (Q : FnSig (.prod TX TKey) (.list .bool))
    (endpoint : FnSig (.prod TX .bool) TR)
    (compilePIdx endpointZeroIdx endpointOneIdx dispatchIdx : ℕ) : Ix TX where
  compile := Q
  endpoint := endpoint
  succ := 0
  pred := 1
  add := 3
  le := 6
  eq := 8
  max := 9
  mul := 10
  sub := 5
  append := 14
  fstE := 103
  mapFst := 104
  entry := 105
  ctr := 106
  md := 107
  reverseCells := 249
  selectScan := 250
  trialCommit := 251
  sortNext := 252
  insertScan := 253
  insertRestore := 254
  medianLookup := 255
  reverseGood := 256
  reverseBad := 257
  reverseOutput := 258
  fop0 := 259
  fop1 := 260
  fop2 := 261
  fop3 := 262
  fop4 := 263
  fop5 := 264
  fop6 := 265
  fetch := 266
  compileP := compilePIdx
  endpointZero := endpointZeroIdx
  endpointOne := endpointOneIdx
  repairAcc := 305
  repair := 306
  pstep := 272
  prefixP := 273
  resume := 274
  dispatch := dispatchIdx
  step := 276
  isDone := 277
  isInvoke := 278
  queryOf := 279
  answer := 280
  answerST := 281

variable (base den density : ℕ) (E : ℕ × ℕ × ℕ)
  (pg : ℕ → ProgP) (nb : ℕ → ℕ → ℕ → ℕ)
  (Q : FnSig (.prod TX TKey) (.list .bool))
  (endpoint : FnSig (.prod TX .bool) TR)
  (compilePIdx endpointZeroIdx endpointOneIdx dispatchIdx : ℕ)

local notation "CX" => indices Q endpoint compilePIdx endpointZeroIdx endpointOneIdx dispatchIdx
local notation "SOURCE" => Installed.program base den density E pg nb

/-- The inherited arithmetic signatures are unchanged; actual tensor callbacks
are supplied by their own installed-body validity proofs. -/
theorem library_valid {P : FL.Program}
    (he : Install.Extends SOURCE P)
    (hOld : LibOK (Install.prog base den density E pg nb)
      (Install.cX base den density E pg nb))
    (hQ : ∀ a, Q.ValidAt P a) (hE : ∀ a, endpoint.ValidAt P a) : LibOK P CX := by
  have hprefix : Install.Extends (Install.prog base den density E pg nb) P := by
    intro k body hk
    exact he k body (Installed.extends_prefix base den density E pg nb k body hk)
  exact {
    compile := hQ
    endpoint := hE
    succ := fun a => Install.ValidAt.extend hprefix (hOld.succ a)
    pred := fun a => Install.ValidAt.extend hprefix (hOld.pred a)
    add := fun a => Install.ValidAt.extend hprefix (hOld.add a)
    le := fun a => Install.ValidAt.extend hprefix (hOld.le a)
    eq := fun a => Install.ValidAt.extend hprefix (hOld.eq a)
    max := fun a => Install.ValidAt.extend hprefix (hOld.max a)
    mul := fun a => Install.ValidAt.extend hprefix (hOld.mul a)
    sub := fun a => Install.ValidAt.extend hprefix (hOld.sub a)
    append := fun a => Install.ValidAt.extend hprefix (hOld.append a)
    mapFst := fun a => Install.ValidAt.extend hprefix (hOld.mapFst a)
    entry := fun a => Install.ValidAt.extend hprefix (hOld.entry a)
    ctr := fun a => Install.ValidAt.extend hprefix (hOld.ctr a)
    md := fun a => Install.ValidAt.extend hprefix (hOld.md a) }

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2000 in
/-- All counting loops are the actual inherited compiled bodies, now acting on
an extended tensor context. Newly installed boundary-call slots are explicit. -/
theorem phases_valid {P : FL.Program} (he : Install.Extends SOURCE P)
    (h : LibOK P CX)
    (hcompile : P[compilePIdx]? = some (compilePBody CX).compile)
    (hzero : P[endpointZeroIdx]? = some (endpointZeroBody CX).compile)
    (hone : P[endpointOneIdx]? = some (endpointOneBody CX).compile) :
    LatentMachine.EndpointControllerFL.PhasesOK P CX := by
  have hps := pstep_valid h (he _ _ rfl)
  exact {
    fetch := fetch_valid h (fop_valid h (he _ _ rfl) (he _ _ rfl) (he _ _ rfl)
      (he _ _ rfl) (he _ _ rfl) (he _ _ rfl) (he _ _ rfl)) (he _ _ rfl)
    prefixP := prefixP_valid h hps (he _ _ rfl)
    compileP := compileP_valid h hcompile
    resume := resume_valid h hps (he _ _ rfl)
    reverseCells := reverseCells_valid h (he _ _ rfl)
    selectScan := selectScan_valid h (he _ _ rfl)
    trialCommit := trialCommit_valid h (he _ _ rfl)
    sortNext := sortNext_valid h (he _ _ rfl)
    insertScan := insertScan_valid h (he _ _ rfl)
    insertRestore := insertRestore_valid h (he _ _ rfl)
    medianLookup := medianLookup_valid h (he _ _ rfl)
    reverseGood := reverseGood_valid h (he _ _ rfl)
    reverseBad := reverseBad_valid h (he _ _ rfl)
    endpointZero := endpointZero_valid h hzero
    endpointOne := endpointOne_valid h hone
    repair := LatentMachine.EndpointControllerFL.repair_valid
      (LatentMachine.EndpointControllerFL.repairAcc_valid h (he _ _ rfl)) (he _ _ rfl)
    reverseOutput := reverseOutput_valid h (he _ _ rfl) }

end QecReliability.TensorMachine.ControlLibrary
