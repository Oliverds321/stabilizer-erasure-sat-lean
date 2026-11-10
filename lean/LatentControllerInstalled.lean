import LatentWrappersInstalled
import LatentEndpointDispatchFL

/-! Seven fixed controller replacement bodies,302–308. Unaffected phases retain
their old slots; compile and endpoint phases call the new latent wrappers, and
repair/dispatch/step call the new endpoint-only bodies. The old true-mode chain
remains in the prefix but is not reachable from this new step signature. -/
set_option autoImplicit false
namespace QecReliability.LatentMachine.ControllerInstalled
open FL FL.Lib Trans.Wire Trans.Control
open Trans.Query.Plain (ProgP)
variable (base den density : ℕ) (E : ℕ × ℕ × ℕ)
  (pg : ℕ → ProgP) (nb : ℕ → ℕ → ℕ → ℕ)

def indices : Trans.Control.Ix TX :=
  { Install.cX base den density E pg nb with
    compile := WrappersFL.compileF Install.wL WrappersInstalled.indices Install.queryFn
      (Install.hashFn E pg nb) base den density
    endpoint := WrappersFL.endpointWF Install.wL WrappersInstalled.indices Install.yR
    compileP := 302, endpointZero := 303, endpointOne := 304
    repairAcc := 305, repair := 306, dispatch := 307, step := 308 }

local notation "CX" => indices base den density E pg nb

def segment : FL.Program :=
  [(compilePBody CX).compile,(endpointZeroBody CX).compile,(endpointOneBody CX).compile,
   (EndpointControllerFL.repairAccBody CX).compile,(EndpointControllerFL.repairBody CX).compile,
   (EndpointControllerFL.dispatchBody CX).compile,(EndpointControllerFL.stepBody CX).compile]

def program : FL.Program :=
  WrappersInstalled.program base den density E pg nb ++ segment base den density E pg nb

local notation "PP" => program base den density E pg nb
local notation "OLD" => Install.prog base den density E pg nb

theorem extends_wrappers : Install.Extends (WrappersInstalled.program base den density E pg nb) PP :=
  Install.extends_append _ _

theorem extends_prefix : Install.Extends OLD PP := by
  intro i b hi
  exact extends_wrappers base den density E pg nb i b
    (WrappersInstalled.extends_prefix base den density E pg nb i b hi)

theorem program_length : (program base den density E pg nb).length = 309 := by
  simp only [program,List.length_append,WrappersInstalled.program_length]
  rfl

theorem library_valid (hH : ∀ x, (Install.hashFn E pg nb).ValidAt OLD x) : LibOK PP CX := by
  have old := Install.cX_lib hH
  have he := extends_prefix base den density E pg nb
  have hw := extends_wrappers base den density E pg nb
  exact {
    compile := fun x => Install.ValidAt.extend hw (WrappersInstalled.compile_valid base den density E pg nb hH x)
    endpoint := fun x => Install.ValidAt.extend hw (WrappersInstalled.endpoint_valid base den density E pg nb x)
    succ := fun x => Install.ValidAt.extend he (old.succ x)
    pred := fun x => Install.ValidAt.extend he (old.pred x)
    add := fun x => Install.ValidAt.extend he (old.add x)
    le := fun x => Install.ValidAt.extend he (old.le x)
    eq := fun x => Install.ValidAt.extend he (old.eq x)
    max := fun x => Install.ValidAt.extend he (old.max x)
    mul := fun x => Install.ValidAt.extend he (old.mul x)
    sub := fun x => Install.ValidAt.extend he (old.sub x)
    append := fun x => Install.ValidAt.extend he (old.append x)
    mapFst := fun x => Install.ValidAt.extend he (old.mapFst x)
    entry := fun x => Install.ValidAt.extend he (old.entry x)
    ctr := fun x => Install.ValidAt.extend he (old.ctr x)
    md := fun x => Install.ValidAt.extend he (old.md x) }

/-- Actual new-body slots and inherited generic phases discharge every call. -/
theorem phases_valid (hH : ∀ x, (Install.hashFn E pg nb).ValidAt OLD x) :
    EndpointControllerFL.PhasesOK PP CX := by
  have old := Install.cX_phases hH
  have he := extends_prefix base den density E pg nb
  have h := library_valid base den density E pg nb hH
  exact {
    fetch := fun x => Install.ValidAt.extend he (old.fetch x)
    prefixP := fun x => Install.ValidAt.extend he (old.prefixP x)
    resume := fun x => Install.ValidAt.extend he (old.resume x)
    reverseCells := fun x => Install.ValidAt.extend he (old.reverseCells x)
    selectScan := fun x => Install.ValidAt.extend he (old.selectScan x)
    trialCommit := fun x => Install.ValidAt.extend he (old.trialCommit x)
    sortNext := fun x => Install.ValidAt.extend he (old.sortNext x)
    insertScan := fun x => Install.ValidAt.extend he (old.insertScan x)
    insertRestore := fun x => Install.ValidAt.extend he (old.insertRestore x)
    medianLookup := fun x => Install.ValidAt.extend he (old.medianLookup x)
    reverseGood := fun x => Install.ValidAt.extend he (old.reverseGood x)
    reverseBad := fun x => Install.ValidAt.extend he (old.reverseBad x)
    reverseOutput := fun x => Install.ValidAt.extend he (old.reverseOutput x)
    compileP := Trans.Control.compileP_valid h rfl
    endpointZero := Trans.Control.endpointZero_valid h rfl
    endpointOne := Trans.Control.endpointOne_valid h rfl
    repair := EndpointControllerFL.repair_valid
      (EndpointControllerFL.repairAcc_valid h rfl) rfl }

theorem step_valid (hH : ∀ x, (Install.hashFn E pg nb).ValidAt OLD x) :
    ∀ x, (EndpointControllerFL.stepF CX).ValidAt PP x :=
  EndpointControllerFL.step_valid
    (EndpointControllerFL.dispatch_valid (library_valid base den density E pg nb hH)
      (phases_valid base den density E pg nb hH) rfl) rfl

/-- Exact false-mode edge, now at the indices of the actual installed step. -/
theorem step_agrees (q r B m : ℕ) (X : TX.den) (ext : OracleCost.WholeWrapperCandidate.External)
    (s : OracleCost.WholeWrapperCandidate.Config) (hn : s.pc ≠ .invoke)
    (he : ExtAgrees CX X ext s) (e : OracleCost.WholeWrapperCandidate.Edge)
    (hs : OracleCost.WholeWrapperCandidate.step q r B m false ext s = some e) :
    (EndpointControllerFL.stepF CX).den (encCtx q r B m X,encCfg s) =
      (encCtx q r B m X,encCfg e.next) :=
  EndpointControllerFL.step_correct CX q r B m X ext s hn he e hs

/-- The SAT-invocation successor is shape-independent; this is the false-mode statement. -/
theorem invoke_next (q r B m : ℕ) (ext : OracleCost.WholeWrapperCandidate.External)
    (s : OracleCost.WholeWrapperCandidate.Config) (hp : s.pc = .invoke) :
    (OracleCost.WholeWrapperCandidate.step q r B m false ext s).map
      OracleCost.WholeWrapperCandidate.Edge.next =
      some { s with pc := .resume, reply := (ext.sat s.query).value } := by
  simp [OracleCost.WholeWrapperCandidate.step,hp]

end QecReliability.LatentMachine.ControllerInstalled

