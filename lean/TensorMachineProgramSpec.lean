import TensorMachineProgramValid

/-! Exact initialization, counting-step transfer and output behavior for the
assembled tensor program. These facts expose its actual compiled callbacks to
the operational trace and finite-tape lowering proofs. -/

set_option autoImplicit false

namespace QecReliability.TensorMachine.Program

open FL FL.Lib FL.Tm Trans.Wire Trans.Control
open Trans.Query.Plain (ProgP)
open OracleCost OracleCost.WholeWrapperCandidate SharedCircuit SharedCircuit.LatentEncoding

def initialized (base den : ℕ) (ds : List ℕ) {n : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ) (coins : List Bool) : (TArg TX).den :=
  let q := keySize n ds.sum
  let r := TensorMachine.slots ds - 1
  let m := rationalRepetitionBudget (2 * TensorMachine.slots ds) c d
  (encCtx q r (rationalCellBudget a b) m (ContextFL.externalData base den ds rows C coins),
    encCfg (initial q r m))

theorem initializer_den (source : FL.Program) (base den : ℕ) (ds : List ℕ) {n : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ) (coins : List Bool) :
    (initializer source base den).den (input ds rows C a b c d coins) =
      initialized base den ds rows C a b c d coins := by
  unfold initializer
  rw [InitializerFL.initial_den]
  simp only [ParserFL.parseF_den, parse_input]
  unfold context
  rw [ContextFL.context_den Install.wL Install.wA Installed.gridIndices Install.paramsFn
    base den 295 13 (source.length + 9) (fun _ => rfl)]
  rfl

variable (source : FL.Program) (Q : FnSig QueryFL.CompilerArg (.list .bool))
  (repair : FnSig ControllerFL.RepairArg (.list TR))
  (base den density : ℕ) (E : ℕ × ℕ × ℕ)
  (pg : ℕ → ProgP) (nb : ℕ → ℕ → ℕ → ℕ)

local notation "PP" => Program.program source Q repair base den density E pg nb
local notation "CX" => controller source Q base den density E pg nb

theorem step_den_other (q r B m : ℕ) (X : TX.den) (s : Config) (hs : s.pc ≠ .endpointZero) :
    (tensorStep source Q repair base den density E pg nb).den (encCtx q r B m X, encCfg s) =
      (LatentMachine.EndpointControllerFL.stepF CX).den (encCtx q r B m X, encCfg s) := by
  simp only [tensorStep, ControllerFL.stepF, bodySig_den, ControllerFL.stepBody,
    LatentMachine.EndpointControllerFL.stepF, LatentMachine.EndpointControllerFL.stepBody, tm_simp]
  rw [ControllerFL.dispatch_den_other CX repair (source.length + 6) (source.length + 7)
    q r B m X s hs]

/-- Every pre-endpoint counting edge is literally the inherited compiled step. -/
theorem counting_step_den (q r B m : ℕ) (X : TX.den) (ext : External) (s : Config)
    (hn : s.pc ≠ .invoke) (hf : s.pc ≠ .endpointZero)
    (he : ExtAgrees CX X ext s) (edge : Edge)
    (hs : WholeWrapperCandidate.step q r B m false ext s = some edge) :
    (tensorStep source Q repair base den density E pg nb).den (encCtx q r B m X, encCfg s) =
      (encCtx q r B m X, encCfg edge.next) := by
  rw [step_den_other source Q repair base den density E pg nb q r B m X s hf]
  exact LatentMachine.EndpointControllerFL.step_correct CX q r B m X ext s hn he edge hs

theorem output_den (q r B m : ℕ) (X : TX.den) (s : Config) :
    (Trans.Bounds.outputF Install.oX TX).den (encCtx q r B m X, encCfg s) =
      Assembly.ratioWord s.output := Trans.Bounds.outputF_den _ _ _

theorem resume_den (q r B m : ℕ) (X : TX.den) (s : Config) (answer : Bool) :
    (Trans.Bounds.resumeTopF Install.oX CX).den (answer, (encCtx q r B m X, encCfg s)) =
      (encCtx q r B m X, encCfg { s with pc := .resume, reply := answer }) := rfl

theorem isDone_den (q r B m : ℕ) (X : TX.den) (s : Config) (hf : s.pc ≠ .fault) :
    (isDoneF CX).den (encCtx q r B m X, encCfg s) = decide (s.pc = .done) := by
  cases hs : s.pc <;> simp_all [isDoneF, bodySig_den, isDoneBody,
    Trans.Control.Tm.eqLit, tm_simp, encCfg, encCtx, pcCode]

/-- Actual initialized FL execution, with the compiler's measured resource budgets. -/
theorem initializer_computes (hv : Valid source Q repair base den density E pg nb)
    (ds : List ℕ) {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program ds.sum n) (a b c d : ℕ) (coins : List Bool) :
    let bits := input ds rows C a b c d coins
    let F := initializer source base den
    FL.Computes PP (assemblyIndices source).init ((Ty.list Ty.bool).enc bits)
      ((TArg TX).enc (initialized base den ds rows C a b c d coins))
      (max (F.msize bits) ((Ty.list Ty.bool).enc bits).size) (F.cost bits) (F.depth bits) := by
  dsimp only
  have h := (hv.initial (input ds rows C a b c d coins)).computes
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  rw [initializer_den] at h
  exact h

end QecReliability.TensorMachine.Program
