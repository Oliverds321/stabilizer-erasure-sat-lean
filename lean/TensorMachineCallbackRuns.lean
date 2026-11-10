import TensorMachineTrace

/-! Actual register-body runs from installed tensor callbacks and their concrete
FL cost, depth and intermediate-space bounds. These are numeric compiler bounds,
not assumptions that the desired machine execution already exists. -/

set_option autoImplicit false
noncomputable section
namespace QecReliability.TensorMachine

open FL FL.Lib FL.Tm Trans.Wire Trans.Control
open Trans.Query.Plain (ProgP)
open OracleCost OracleCost.WholeWrapperCandidate RegMachine Interp Assembly RationalOutput

structure CallBounds {a b : Ty} (F : FnSig a b) (x : a.den) (M T D : ℕ) : Prop where
  space : F.msize x ≤ M
  argument : (a.enc x).size ≤ M
  time : F.cost x ≤ T
  depth : F.depth x ≤ D

theorem CallBounds.computes {a b : Ty} {P : FL.Program} {F : FnSig a b}
    {x : a.den} {M T D : ℕ} (h : CallBounds F x M T D) (hv : F.ValidAt P x) :
    FL.Computes P F.idx (a.enc x) (b.enc (F.den x)) M T D := by
  obtain ⟨harg,t,d,ht,hd,he⟩ := hv.computes h.space h.argument
  exact ⟨harg,t,d,ht.trans h.time,hd.trans h.depth,he⟩

namespace Program
variable (source : FL.Program) (Q : FnSig QueryFL.CompilerArg (.list .bool))
  (repair : FnSig ControllerFL.RepairArg (.list TR))
  (base den density : ℕ) (E : ℕ × ℕ × ℕ)
  (pg : ℕ → ProgP) (nb : ℕ → ℕ → ℕ → ℕ)

local notation "PP" => program source Q repair base den density E pg nb
local notation "CX" => controller source Q base den density E pg nb
local notation "II" => assemblyIndices source
local notation "SF" => tensorStep source Q repair base den density E pg nb

variable {O : OracleSpec} {S M T D : ℕ} {q r B m : ℕ} {X : TX.den}

/-- A compiled ordinary counting transition, before the tensor repair boundary. -/
theorem counting_body_run (hv : Valid source Q repair base den density E pg nb)
    (ext : External) (s : Config) (edge : Edge)
    (hn : s.pc ≠ .invoke) (hf : s.pc ≠ .endpointZero)
    (he : ExtAgrees CX X ext s)
    (hs : WholeWrapperCandidate.step q r B m false ext s = some edge)
    (hnext : edge.next.pc ≠ .fault)
    (hS : stBound PP II M D + (FL.Program.enc PP).size + 2 ≤ S) (hm : 2 * M + 4 ≤ S)
    (hi : CallBounds (isInvokeF CX) (encCtx q r B m X,encCfg s) M T D)
    (hst : CallBounds SF (encCtx q r B m X,encCfg s) M T D)
    (hd : CallBounds (isDoneF CX) (encCtx q r B m X,encCfg edge.next) M T D) :
    ORuns O S (body PP II)
      (headRegs ((TArg TX).enc (encCtx q r B m X,encCfg s)) false)
      (headRegs ((TArg TX).enc (encCtx q r B m X,encCfg edge.next))
        (decide (edge.next.pc = .done))) (bodyCost PP II S M T D) := by
  have hi' := hi.computes (hv.isInvoke _)
  rw [isInvoke_correct, show decide (s.pc = .invoke) = false by simp [hn]] at hi'
  have hs' := hst.computes (hv.step _)
  rw [counting_step_den source Q repair base den density E pg nb q r B m X ext s hn hf he edge hs] at hs'
  have hd' := hd.computes (hv.isDone _)
  rw [isDone_den source Q base den density E pg nb q r B m X edge.next hnext] at hd'
  exact body_step_run hS hm hi' hs' hd'

/-- The extra body iteration executes the actual whole-grid repair callback. -/
theorem repair_body_run (hv : Valid source Q repair base den density E pg nb)
    (s : Config) (values : List Ratio) (hs : s.pc = .endpointZero)
    (hr : repair.den (X,s.goodTable,s.badTable) = values.map toR)
    (hS : stBound PP II M D + (FL.Program.enc PP).size + 2 ≤ S) (hm : 2 * M + 4 ≤ S)
    (hi : CallBounds (isInvokeF CX) (encCtx q r B m X,encCfg s) M T D)
    (hst : CallBounds SF (encCtx q r B m X,encCfg s) M T D)
    (hd : CallBounds (isDoneF CX)
      (encCtx q r B m X,encCfg {s with pc := .done, output := values}) M T D) :
    ORuns O S (body PP II)
      (headRegs ((TArg TX).enc (encCtx q r B m X,encCfg s)) false)
      (headRegs ((TArg TX).enc
        (encCtx q r B m X,encCfg {s with pc := .done, output := values})) true)
      (bodyCost PP II S M T D) := by
  have hi' := hi.computes (hv.isInvoke _)
  rw [isInvoke_correct, show decide (s.pc = .invoke) = false by simp [hs]] at hi'
  have hs' := hst.computes (hv.step _)
  change FL.Computes PP _ _ ((TArg TX).enc
    ((ControllerFL.stepF CX repair (source.length+6) (source.length+7) (source.length+8)).den
      (encCtx q r B m X,encCfg s))) M T D at hs'
  rw [ControllerFL.step_den_endpoint CX repair _ _ _ q r B m X s hs values hr] at hs'
  have hd' := hd.computes (hv.isDone _)
  rw [isDone_den source Q base den density E pg nb q r B m X
    {s with pc := .done, output := values} (by simp)] at hd'
  exact body_step_run hS hm hi' hs' hd'

/-- The SAT call is performed by the actual isolated oracle instruction. -/
theorem invoke_body_run (hv : Valid source Q repair base den density E pg nb)
    (s : Config) (hs : s.pc = .invoke) (hok : O.qok s.query)
    (hS : stBound PP II M D + (FL.Program.enc PP).size + 2 ≤ S) (hm : 2 * M + 4 ≤ S)
    (hi : CallBounds (isInvokeF CX) (encCtx q r B m X,encCfg s) M T D)
    (hq : CallBounds (queryOfF CX) (encCtx q r B m X,encCfg s) M T D)
    (hr : CallBounds (Trans.Bounds.resumeTopF Install.oX CX)
      (O.oracle s.query,(encCtx q r B m X,encCfg s)) M T D)
    (hd : CallBounds (isDoneF CX) (encCtx q r B m X,
      encCfg {s with pc := .resume, reply := O.oracle s.query}) M T D) :
    ORuns O S (body PP II)
      (headRegs ((TArg TX).enc (encCtx q r B m X,encCfg s)) false)
      (headRegs ((TArg TX).enc (encCtx q r B m X,
        encCfg {s with pc := .resume, reply := O.oracle s.query})) false)
      (bodyCost PP II S M T D + O.ocost s.query) := by
  have hi' := hi.computes (hv.isInvoke _)
  rw [isInvoke_correct, show decide (s.pc = .invoke) = true by simp [hs]] at hi'
  have hq' := hq.computes (hv.query _)
  rw [queryOf_correct] at hq'
  have hr' := hr.computes (hv.resume _)
  rw [resume_den source Q base den density E pg nb q r B m X s (O.oracle s.query)] at hr'
  have hd' := hd.computes (hv.isDone _)
  rw [isDone_den source Q base den density E pg nb q r B m X
    {s with pc := .resume, reply := O.oracle s.query} (by simp)] at hd'
  exact body_invoke_run hS hm hi' hq' hok hr' hd'

end Program
end QecReliability.TensorMachine
end
