import GeneralMachineAgreement
import TensorMachineInvoke
import TensorMachineCallbackRuns

/-! Counting and final repair on the fixed installed tensor program. The only
remaining inputs to this execution theorem are numerical compiler budgets. -/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace QecReliability.TensorMachineG.Runtime
open QecReliability.TensorMachine QecReliability.TensorMachine.Runtime
open FL FL.Lib Trans.Wire Trans.Control RegMachine Assembly RationalOutput
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.MultiTape

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {Pt Ps : PolynomialEnvelope} {timeE : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps timeE requestExtent)
  {n : ℕ} {ds : List ℕ} (rows : List (List (PauliCoord n)))
  (C : SharedCircuit.Program ds.sum n) (B m : ℕ)
  (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
    (Factory.width hD hd A n ds) m) → Bool)

local notation "SRC" => source hD hd A density
local notation "PP" => program hD hd A density
local notation "II" => indices hD hd A density
local notation "CX" => controller hD hd A density
local notation "XX" => contextData hD hd A ds rows C (List.ofFn coins)
local notation "EXT" => external hD hd A density spec rows C m coins
local notation "QQ" => keySize n ds.sum
local notation "RR" => slots ds - 1
local notation "AA" => fun s : Config => (encCtx QQ RR B m XX,encCfg s)
local notation "VV" => fun s : Config => (TArg ContextFL.TX).enc (AA s)
local notation "REACH" => Reachable QQ RR B m false EXT
local notation "SF" => Program.tensorStep SRC Concrete.query Concrete.repair
  (data hD hd A).base (data hD hd A).den density
  (Trans.HashCallees.encConsts D A) (Install.thePg hD hd A) (Trans.Hash.gNbr actualMGG)

structure LoopBounds (M T Dp : ℕ) : Prop where
  argument : ∀ s, REACH s → (VV s).size ≤ M
  invoke : ∀ s, REACH s → CallBounds (isInvokeF CX) (AA s) M T Dp
  done : ∀ s, REACH s → CallBounds (isDoneF CX) (AA s) M T Dp
  query : ∀ s, REACH s → CallBounds (queryOfF CX) (AA s) M T Dp
  step_counting : ∀ s e, REACH s → s.pc ≠ .invoke → s.pc ≠ .endpointZero →
    WholeWrapperCandidate.step QQ RR B m false EXT s = some e →
    CallBounds SF (AA s) M T Dp
  step_finish : ∀ s, REACH s → s.pc = .endpointZero → CallBounds SF (AA s) M T Dp
  resume : ∀ s, REACH s → ∀ answer,
    CallBounds (Trans.Bounds.resumeTopF Install.oX CX) (answer,AA s) M T Dp

set_option maxHeartbeats 1500000 in
theorem counting_repair_loop {M T Dp S g : ℕ}
    (hg : ∀ scale seed, ((Factory.circuits hD hd A n ds).program scale seed).gates ≤ g)
    (hbounds : LoopBounds hD hd A density spec rows C B m coins M T Dp)
    (hS : stBound PP II M Dp + (FL.Program.enc PP).size + 2 ≤ S) (hm : 2*M+4 ≤ S)
    {boundary : Config} {totals : Totals} {events : List RequestKey}
    (htr : Trace QQ RR B m false EXT (initial QQ RR m) totals events boundary)
    (hpc : boundary.pc = .endpointZero) (values : List Ratio)
    (hrepair : Concrete.repair.den (XX,boundary.goodTable,boundary.badTable) = values.map toR)
    (hfinished : CallBounds (isDoneF CX)
      (AA {boundary with pc := .done,output := values}) M T Dp) :
    let cap := Boundary.extentCap rows C density g
    ORuns (resourceSatOracle E density requestExtent cap) S (mainLoop PP II)
      (headRegs (VV (initial QQ RR m)) false)
      (headRegs (VV {boundary with pc := .done,output := values}) true)
      ((totals.dispatches+2)*(bodyCost PP II S M T Dp+Ps.eval cap+1)+totals.oracleTime) := by
  dsimp only
  let cap := Boundary.extentCap rows C density g
  let O := resourceSatOracle E density requestExtent cap
  have hv := valid hD hd A density
  have hbody : ∀ s e, REACH s → s.pc ≠ .endpointZero →
      WholeWrapperCandidate.step QQ RR B m false EXT s = some e →
      (∃ ts es, Trace QQ RR B m false EXT e.next ts es boundary) →
      ORuns O S (body PP II) (headRegs (VV s) false)
        (headRegs (VV e.next) (decide (e.next.pc = .done)))
        ((bodyCost PP II S M T Dp+Ps.eval cap)+e.oracleTime) := by
    intro s e hs hboundary hedge htail
    have hn := reachable_next hs hedge
    obtain ⟨ts,es,htail⟩ := htail
    have hnf := boundary_trace_ne_fault htail hpc
    by_cases hinvoke : s.pc = .invoke
    · have ho := Boundary.invoke_correct rows C (Factory.system hD hd A n ds).stages
        (Factory.circuits hD hd A n ds) m
        (LatentMachine.decodeCoins (Factory.length hD hd A n ds)
          (Factory.width hD hd A n ds) m coins) density spec g hg hs hinvoke
      have hnext : e.next = {s with pc := .resume,reply := O.oracle s.query} := by
        simp only [WholeWrapperCandidate.step,hinvoke,Option.some.injEq] at hedge
        subst e
        rw [ho.2.1]
      have hdnext := hbounds.done e.next hn
      rw [hnext] at hdnext
      have hr := Program.invoke_body_run SRC Concrete.query Concrete.repair
        (data hD hd A).base (data hD hd A).den density (Trans.HashCallees.encConsts D A)
        (Install.thePg hD hd A) (Trans.Hash.gNbr actualMGG) hv s hinvoke ho.1 hS hm
        (hbounds.invoke s hs) (hbounds.query s hs) (hbounds.resume s hs _) hdnext
      have ht := invoke_edge_time hinvoke hedge
      rw [hnext]
      simpa only [program,indices,Concrete.program,Concrete.indices,Program.TX,O,cap,show decide (({s with pc := .resume,reply := O.oracle s.query} : Config).pc = .done) = false by simp]
        using hr.mono (show bodyCost PP II S M T Dp+O.ocost s.query ≤
          bodyCost PP II S M T Dp+Ps.eval cap+e.oracleTime by
            have hc : O.ocost s.query ≤ ((EXT).sat s.query).time + Ps.eval cap := ho.2.2
            omega)
    · have ha := extAgrees hD hd A density spec rows C m coins s
        (reachable_request_invariant hs).request
      exact (Program.counting_body_run SRC Concrete.query Concrete.repair
        (data hD hd A).base (data hD hd A).den density (Trans.HashCallees.encConsts D A)
        (Install.thePg hD hd A) (Trans.Hash.gNbr actualMGG) hv EXT s e hinvoke hboundary
        ha hedge hnf hS hm (hbounds.invoke s hs) (hbounds.step_counting s e hs hinvoke hboundary hedge) (hbounds.done e.next hn)).mono
        (by change bodyCost PP II S M T Dp ≤ bodyCost PP II S M T Dp+Ps.eval cap+e.oracleTime; omega)
  have hfinish : REACH boundary → ORuns O S (body PP II) (headRegs (VV boundary) false)
      (headRegs (VV {boundary with pc := .done,output := values}) true)
      (bodyCost PP II S M T Dp+Ps.eval cap) := by
    intro hs
    exact (Program.repair_body_run SRC Concrete.query Concrete.repair
      (data hD hd A).base (data hD hd A).den density (Trans.HashCallees.encConsts D A)
      (Install.thePg hD hd A) (Trans.Hash.gNbr actualMGG) hv boundary values hpc hrepair hS hm
      (hbounds.invoke boundary hs) (hbounds.step_finish boundary hs hpc) hfinished).mono (by change bodyCost PP II S M T Dp ≤ bodyCost PP II S M T Dp+Ps.eval cap; omega)
  have hloop := loop_to_repaired_path VV REACH
    (fun s => {s with pc := .done,output := values}) (fun _ => rfl)
    (fun s e hs he => reachable_next hs he)
    (fun s hs => fits_start hm (hbounds.argument s hs)) hbody hfinish htr reachable_initial hpc
  simpa [initial] using hloop

end QecReliability.TensorMachineG.Runtime
end
