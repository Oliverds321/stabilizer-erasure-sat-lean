import GeneralMachineAgreement
import GeneralCountingOutput
import GeneralMachineRuntimeLoop
import TensorMachineResourceLowering
import TensorCountingOutput
import TensorPhysicalOutput

/-! The concrete fixed tensor machine completes and writes the same rational
table used by the physical confidence theorem. Only numerical compiler budget
inequalities are exposed here; trace, SAT agreement and repair are derived. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
namespace QecReliability.TensorMachineG.Runtime
open QecReliability.TensorMachine QecReliability.TensorMachine.Runtime
open FL FL.Lib Trans.Wire Trans.Control RegMachine Assembly RationalOutput Final
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.MultiTape

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {Pt Ps : PolynomialEnvelope} {timeE : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps timeE requestExtent)
  {n : ℕ} {ds : List ℕ} (rows : List (List (PauliCoord n)))
  (C : SharedCircuit.Program ds.sum n) (a b c d m : ℕ)


variable (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
    (Factory.width hD hd A n ds) (m)) → Bool)


set_option maxHeartbeats 2000000 in
theorem completed_of_budgets {M T Dp S g : ℕ}
    (hrep : m = rationalRepetitionBudget (2*slots ds) c d)
    (hg : ∀ scale seed, ((Factory.circuits hD hd A n ds).program scale seed).gates ≤ g)
    (hbounds : LoopBounds hD hd A density spec (n:=n) (ds:=ds) rows C (rationalCellBudget a b) (m) coins M T Dp)
    (hS : stBound (program hD hd A density) (indices hD hd A density) M Dp + (FL.Program.enc (program hD hd A density)).size + 2 ≤ S) (hm : 2*M+4 ≤ S)
    (hinit : CallBounds (Program.initializer (source hD hd A density) (data hD hd A).base (data hD hd A).den) (input ds rows C a b c d (List.ofFn coins)) M T Dp)
    (hfinished : ∀ s, (Reachable (keySize n ds.sum) (slots ds - 1) (rationalCellBudget a b) (m) false (external hD hd A density spec rows C (m) coins)) s → s.pc = .endpointZero →
      Concrete.repair.den ((contextData hD hd A ds rows C (List.ofFn coins)),s.goodTable,s.badTable) = ((GeneralAlgorithm.output hD hd A rows C spec.service.solver (rationalCellBudget a b) (m) coins)).map toR →
      CallBounds (isDoneF (controller hD hd A density)) ((fun s : Config => (encCtx (keySize n ds.sum) (slots ds - 1) (rationalCellBudget a b) (m) (contextData hD hd A ds rows C (List.ofFn coins)),encCfg s)) {s with pc := .done,output := (GeneralAlgorithm.output hD hd A rows C spec.service.solver (rationalCellBudget a b) (m) coins)}) M T Dp)
    (houtput : ∀ s, (Reachable (keySize n ds.sum) (slots ds - 1) (rationalCellBudget a b) (m) false (external hD hd A density spec rows C (m) coins)) s → s.pc = .endpointZero →
      Concrete.repair.den ((contextData hD hd A ds rows C (List.ofFn coins)),s.goodTable,s.badTable) = ((GeneralAlgorithm.output hD hd A rows C spec.service.solver (rationalCellBudget a b) (m) coins)).map toR →
      CallBounds (Trans.Bounds.outputF Install.oX ContextFL.TX)
      ((fun s : Config => (encCtx (keySize n ds.sum) (slots ds - 1) (rationalCellBudget a b) (m) (contextData hD hd A ds rows C (List.ofFn coins)),encCfg s)) {s with pc := .done,output := (GeneralAlgorithm.output hD hd A rows C spec.service.solver (rationalCellBudget a b) (m) coins)}) M T Dp) :
    let cap := Boundary.extentCap rows C density g
    ∃ totals : Totals, ∃ run : Completed (theMachine E (program hD hd A density) (indices hD hd A density)) (input ds rows C a b c d (List.ofFn coins)),
      Outputs (theMachine E (program hD hd A density) (indices hD hd A density)) run (outTape kE) (GeneralAlgorithm.outputVector hD hd A rows C spec.service.solver (rationalCellBudget a b) (m) coins) ∧
      totals.calls = CountingTrace.sideCalls (keySize n ds.sum) (slots ds - 1) (rationalCellBudget a b) (m) (external hD hd A density spec rows C (m) coins) true (List.finRange ((slots ds - 1)+1)) +
        CountingTrace.sideCalls (keySize n ds.sum) (slots ds - 1) (rationalCellBudget a b) (m) (external hD hd A density spec rows C (m) coins) false (List.finRange ((slots ds - 1)+1)) ∧
      totals.oracleTime = CountingTrace.sideTime (keySize n ds.sum) (slots ds - 1) (rationalCellBudget a b) (m) (external hD hd A density spec rows C (m) coins) true (List.finRange ((slots ds - 1)+1)) +
        CountingTrace.sideTime (keySize n ds.sum) (slots ds - 1) (rationalCellBudget a b) (m) (external hD hd A density spec rows C (m) coins) false (List.finRange ((slots ds - 1)+1)) ∧
      totals.dispatches ≤ 8*totals.calls+2*((slots ds - 1)+1)*coefficientLocalBound (keySize n ds.sum) (m)+2*((slots ds - 1)+1)+3 ∧
      run.time ≤ (3*kE+6)*(preCost (program hD hd A density) (indices hD hd A density) S M T Dp+
        (totals.dispatches+2)*(bodyCost (program hD hd A density) (indices hD hd A density) S M T Dp+Ps.eval cap+1)+
        totals.oracleTime+postCost (program hD hd A density) (indices hD hd A density) S M T Dp+1) ∧
      run.cells ≤ (19+kE+1+1)*(2*max S (Ps.eval cap)+3) := by
  dsimp only
  let cap := Boundary.extentCap rows C density g
  let O := resourceSatOracle E density requestExtent cap
  have hv := valid hD hd A density
  obtain ⟨boundary,totals,events,htr,hpc,_,hgt,hbt,hcalls,htime,hend,hdispatch⟩ :=
    CountingTrace.initial_to_tables_trace (keySize n ds.sum) (slots ds - 1) (rationalCellBudget a b) (m) false (external hD hd A density spec rows C (m) coins)
  have hreach : (Reachable (keySize n ds.sum) (slots ds - 1) (rationalCellBudget a b) (m) false (external hD hd A density spec rows C (m) coins)) boundary := ⟨_,_,htr⟩
  have hr : Concrete.repair.den ((contextData hD hd A ds rows C (List.ofFn coins)),boundary.goodTable,boundary.badTable) = ((GeneralAlgorithm.output hD hd A rows C spec.service.solver (rationalCellBudget a b) (m) coins)).map toR := by
    change (GeneralRepairFL.generalF Install.wL GeneralInstalled.ri GeneralInstalled.ci
      Install.yR GeneralInstalled.ai GeneralInstalled.wi GeneralInstalled.gi).den _ = _
    rw [GeneralRepairFL.generalF_den,hgt,hbt]
    have h := GeneralBoundary.general_tables rows C (Factory.system hD hd A n ds).stages
      (Factory.circuits hD hd A n ds) (m)
      (LatentMachine.decodeCoins (Factory.length hD hd A n ds)
        (Factory.width hD hd A n ds) (m) coins) density spec (rationalCellBudget a b) (keySize n ds.sum)
      (seedB (data hD hd A).base (data hD hd A).den (keySize n ds.sum)) (List.ofFn coins)
    have hdecode := congrArg
      (fun omega => (TensorGeneral.output rows (TensorEncoding.circuitMap C)
        (PhysicalAlgorithm.decisions hD hd A (n:=n) (ds:=ds) rows C spec.service.solver)
        (rationalCellBudget a b) m omega).map toR)
      (LatentMachine.decodeCoins_eq (Factory.length hD hd A n ds)
        (Factory.width hD hd A n ds) m coins)
    exact h.trans hdecode
  have hloop := counting_repair_loop hD hd A density spec (n:=n) (ds:=ds) rows C (rationalCellBudget a b) (m) coins hg hbounds hS hm
    htr hpc (GeneralAlgorithm.output hD hd A rows C spec.service.solver (rationalCellBudget a b) (m) coins) hr (hfinished boundary hreach hpc hr)
  have hi := hinit.computes (hv.initial (input ds rows C a b c d (List.ofFn coins)))
  rw [Program.initializer_den] at hi
  simp only [Program.initialized,← hrep] at hi
  change FL.Computes (program hD hd A density) ((indices hD hd A density)).init (bitsVal (input ds rows C a b c d (List.ofFn coins))) ((fun s : Config => (TArg ContextFL.TX).enc ((fun s : Config => (encCtx (keySize n ds.sum) (slots ds - 1) (rationalCellBudget a b) (m) (contextData hD hd A ds rows C (List.ofFn coins)),encCfg s)) s)) (initial (keySize n ds.sum) (slots ds - 1) (m))) M T Dp at hi
  have hd0 := (hbounds.done (initial (keySize n ds.sum) (slots ds - 1) (m)) reachable_initial).computes (hv.isDone _)
  rw [Program.isDone_den (source hD hd A density) Concrete.query (data hD hd A).base (data hD hd A).den density
    (Trans.HashCallees.encConsts D A) (Install.thePg hD hd A) (Trans.Hash.gNbr actualMGG)
    (keySize n ds.sum) (slots ds - 1) (rationalCellBudget a b) (m) (contextData hD hd A ds rows C (List.ofFn coins)) (initial (keySize n ds.sum) (slots ds - 1) (m)) (by simp [initial])] at hd0
  have hpre := preamble_run (O:=O) hS hm hi hd0
  have hout := (houtput boundary hreach hpc hr).computes (hv.output _)
  rw [Trans.Bounds.outputF_den] at hout
  have hpost := postamble_run (O:=O) hS hout hloop.fits_end
  have hreg := hpre.seq (hloop.seq hpost)
  have hword : outputWord (GeneralAlgorithm.outputVector hD hd A rows C spec.service.solver (rationalCellBudget a b) (m) coins) = ratioWord (GeneralAlgorithm.output hD hd A rows C spec.service.solver (rationalCellBudget a b) (m) coins) := by
    unfold outputWord ratioWord
    rw [GeneralAlgorithm.outputVector_list]
  have hreg' : ∃ u : Regs 20,
      ORuns O S (mainProg (program hD hd A density) (indices hD hd A density)).body (inputRegs (R:=19) (input ds rows C a b c d (List.ofFn coins))) u
        (preCost (program hD hd A density) (indices hD hd A density) S M T Dp+(totals.dispatches+2)*(bodyCost (program hD hd A density) (indices hD hd A density) S M T Dp+Ps.eval cap+1)+
          totals.oracleTime+postCost (program hD hd A density) (indices hD hd A density) S M T Dp) ∧ u rOUT = outputWord (GeneralAlgorithm.outputVector hD hd A rows C spec.service.solver (rationalCellBudget a b) (m) coins) := by
    refine ⟨_,hreg.mono (by dsimp only [cap]; omega),?_⟩
    rw [hword]
    rfl
  obtain ⟨run,hout,ht,hcells⟩ := tape_run_resource spec hreg'
  exact ⟨totals,run,hout,hcalls,htime,hdispatch,ht,hcells⟩

end QecReliability.TensorMachineG.Runtime
end
