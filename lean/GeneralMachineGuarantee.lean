import GeneralMachineAgreement
import GeneralMachinePolynomial
import TensorMachineTotalsFromEqualities
import TensorMachineTotalResources
import GeneralCountingOutput
import TensorMachineStructuralTime

/-! Closed fixed-machine tensor reliability guarantees. All parser, controller,
repair, serialization and interpreter budgets are derived from the input. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
namespace QecReliability.TensorMachineG.Runtime
open QecReliability.TensorMachine QecReliability.TensorMachine.Runtime
open FL Assembly RationalOutput Final
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.MultiTape QecPhysical QecPhysical.Stabilizer

variable {D t : ℕ} (hD : D=16^384) (hd : D=256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps T requestExtent) (hT : Monotone T)

local notation "PP" => program hD hd A density
local notation "II" => indices hD hd A density
local notation "MACHINE" => theMachine E PP II

include hT in
theorem bounded_completion : ∃ Ptime Pspace : PolynomialEnvelope, ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds) (rationalRepetitionBudget (2*slots ds) c d)) → Bool),
    let L := Boundary.resourceSize rows C a b c d
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*slots ds) c d
    ∃ run : Completed MACHINE (input ds rows C a b c d (List.ofFn coins)),
      Outputs MACHINE run (outTape kE)
        (GeneralAlgorithm.outputVector hD hd A (n:=n) (ds:=ds) rows C spec.service.solver B m coins) ∧
      run.time ≤ Ptime.eval L*(B+1)*(T (Boundary.variableCoefficient density
        (data hD hd A).Cfixed*(Boundary.satStructuralSize rows C+1))+1) ∧
      run.cells ≤ Pspace.eval L := by
  obtain ⟨P,hP⟩ := polynomial_completion hD hd A density spec
  obtain ⟨Ptot,htot⟩ := counting_bounds_of_totals hD hd A density spec hT
  obtain ⟨Poracle,horacleBound⟩ := structural_time_budget hD hd A density spec hT
  obtain ⟨Pcap,hcap⟩ := (Boundary.extentPolynomial_pb density (data hD hd A).Cfixed).envelope
  obtain ⟨Ptime,Pspace,hres⟩ := completion_resource_envelopes PP II ⟨P,P,P⟩ Pcap Ptot Poracle Ps kE
  refine ⟨Ptime,Pspace,?_⟩
  intro n ds rows C a b c d ha hc coins
  obtain ⟨totals,run,hout,hcalls,horacle,hdispatch,htime,hspace⟩ :=
    hP (n:=n) (ds:=ds) rows C a b c d ha hc coins
  rw [Boundary.slots_pred_succ] at hdispatch
  obtain ⟨_,hdsp,_⟩ := htot (n:=n) (ds:=ds) rows C a b c d ha hc coins totals
    hcalls horacle hdispatch
  have horc := horacleBound (n:=n) (ds:=ds) rows C a b c d (rationalCellBudget a b) ha hc coins
  dsimp only at horc
  rw [← horacle] at horc
  have hi := (Boundary.input_caps rows C a b c d (data hD hd A).Cfixed density ha hc).2
  have hic := hi.trans ((Boundary.extentPolynomial_mono density (data hD hd A).Cfixed
    (Boundary.structuralSize_le_resource rows C a b c d)).trans (hcap _))
  have hr := hres (Boundary.resourceSize rows C a b c d) (rationalCellBudget a b)
    (T (Boundary.variableCoefficient density (data hD hd A).Cfixed*
      (Boundary.satStructuralSize rows C+1))) _ totals.dispatches totals.oracleTime hic hdsp horc
  exact ⟨run,hout,htime.trans hr.1,hspace.trans hr.2⟩

include hT in
/-- General circuits (no monotonicity): every coin string gives a completed run
within the polynomial envelopes whose output is the corner-replaced estimate
vector, and one coin event gives two-tail relative accuracy on the whole cube. -/
theorem tensor_machine_guarantee_general : ∃ Ptime Pspace : PolynomialEnvelope, ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → a≤b → 0<c → 0<d →
    ∀ (lift : Lift (rowSpace rows)),
    let L := Boundary.resourceSize rows C a b c d
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*slots ds) c d
    let N := CodeHash.repeatBits (Factory.length hD hd A n ds) (Factory.width hD hd A n ds) m
    (∀ coins : Fin N → Bool,
      ∃ run : Completed MACHINE (input ds rows C a b c d (List.ofFn coins)),
        Outputs MACHINE run (outTape kE)
          (GeneralAlgorithm.outputVector hD hd A (n:=n) (ds:=ds) rows C spec.service.solver B m coins) ∧
        run.time ≤ Ptime.eval L*(B+1)*(T (Boundary.variableCoefficient density
          (data hD hd A).Cfixed*(Boundary.satStructuralSize rows C+1))+1) ∧
        run.cells ≤ Pspace.eval L) ∧
    (∀ (coins : Fin N → Bool) (run : Completed MACHINE (input ds rows C a b c d (List.ofFn coins)))
      (v : Vector (slots ds-1)), Outputs MACHINE run (outTape kE) v →
        v = GeneralAlgorithm.outputVector hD hd A (n:=n) (ds:=ds) rows C spec.service.solver B m coins) ∧
    1-(c:ℝ)/d ≤ (uniformLaw (CodeHash.BitTape N)).prob
      (fun coins => ∀ (run : Completed MACHINE (input ds rows C a b c d (List.ofFn coins)))
        (v : Vector (slots ds-1)), Outputs MACHINE run (outTape kE) v →
          lift.TensorPhysicalAccuracy (TensorEncoding.circuitMap C) ((a:ℝ)/b) (vectorCurve ds v)) := by
  obtain ⟨Ptime,Pspace,hruns⟩ := bounded_completion hD hd A density spec hT
  refine ⟨Ptime,Pspace,?_⟩
  intro n ds rows C a b c d ha hab hc hdpos lift
  have hr := hruns (n:=n) (ds:=ds) rows C a b c d ha hc
  have hp := GeneralAlgorithm.general_output_transfer hD hd A (n:=n) (ds:=ds) rows C
    spec.service.solver a b c d lift ha hab hc hdpos MACHINE (outTape kE)
    (fun coins => input ds rows C a b c d (List.ofFn coins))
    (fun coins => by obtain ⟨run,hout,_,_⟩ := hr coins; exact ⟨run,hout⟩)
  exact ⟨hr,hp⟩

end QecReliability.TensorMachineG.Runtime
