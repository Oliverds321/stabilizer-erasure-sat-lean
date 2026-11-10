import GeneralMachineAgreement
import GeneralMachineBudgetEnvelope
import GeneralMachineCompleted

/-! The fixed multiclass finite-tape machine completes with its actual repaired
rational table. All callback budgets are discharged; resource formulas retain
actual oracle totals for the final SAT-rate composition. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
namespace QecReliability.TensorMachineG.Runtime
open QecReliability.TensorMachine QecReliability.TensorMachine.Runtime
open FL Trans.Control Trans.Wire RegMachine Assembly RationalOutput Final
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.MultiTape

variable {D t : ℕ} (hD : D=16^384) (hd : D=256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {Pt Ps : PolynomialEnvelope} {timeE : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps timeE requestExtent)


set_option maxHeartbeats 2000000 in
/-- One shared polynomial is fixed before every runtime input. This theorem
runs the installed program and resource-aware embedded SAT machine, including
exact anchors, full tensor repair, and serialization of the output vector. -/
theorem polynomial_completion : ∃ P : PolynomialEnvelope, ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds) (rationalRepetitionBudget (2*slots ds) c d)) → Bool),
    let L := Boundary.resourceSize rows C a b c d
    let q := keySize n ds.sum
    let r := slots ds-1
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*slots ds) c d
    let ext := external hD hd A density spec (n:=n) (ds:=ds) rows C m coins
    let Bd : Assembly.Budget := ⟨P,P,P⟩
    let cap := Boundary.extentCap rows C density ((data hD hd A).Cfixed*(q+1))
    ∃ totals : Totals, ∃ run : Completed (theMachine E (program hD hd A density) (indices hD hd A density))
      (input ds rows C a b c d (List.ofFn coins)),
      Outputs (theMachine E (program hD hd A density) (indices hD hd A density)) run (outTape kE)
        (GeneralAlgorithm.outputVector hD hd A (n:=n) (ds:=ds) rows C spec.service.solver B m coins) ∧
      totals.calls = CountingTrace.sideCalls q r B m ext true (List.finRange (r+1))+
        CountingTrace.sideCalls q r B m ext false (List.finRange (r+1)) ∧
      totals.oracleTime = CountingTrace.sideTime q r B m ext true (List.finRange (r+1))+
        CountingTrace.sideTime q r B m ext false (List.finRange (r+1)) ∧
      totals.dispatches≤8*totals.calls+2*(r+1)*coefficientLocalBound q m+2*(r+1)+3 ∧
      run.time≤(3*kE+6)*(preBound (program hD hd A density) (indices hD hd A density) Bd L+
        (totals.dispatches+2)*(iterBound (program hD hd A density) (indices hD hd A density) Bd L+Ps.eval cap+1)+
        totals.oracleTime+postBound (program hD hd A density) (indices hD hd A density) Bd L+1) ∧
      run.cells≤(19+kE+1+1)*(2*max (regBound (program hD hd A density) (indices hD hd A density) Bd L) (Ps.eval cap)+3) := by
  obtain ⟨P,S,hP⟩ := budget_envelope hD hd A density spec
  refine ⟨P,?_⟩
  intro n ds rows C a b c d ha hc coins
  generalize hrep : rationalRepetitionBudget (2*slots ds) c d = m at coins ⊢
  let L := Boundary.resourceSize rows C a b c d
  let Bd : Assembly.Budget := ⟨P,P,P⟩
  have hb := hP (n:=n) (ds:=ds) rows C a b c d ha hc m hrep.symm coins
  have hg := Factory.gates_all hD hd A n ds
  have hrun := completed_of_budgets hD hd A density spec (n:=n) (ds:=ds)
    rows C a b c d m coins hrep.symm hg hb.loop
    (regBound_hS (program hD hd A density) (indices hD hd A density) Bd L) (regBound_hm (program hD hd A density) (indices hD hd A density) Bd L) hb.initial
    (fun s hs hp he => (hb.finished s hs hp
      (GeneralAlgorithm.output hD hd A (n:=n) (ds:=ds) rows C spec.service.solver
        (rationalCellBudget a b) m coins) he).1)
    (fun s hs hp he => (hb.finished s hs hp
      (GeneralAlgorithm.output hD hd A (n:=n) (ds:=ds) rows C spec.service.solver
        (rationalCellBudget a b) m coins) he).2)
  exact hrun

end QecReliability.TensorMachineG.Runtime
end
