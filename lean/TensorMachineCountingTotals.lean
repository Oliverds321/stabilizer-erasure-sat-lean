import TensorCountingTimeBudget
import TensorMachineAgreement

/-! Uniform total call, dispatch, and SAT-time bounds for the actual fixed
factory counting trace. The coefficient-grid cardinality is charged only in
the polynomial prefactor, never inside the SAT rate argument. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
namespace QecReliability.TensorMachine.Runtime
open FL Trans.Control
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.MultiTape

def countingCallPolynomial (L : ℕ) : ℕ := 512*(L+1)^4
def countingDispatchPolynomial (L : ℕ) : ℕ :=
  8*countingCallPolynomial L+2*L*coefficientLocalBound (2*L) (3*L+2)+2*L+3

private theorem totals_polynomial (P : PolynomialEnvelope) :
    Assembly.PolyBounded (fun L => P.eval L+countingCallPolynomial L+countingDispatchPolynomial L) := by
  unfold countingDispatchPolynomial countingCallPolynomial coefficientLocalBound
  poly_bounded

private theorem dispatch_bound (q Q m B L calls steps : ℕ)
    (hq : q≤2*L) (hQ : Q≤L) (hm : 2*m+1≤6*L+5)
    (hc : calls≤countingCallPolynomial L*(B+1))
    (hs : steps≤8*calls+2*Q*coefficientLocalBound q m+2*Q+3) :
    steps≤countingDispatchPolynomial L*(B+1) := by
  have hm' : m≤3*L+2 := by omega
  have he : coefficientLocalBound q m≤coefficientLocalBound (2*L) (3*L+2) := by
    unfold coefficientLocalBound
    gcongr
  have hmul := Nat.mul_le_mul (show 2*Q≤2*L by omega) he
  unfold countingDispatchPolynomial
  nlinarith [Nat.zero_le ((2*L*coefficientLocalBound (2*L) (3*L+2)+2*L+3)*B)]

variable {D t : ℕ} (hD : D=16^384) (hd : D=256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps T requestExtent) (hT : Monotone T)

include hT in
theorem counting_time_budget : ∃ P : PolynomialEnvelope, ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d B : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds) (rationalRepetitionBudget (2*slots ds) c d)) → Bool),
    let m := rationalRepetitionBudget (2*slots ds) c d
    let ext := external hD hd A density spec rows C m coins
    let L := Boundary.resourceSize rows C a b c d
    CountingTrace.sideTime (keySize n ds.sum) (slots ds-1) B m ext true (List.finRange (slots ds-1+1))+
      CountingTrace.sideTime (keySize n ds.sum) (slots ds-1) B m ext false (List.finRange (slots ds-1+1))≤
        P.eval L*(B+1)*T (Boundary.variableCoefficient density (data hD hd A).Cfixed*
          (Boundary.structuralSize rows C a b c d+1)) := by
  obtain ⟨P,hP⟩ := Boundary.total_time_input spec hT (data hD hd A).Cfixed
  refine ⟨P,?_⟩
  intro n ds rows C a b c d B ha hc coins
  exact hP rows C (Factory.system hD hd A n ds).stages (Factory.circuits hD hd A n ds)
    (Factory.gates_all hD hd A n ds) a b c d B ha hc
    (LatentMachine.decodeCoins (Factory.length hD hd A n ds) (Factory.width hD hd A n ds)
      (rationalRepetitionBudget (2*slots ds) c d) coins)

include hT in
/-- Actual initial-to-table execution with one common input polynomial for
dispatches, SAT calls, and the prefactor of accumulated SAT service time. -/
theorem counting_totals_budget : ∃ P : PolynomialEnvelope, ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds) (rationalRepetitionBudget (2*slots ds) c d)) → Bool),
    let m := rationalRepetitionBudget (2*slots ds) c d
    let B := rationalCellBudget a b
    let ext := external hD hd A density spec rows C m coins
    let L := Boundary.resourceSize rows C a b c d
    ∃ s totals events,
      Trace (keySize n ds.sum) (slots ds-1) B m false ext
        (initial (keySize n ds.sum) (slots ds-1) m) totals events s ∧
      s.pc=.endpointZero ∧ s.code=[] ∧
      s.goodTable=CountingTrace.sideEntries (keySize n ds.sum) (slots ds-1) B m ext true
        (List.finRange (slots ds-1+1)) ∧
      s.badTable=CountingTrace.sideEntries (keySize n ds.sum) (slots ds-1) B m ext false
        (List.finRange (slots ds-1+1)) ∧
      totals.calls≤P.eval L*(B+1) ∧ totals.dispatches≤P.eval L*(B+1) ∧
      totals.oracleTime≤P.eval L*(B+1)*
        T (Boundary.variableCoefficient density (data hD hd A).Cfixed*
          (Boundary.structuralSize rows C a b c d+1)) ∧ totals.endpointTime=0 := by
  obtain ⟨Ptime,htime⟩ := counting_time_budget hD hd A density spec hT
  obtain ⟨P,hP⟩ := (totals_polynomial Ptime).envelope
  refine ⟨P,?_⟩
  intro n ds rows C a b c d ha hc coins
  dsimp only
  let L := Boundary.resourceSize rows C a b c d
  let m := rationalRepetitionBudget (2*slots ds) c d
  let B := rationalCellBudget a b
  let ext := external hD hd A density spec rows C m coins
  obtain ⟨s,totals,events,htrace,hpc,hcode,hgood,hbad,hcalls,horacle,hend,hsteps⟩ :=
    CountingTrace.initial_to_tables_trace (keySize n ds.sum) (slots ds-1) B m false ext
  have hcall := Boundary.total_calls_input rows C (Factory.system hD hd A n ds).stages
    (Factory.circuits hD hd A n ds) spec a b c d B ha hc
    (LatentMachine.decodeCoins (Factory.length hD hd A n ds) (Factory.width hD hd A n ds) m coins)
  have hcapped : totals.calls≤countingCallPolynomial L*(B+1) := by
    rw [hcalls]
    exact hcall
  obtain ⟨_,hq,_,hm,_⟩ := Boundary.resource_parameters rows C a b c d ha hc
  have hQ : slots ds≤L := by dsimp only [L,Boundary.resourceSize]; omega
  have hstep' : totals.dispatches≤countingDispatchPolynomial L*(B+1) := by
    rw [Boundary.slots_pred_succ] at hsteps
    exact dispatch_bound _ _ _ _ _ _ _ hq hQ hm hcapped hsteps
  have horacle' := htime (n:=n) (ds:=ds) rows C a b c d B ha hc coins
  have hpoly := hP L
  have hpTime : Ptime.eval L≤P.eval L := by omega
  have hpCalls : countingCallPolynomial L≤P.eval L := by omega
  have hpSteps : countingDispatchPolynomial L≤P.eval L := by omega
  refine ⟨s,totals,events,htrace,hpc,hcode,hgood,hbad,
    hcapped.trans (Nat.mul_le_mul_right (B+1) hpCalls),
    hstep'.trans (Nat.mul_le_mul_right (B+1) hpSteps),?_,hend⟩
  rw [horacle]
  exact horacle'.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right (B+1) hpTime))

end QecReliability.TensorMachine.Runtime
