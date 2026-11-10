import WholeWrapperOutputTrace

/-! The output contract uses the explicit broad
polynomial actually established by the trace chain, not the older unproved
`dispatchBound`. Source-event provenance is deliberately a separate obligation.
No contract below is a hypothesis of its own proof. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open RationalOutput

/-- Pure polynomial in q,r,B,m after unfolding the two elementary definitions.
This is macro dispatch only: all primitive bit-operation costs remain separate. -/
def macroDispatchBound (q r B m : ℕ) : ℕ :=
  8*totalCallCap q r B m+2*(r+1)*coefficientLocalBound q m+4*(r+1)+7

variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (service : SATService)
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) (D : ℕ) (shape : Bool) (ext : External)

/-- Updated exact-output contract. Unlike the original whole ordered target,
this name does not claim SourceWholeEvents. All cache/report/value identities,
call counts, and service times remain the original ones. -/
def WholeOutputRefinementClaim : Prop :=
  BoundaryCorrect rows C H K service m ω D ext →
  ∃ final totals events,
    Trace (keySize n r) r B m shape ext (initial (keySize n r) r m) totals events final ∧
    HasOutput final
      (prepare rows C H K service.solver B m ω).good.entries
      (prepare rows C H K service.solver B m ω).bad.entries
      (LinearRepair.fromCache shape rows C (prepare rows C H K service.solver B m ω)) ∧
    totals.calls=(prepare rows C H K service.solver B m ω).calls ∧
    totals.oracleTime=(QuantumService.prepareMeasured rows C H K service B m ω).oracleTime ∧
    totals.endpointTime=(ext.endpoint false).time+(ext.endpoint true).time ∧
    totals.calls≤totalCallCap (keySize n r) r B m ∧
    totals.dispatches≤macroDispatchBound (keySize n r) r B m

/-- Direct derivation, NOT an assumed refinement/resource contract. -/
theorem whole_output_refinement :
    WholeOutputRefinementClaim rows C H K service B m ω D shape ext := by
  intro hboundary
  obtain ⟨final,totals,events,htrace,hout,hcalls,htime,hendpoint,hcap,hdispatch⟩ :=
    initial_output_trace rows C H K service B m ω D ext hboundary shape
  refine ⟨final,totals,events,htrace,hout,hcalls,htime,hendpoint,hcap,?_⟩
  unfold macroDispatchBound
  rw [← hcalls] at hdispatch
  omega

end QecReliability.OracleCost.WholeWrapperCandidate
