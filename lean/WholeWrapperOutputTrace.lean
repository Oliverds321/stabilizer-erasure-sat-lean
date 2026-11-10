import WholeWrapperRepairFrame

/-! Full actual-controller termination and SAME
source raw caches, rational output, and operation report. This does not assert
SourceWholeEvents or physical bit-machine runtime. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open RationalOutput

/-- The original repair report always includes the incoming denominator. -/
theorem run_previous_den_le (shape : Bool) (r j : ℕ) (a ell previous : Ratio)
    (gs bs : List Entry) :
    previous.den≤(LinearRepair.run shape r a ell j previous gs bs).maxAccumulatorDen := by
  cases gs with
  | nil => exact le_rfl
  | cons g gs =>
      cases bs with
      | nil => exact le_rfl
      | cons b bs => exact le_max_left _ _

variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (service : SATService)
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) (D : ℕ) (ext : External)
    (hboundary : BoundaryCorrect rows C H K service m ω D ext)

include hboundary in
/-- Only the primitive boundary-fidelity hypothesis is used. The trace starts
at the actual literal initial controller and derives exact old cache/output
and ALL original report fields. Arithmetic remains macro arithmetic; this is
not a theorem about total finite-machine time or encoded storage. -/
theorem initial_output_trace (shape : Bool) :
    let cache := prepare rows C H K service.solver B m ω
    ∃ final totals events,
      Trace (keySize n r) r B m shape ext (initial (keySize n r) r m) totals events final ∧
      HasOutput final cache.good.entries cache.bad.entries (LinearRepair.fromCache shape rows C cache) ∧
      totals.calls=cache.calls ∧
      totals.oracleTime=(QuantumService.prepareMeasured rows C H K service B m ω).oracleTime ∧
      totals.endpointTime=(ext.endpoint false).time+(ext.endpoint true).time ∧
      totals.calls≤totalCallCap (keySize n r) r B m ∧
      totals.dispatches≤8*cache.calls+2*(r+1)*coefficientLocalBound (keySize n r) m+4*(r+1)+7 := by
  let cache := prepare rows C H K service.solver B m ω
  let target := LinearRepair.fromCache shape rows C cache
  obtain ⟨s,stotal,events,hstart,hpc,hcode,hgood,hbad,hrepairgood,hrepairbad,
      hzero,hone,hprevious,hindex,houtrev,hvisits,hratios,horders,htests,hmaxstart,
      hcalls,htime,hendpoint,hcap,hsteps⟩ :=
    initial_to_repair_trace rows C H K service B m ω D ext hboundary shape
  have hden : s.previous.den≤s.maxAccumulatorDen := by rw [hprevious,hmaxstart]
  obtain ⟨mid,hrepair,hmidpc,hvalues,hmidvisits,hmidratios,hmidorders,hmidtests,hmidmax,
      hmidout,hframe⟩ :=
    repair_framed (keySize n r) r B m shape ext cache.good.entries cache.bad.entries
      s hpc hrepairgood hrepairbad (by rw [cache.good.length_eq,cache.bad.length_eq]) hden
  have hsource : LinearRepair.run shape r s.endpoint0 s.endpoint1 s.repairIndex s.previous
      cache.good.entries cache.bad.entries=target := by
    simp [hprevious,hindex,hzero,hone,target,LinearRepair.fromCache]
  rw [hsource] at hvalues hmidvisits hmidratios hmidorders hmidtests hmidmax
  have hvalues' : mid.outputRev=target.values.reverse := by simpa [houtrev] using hvalues
  have hmidgood : mid.goodTable=cache.good.entries := by
    have h := congrArg Config.goodTable hframe
    simpa [repairFrame,hgood] using h
  have hmidbad : mid.badTable=cache.bad.entries := by
    have h := congrArg Config.badTable hframe
    simpa [repairFrame,hbad] using h
  have hge : (Ratio.dyadic rows (circuitMap C ∅)).den≤target.maxAccumulatorDen :=
    run_previous_den_le shape r 0 _ _ _ cache.good.entries cache.bad.entries
  have hmidmax' : mid.maxAccumulatorDen=target.maxAccumulatorDen := by
    simpa [hmaxstart,hzero,max_eq_right hge] using hmidmax
  let final : Config := { mid with pc := .done,outputRev := [],output := target.values }
  have hreverse : LocalTrace (keySize n r) r B m shape ext mid (target.values.length+1) final := by
    have h := reverseOutput_trace (keySize n r) r B m shape ext mid.outputRev mid hmidpc rfl
    simpa [hvalues',hmidout,final] using h
  have hpost := hrepair.trans hreverse
  have path := hstart.trans hpost.toTrace
  let totals := Totals.append stotal (localTotals (cache.good.entries.length+1+(target.values.length+1)))
  refine ⟨final,totals,events,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [totals] using path
  · refine ⟨rfl,hmidgood,hmidbad,rfl,?_,?_,?_,?_,hmidmax'⟩
    · simpa [final,hvisits] using hmidvisits
    · simpa [final,hratios] using hmidratios
    · simpa [final,horders] using hmidorders
    · simpa [final,htests] using hmidtests
  · simpa [totals,Totals.append,localTotals] using hcalls
  · simpa [totals,Totals.append,localTotals] using htime
  · simpa [totals,Totals.append,localTotals] using hendpoint
  · simpa [totals,Totals.append,localTotals] using hcap
  · simp only [totals,Totals.append,localTotals]
    have hlen : target.values.length=r+1 := LinearRepair.fromCache_length shape rows C cache
    rw [cache.good.length_eq,hlen]
    omega

end QecReliability.OracleCost.WholeWrapperCandidate
