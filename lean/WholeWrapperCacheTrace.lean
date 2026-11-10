import WholeWrapperCoefficientBatch

/-! Exact two-sided cached source materialization
from the actual initial controller. Does not yet claim repaired output or the
source-event predicate. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (service : SATService)
    (B m : ℕ) (ω : Fin (2*m+1) → Ω)

/-- Exact aggregate identities for the SAME source tables. -/
theorem sideCalls_eq_prepare :
    sideCalls rows C H K service B m ω true (List.finRange (r+1))+
      sideCalls rows C H K service B m ω false (List.finRange (r+1))=
        (prepare rows C H K service.solver B m ω).calls := by
  simp [sideCalls,sideEntries_finRange,prepare_eq_cached,CoefficientTable.calls,CountTable.calls]

theorem sideTime_eq_prepareMeasured :
    sideTime rows C H K service B m ω true (List.finRange (r+1))+
      sideTime rows C H K service B m ω false (List.finRange (r+1))=
        (QuantumService.prepareMeasured rows C H K service B m ω).oracleTime := by
  simp only [sideTime,QuantumService.prepareMeasured,QuantumService.MeasuredCoefficients.oracleTime,
    CachedControl.MeasuredTable.oracleTime,CachedControl.MeasuredTable.build,
    List.map_ofFn,List.ofFn_eq_map,List.map_map,Function.comp_def]

variable (D : ℕ) (ext : External)
    (hboundary : BoundaryCorrect rows C H K service m ω D ext)

include hboundary in
/-- Both actual ascending coefficient blocks produce literally the old
`prepare` caches, stored in reverse pending the actual finish loops. The only
semantic premise is primitive BoundaryCorrect. All entry-state/report/frame
facts follow from the literal initial Config and the actual stores. -/
theorem initial_cache_trace (shape : Bool) :
    let cache := prepare rows C H K service.solver B m ω
    ∃ t totals events,
      Trace (keySize n r) r B m shape ext (initial (keySize n r) r m) totals events t ∧
      t.pc=.fetch ∧ t.code=[.finish] ∧
      t.goodRev=cache.good.entries.reverse ∧ t.badRev=cache.bad.entries.reverse ∧
      cacheFrame t=cacheFrame { initial (keySize n r) r m with
        code := [.finish],
        goodRev := cache.good.entries.reverse,badRev := cache.bad.entries.reverse } ∧
      totals.calls=cache.calls ∧
      totals.oracleTime=(QuantumService.prepareMeasured rows C H K service B m ω).oracleTime ∧
      totals.endpointTime=0 ∧ totals.calls≤totalCallCap (keySize n r) r B m ∧
      totals.dispatches≤8*cache.calls+2*(r+1)*coefficientLocalBound (keySize n r) m := by
  let cache := prepare rows C H K service.solver B m ω
  let js := List.finRange (r+1)
  let tailCode := js.flatMap (fun j => coefficientCode (keySize n r) m false j.val)++[.finish]
  obtain ⟨mid,gtotal,gevents,hgood,hmidpc,hmidcode,hmidgood,hmidbad,hmidframe,
      hgoodcalls,hgoodtime,hgoodendpoint,hgoodsteps⟩ :=
    coefficients_trace rows C H K service B m ω D ext hboundary shape true js
      (initial (keySize n r) r m) tailCode rfl
      (by simp only [initial,program_finRange,tailCode,js,List.append_assoc])
  have hmidgood' : mid.goodRev=cache.good.entries.reverse := by
    simpa [initial,cache,prepare_eq_cached,js,sideEntries_finRange] using hmidgood
  have hmidbad' : mid.badRev=[] := by simpa [initial] using hmidbad
  obtain ⟨t,btotal,bevents,hbad,htpc,htcode,htgood,htbad,htframe,
      hbadcalls,hbadtime,hbadendpoint,hbadsteps⟩ :=
    coefficients_trace rows C H K service B m ω D ext hboundary shape false js
      mid [.finish] hmidpc hmidcode
  have htgood' : t.goodRev=cache.good.entries.reverse := by simpa [hmidgood'] using htgood
  have htbad' : t.badRev=cache.bad.entries.reverse := by
    simpa [cache,prepare_eq_cached,js,sideEntries_finRange,hmidbad'] using htbad
  have hf : cacheFrame t=cacheFrame { initial (keySize n r) r m with
      code := [.finish],
      goodRev := cache.good.entries.reverse,badRev := cache.bad.entries.reverse } := by
    have hh := congrArg (fun a : Config => { a with
      code := [.finish],trialsRev := [],
      badRev := cache.bad.entries.reverse }) hmidframe
    have hh' : cacheFrame { mid with code := [.finish],trialsRev := [],badRev := cache.bad.entries.reverse }=
        cacheFrame { initial (keySize n r) r m with
          code := [.finish],
          goodRev := cache.good.entries.reverse,badRev := cache.bad.entries.reverse } := by
      simpa [cacheFrame,coefficientFrame,sortWorkFrame,repetitionFrame,trialFrame,
        selectionFrame,batchFrame,prefixFrame,initial,js,cache,prepare_eq_cached,sideEntries_finRange] using hh
    have htframe' : cacheFrame t=cacheFrame { mid with
        code := [.finish],trialsRev := [],
        badRev := cache.bad.entries.reverse } := by
      simpa [cache,prepare_eq_cached,js,sideEntries_finRange,hmidbad'] using htframe
    exact htframe'.trans hh'
  let totals := Totals.append gtotal btotal
  have hcalls : totals.calls=cache.calls := by
    simpa [totals,Totals.append,hgoodcalls,hbadcalls,js,cache]
      using sideCalls_eq_prepare rows C H K service B m ω
  refine ⟨t,totals,gevents++bevents,hgood.trans hbad,htpc,htcode,htgood',htbad',hf,
    hcalls,?_,?_,?_,?_⟩
  · simpa [totals,Totals.append,hgoodtime,hbadtime,js]
      using sideTime_eq_prepareMeasured rows C H K service B m ω
  · simp [totals,Totals.append,hgoodendpoint,hbadendpoint]
  · rw [hcalls]
    exact prepare_calls rows C H K service.solver B m ω
  · have hsum := sideCalls_eq_prepare rows C H K service B m ω
    simp only [js,List.length_finRange] at hgoodsteps hbadsteps
    change _=cache.calls at hsum
    simp only [totals,Totals.append]
    nlinarith

include hboundary in
/-- Actual finish reversals expose the forward source cache and actual endpoint
values, ready for a framed repair theorem. Endpoint acquisition time/space is
charged by the two real endpoint edges, never hidden in controller dispatch. -/
theorem initial_to_repair_trace (shape : Bool) :
    let cache := prepare rows C H K service.solver B m ω
    ∃ t totals events,
      Trace (keySize n r) r B m shape ext (initial (keySize n r) r m) totals events t ∧
      t.pc=.repair ∧ t.code=[] ∧
      t.goodTable=cache.good.entries ∧ t.badTable=cache.bad.entries ∧
      t.repairGood=cache.good.entries ∧ t.repairBad=cache.bad.entries ∧
      t.endpoint0=RationalOutput.Ratio.dyadic rows (circuitMap C ∅) ∧
      t.endpoint1=RationalOutput.Ratio.dyadic rows (circuitMap C Finset.univ) ∧
      t.previous=t.endpoint0 ∧ t.repairIndex=0 ∧ t.outputRev=[] ∧
      t.pairVisits=0 ∧ t.ratioBuilds=0 ∧ t.orderComparisons=0 ∧ t.endpointTests=0 ∧
      t.maxAccumulatorDen=t.endpoint0.den ∧
      totals.calls=cache.calls ∧
      totals.oracleTime=(QuantumService.prepareMeasured rows C H K service B m ω).oracleTime ∧
      totals.endpointTime=(ext.endpoint false).time+(ext.endpoint true).time ∧
      totals.calls≤totalCallCap (keySize n r) r B m ∧
      totals.dispatches≤8*cache.calls+2*(r+1)*coefficientLocalBound (keySize n r) m+2*(r+1)+5 := by
  let cache := prepare rows C H K service.solver B m ω
  obtain ⟨s,stotal,events,hcache,hpc,hcode,hgood,hbad,hframe,hcalls,htime,hendpoint,hcap,hsteps⟩ :=
    initial_cache_trace rows C H K service B m ω D ext hboundary shape
  have hvisits : s.pairVisits=0 := by
    simpa [cacheFrame,coefficientFrame,sortWorkFrame,repetitionFrame,trialFrame,
      selectionFrame,batchFrame,prefixFrame,initial] using congrArg Config.pairVisits hframe
  have hratios : s.ratioBuilds=0 := by
    simpa [cacheFrame,coefficientFrame,sortWorkFrame,repetitionFrame,trialFrame,
      selectionFrame,batchFrame,prefixFrame,initial] using congrArg Config.ratioBuilds hframe
  have horders : s.orderComparisons=0 := by
    simpa [cacheFrame,coefficientFrame,sortWorkFrame,repetitionFrame,trialFrame,
      selectionFrame,batchFrame,prefixFrame,initial] using congrArg Config.orderComparisons hframe
  have htests : s.endpointTests=0 := by
    simpa [cacheFrame,coefficientFrame,sortWorkFrame,repetitionFrame,trialFrame,
      selectionFrame,batchFrame,prefixFrame,initial] using congrArg Config.endpointTests hframe
  let final : Config := { s with
    pc := .repair,code := [],goodRev := [],badRev := [],
    goodTable := s.goodRev.reverse,badTable := s.badRev.reverse,pairSrc := [],pairDst := [],
    endpoint0 := (ext.endpoint false).value,endpoint1 := (ext.endpoint true).value,
    previous := (ext.endpoint false).value,repairGood := s.goodRev.reverse,
    repairBad := s.badRev.reverse,repairIndex := 0,outputRev := [],
    maxAccumulatorDen := (ext.endpoint false).value.den }
  have hfinish := finish_to_repair_trace (keySize n r) r B m shape ext s [] hpc hcode
  have path := hcache.trans hfinish
  let totals := Totals.append stotal
    { dispatches := s.goodRev.length+s.badRev.length+5,
      endpointTime := (ext.endpoint false).time+(ext.endpoint true).time,
      boundaryPeak := max (ext.endpoint false).space (ext.endpoint true).space }
  refine ⟨final,totals,events,?_,rfl,rfl,?_,?_,?_,?_,?_,?_,rfl,rfl,rfl,
    hvisits,hratios,horders,htests,rfl,?_,?_,?_,?_,?_⟩
  · simpa [totals,final] using path
  · simpa [final,hgood] using List.reverse_reverse cache.good.entries
  · simpa [final,hbad] using List.reverse_reverse cache.bad.entries
  · simpa [final,hgood] using List.reverse_reverse cache.good.entries
  · simpa [final,hbad] using List.reverse_reverse cache.bad.entries
  · exact hboundary.endpoint0
  · exact hboundary.endpoint1
  · simpa [totals,Totals.append] using hcalls
  · simpa [totals,Totals.append] using htime
  · simp [totals,Totals.append,hendpoint]
  · simpa [totals,Totals.append] using hcap
  · simp only [totals,Totals.append]
    rw [hgood,hbad,List.length_reverse,List.length_reverse,cache.good.length_eq,cache.bad.length_eq]
    omega

end QecReliability.OracleCost.WholeWrapperCandidate
