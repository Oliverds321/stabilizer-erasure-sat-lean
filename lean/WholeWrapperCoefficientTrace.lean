import WholeWrapperMedianFrame

/-! Begin/repetitions/odd median/store for the
actual coefficientCode. Completed trial lists and call aggregates are derived,
not supplied as an opaque source-record hypothesis. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate

def operationalCoefficient (q B m : ℕ) (ext : External) (anchor : Config) : Entry :=
  (MedianSort.median (fun i : Fin (2*m+1) => (operationalTrial q B ext anchor i.val).1),
    repetitionCalls q B ext anchor (List.range (2*m+1)))

theorem repetitionEntries_ofFn (q B m : ℕ) (ext : External) (anchor : Config) :
    repetitionEntries q B ext anchor (List.range (2*m+1))=
      List.ofFn (fun i : Fin (2*m+1) => operationalTrial q B ext anchor i.val) := by
  unfold repetitionEntries
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hi'
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]

/-- Complete actual coefficient block, with exactly one side-list store and
full persistent framing. This is not a theorem conditional on a final cache. -/
theorem coefficient_code_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (s : Config) (side : Bool) (j : ℕ) (rest : List Opcode)
    (hpc : s.pc=.fetch) (hcode : s.code=coefficientCode q m side j++rest) :
    let anchor := { s with good := side,coefficient := j }
    let pair := operationalCoefficient q B m ext anchor
    ∃ t totals events,
      Trace q r B m shape ext s totals events t ∧
      t.pc=.fetch ∧ t.code=rest ∧ t.good=side ∧ t.coefficient=j ∧
      t.selected=pair.1 ∧ t.coefficientCalls=pair.2 ∧ t.trialsRev=[] ∧
      t.goodRev=(if side then pair::s.goodRev else s.goodRev) ∧
      t.badRev=(if side then s.badRev else pair::s.badRev) ∧
      coefficientFrame t=coefficientFrame { s with
        code := rest,good := side,coefficient := j,
        trialsRev := [],coefficientCalls := pair.2,
        goodRev := (if side then pair::s.goodRev else s.goodRev),
        badRev := (if side then s.badRev else pair::s.badRev) } ∧
      totals.calls=pair.2 ∧
      totals.oracleTime=repetitionTime q B ext anchor (List.range (2*m+1)) ∧
      totals.endpointTime=0 ∧
      totals.dispatches≤8*pair.2+(5*q+20)*(2*m+1)+
        (2*(2*m+1)^2+5*(2*m+1)+m+5)+2 := by
  let anchor : Config := { s with good := side,coefficient := j }
  let pair := operationalCoefficient q B m ext anchor
  let trialCodeTail := (List.range (2*m+1)).flatMap (trialCode q)++(.median::.store::rest)
  let start : Config := { s with
    pc := .fetch,code := trialCodeTail,good := side,
    coefficient := j,trialsRev := [],coefficientCalls := 0 }
  have hbegin : step q r B m shape ext s=localEdge start := by
    simp [step,hpc,hcode,coefficientCode,trialCodeTail,start,List.append_assoc,localEdge]
  obtain ⟨rfinal,rtotal,revents,hreps,hrpc,hrcode,hrtrials,hrcalls,hrframe,
      hrcalltotal,hrtime,hrendpoint,hrsteps⟩ :=
    repetitions_trace q r B m shape ext anchor (List.range (2*m+1)) start (.median::.store::rest)
      rfl rfl (by simp [CoefficientContextEq,start,anchor])
  have htrials : rfinal.trialsRev=
      (List.ofFn (fun i : Fin (2*m+1) => operationalTrial q B ext anchor i.val)).reverse := by
    simpa [start,repetitionEntries_ofFn] using hrtrials
  obtain ⟨mn,mid,hmedian,hmidpc,hmidcode,hselected,hcleared,hmedianframe,hmsteps⟩ :=
    median_opcode_trace q r B m shape ext rfinal (.store::rest)
      (fun i : Fin (2*m+1) => operationalTrial q B ext anchor i.val) hrpc hrcode htrials
  have hframed : coefficientFrame mid=coefficientFrame
      { s with
        code := .store::rest,good := side,coefficient := j,
        trialsRev := [],coefficientCalls := pair.2 } := by
    have hm := congrArg repetitionFrame hmedianframe
    have hm' : coefficientFrame mid=coefficientFrame { rfinal with code := .store::rest,trialsRev := [] } := by
      simpa [coefficientFrame,sortWorkFrame,repetitionFrame,trialFrame,selectionFrame,batchFrame,prefixFrame] using hm
    have hr := congrArg (fun a : Config => sortWorkFrame { a with code := .store::rest,trialsRev := [] }) hrframe
    have hr' : coefficientFrame { rfinal with code := .store::rest,trialsRev := [] }=
        coefficientFrame { s with
          code := .store::rest,good := side,coefficient := j,
          trialsRev := [],coefficientCalls := pair.2 } := by
      simpa [coefficientFrame,sortWorkFrame,repetitionFrame,trialFrame,selectionFrame,
        batchFrame,prefixFrame,start,pair,operationalCoefficient] using hr
    exact hm'.trans hr'
  have hgood : mid.good=side := by
    simpa [coefficientFrame,sortWorkFrame,repetitionFrame,trialFrame,selectionFrame,batchFrame,prefixFrame]
      using congrArg Config.good hframed
  have hcoefficient : mid.coefficient=j := by
    simpa [coefficientFrame,sortWorkFrame,repetitionFrame,trialFrame,selectionFrame,batchFrame,prefixFrame]
      using congrArg Config.coefficient hframed
  have hcalls : mid.coefficientCalls=pair.2 := by
    simpa [coefficientFrame,sortWorkFrame,repetitionFrame,trialFrame,selectionFrame,batchFrame,prefixFrame]
      using congrArg Config.coefficientCalls hframed
  have hgoodRev : mid.goodRev=s.goodRev := by
    simpa [coefficientFrame,sortWorkFrame,repetitionFrame,trialFrame,selectionFrame,batchFrame,prefixFrame]
      using congrArg Config.goodRev hframed
  have hbadRev : mid.badRev=s.badRev := by
    simpa [coefficientFrame,sortWorkFrame,repetitionFrame,trialFrame,selectionFrame,batchFrame,prefixFrame]
      using congrArg Config.badRev hframed
  have hselected' : mid.selected=pair.1 := hselected
  let t : Config := { mid with
    code := rest,
    goodRev := (if side then (mid.selected,mid.coefficientCalls)::mid.goodRev else mid.goodRev),
    badRev := (if side then mid.badRev else (mid.selected,mid.coefficientCalls)::mid.badRev) }
  have hstore : step q r B m shape ext mid=localEdge t := by
    cases side <;> simp [step,hmidpc,hmidcode,hgood,t,localEdge]
  let totals := Totals.append (localTotals 1) (Totals.append rtotal (localTotals (mn+1)))
  refine ⟨t,totals,revents,?_,?_,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have post := hmedian.trans (LocalTrace.single hstore)
    have all := (LocalTrace.single hbegin).toTrace.trans (hreps.trans post.toTrace)
    simpa [totals] using all
  · simpa [t] using hmidpc
  · exact hgood
  · exact hcoefficient
  · exact hselected'
  · exact hcalls
  · exact hcleared
  · simp [t,hselected',hcalls,hgoodRev,pair,anchor]
  · simp [t,hselected',hcalls,hbadRev,pair,anchor]
  · have hf := congrArg (fun a : Config => { a with
        code := rest,
        goodRev := (if side then pair::a.goodRev else a.goodRev),
        badRev := (if side then a.badRev else pair::a.badRev) }) hframed
    simpa [coefficientFrame,sortWorkFrame,repetitionFrame,trialFrame,selectionFrame,batchFrame,
      prefixFrame,t,hselected',hcalls,pair,anchor] using hf
  · simp [totals,Totals.append,localTotals,pair,operationalCoefficient,hrcalltotal,anchor]
  · simp [totals,Totals.append,localTotals,hrtime,anchor]
  · simp [totals,Totals.append,localTotals,hrendpoint]
  · simp only [List.length_range] at hrsteps
    simp only [totals,Totals.append,localTotals]
    change 1+(rtotal.dispatches+(mn+1))≤_
    change rtotal.dispatches≤8*pair.2+(5*q+20)*(2*m+1) at hrsteps
    dsimp only [pair,anchor] at hrsteps
    omega

open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (service : SATService)
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) (D : ℕ) (ext : External)
    (hboundary : BoundaryCorrect rows C H K service m ω D ext)
    (anchor : Config) (hj : anchor.coefficient<r+1)

include hboundary in
/-- The actual repeated-record list, in source Fin order, is the SAME cached
trial table. Duplicates remain, and no source-record premise is assumed. -/
theorem concrete_repetitionEntries :
    repetitionEntries (keySize n r) B ext anchor (List.range (2*m+1))=
      (CountTable.build (fun i : Fin (2*m+1) =>
        (queries rows C H K service.solver (anchor.good,⟨anchor.coefficient,hj⟩)).cachedTrial B (ω i))).entries := by
  rw [repetitionEntries_ofFn]
  unfold CountTable.build
  congr 1
  funext i
  exact operationalTrial_eq_cachedTrial rows C H K service B m ω D ext hboundary
    anchor i.val hj i.isLt

include hboundary in
/-- Exact source median AND exact source calls, not merely a close estimate. -/
theorem operationalCoefficient_eq_cachedMedian :
    operationalCoefficient (keySize n r) B m ext anchor=
      (queries rows C H K service.solver (anchor.good,⟨anchor.coefficient,hj⟩)).cachedMedian B m ω := by
  have he := concrete_repetitionEntries rows C H K service B m ω D ext hboundary anchor hj
  have hv : (fun i : Fin (2*m+1) => (operationalTrial (keySize n r) B ext anchor i.val).1)=
      (fun i => ((queries rows C H K service.solver
        (anchor.good,⟨anchor.coefficient,hj⟩)).cachedTrial B (ω i)).1) := by
    funext i
    exact congrArg Prod.fst (operationalTrial_eq_cachedTrial rows C H K service B m ω D ext
      hboundary anchor i.val hj i.isLt)
  unfold operationalCoefficient DecisionQueries.cachedMedian
  rw [hv,MedianSort.median_eq]
  apply Prod.ext
  · simp only [CountTable.get_build]
  · unfold repetitionCalls
    rw [he]
    rfl

include hboundary in
/-- Existing QuantumService.coefficient service-time equality for the actual
repetition block; local sorting and store edges invoke no decision service. -/
theorem repetitionTime_eq_coefficient :
    repetitionTime (keySize n r) B ext anchor (List.range (2*m+1))=
      (QuantumService.coefficient rows C H K service B m ω
        (anchor.good,⟨anchor.coefficient,hj⟩)).oracleTime := by
  have ht : (fun i : Fin (2*m+1) => operationalTrialTime (keySize n r) B ext anchor i.val)=
      (fun i => (CachedControl.trial
        (queries rows C H K service.solver (anchor.good,⟨anchor.coefficient,hj⟩)) B (ω i)
        (service.run (QuantumService.baseRequest rows C (anchor.good,⟨anchor.coefficient,hj⟩) [])).time
        (fun scale pre => (service.run (QuantumService.cellRequest rows C H K
          (anchor.good,⟨anchor.coefficient,hj⟩) scale (ω i) pre)).time)).oracleTime) := by
    funext i
    exact operationalTrialTime_eq_measured rows C H K service B m ω D ext hboundary
      anchor i.val hj i.isLt
  unfold repetitionTime
  have hrange : (List.range (2*m+1)).map (operationalTrialTime (keySize n r) B ext anchor)=
      List.ofFn (fun i : Fin (2*m+1) => operationalTrialTime (keySize n r) B ext anchor i.val) := by
    apply List.ext_getElem
    · simp only [List.length_map,List.length_range,List.length_ofFn]
    · intro i hi hi'
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
  rw [hrange,ht,QuantumService.coefficient_eq_median]
  simp only [CachedControl.median,CachedControl.MeasuredTable.oracleTime,
    CachedControl.MeasuredTable.build,List.map_ofFn,Function.comp_def]

include hboundary in
/-- Source-facing exact coefficient endpoint. Only actual entry phase/code
and concrete boundary fidelity are premises. The source cachedMedian record,
its source measured time, and its single raw-list store are all conclusions. -/
theorem concrete_coefficient_trace (shape : Bool) (s : Config) (side : Bool)
    (j : Fin (r+1)) (rest : List Opcode) (hpc : s.pc=.fetch)
    (hcode : s.code=coefficientCode (keySize n r) m side j.val++rest) :
    let pair := (queries rows C H K service.solver (side,j)).cachedMedian B m ω
    ∃ t totals events,
      Trace (keySize n r) r B m shape ext s totals events t ∧
      t.pc=.fetch ∧ t.code=rest ∧
      t.goodRev=(if side then pair::s.goodRev else s.goodRev) ∧
      t.badRev=(if side then s.badRev else pair::s.badRev) ∧
      coefficientFrame t=coefficientFrame { s with
        code := rest,good := side,coefficient := j.val,
        trialsRev := [],coefficientCalls := pair.2,
        goodRev := (if side then pair::s.goodRev else s.goodRev),
        badRev := (if side then s.badRev else pair::s.badRev) } ∧
      totals.calls=pair.2 ∧
      totals.oracleTime=(QuantumService.coefficient rows C H K service B m ω (side,j)).oracleTime ∧
      totals.endpointTime=0 ∧
      totals.dispatches≤8*pair.2+(5*(keySize n r)+20)*(2*m+1)+
        (2*(2*m+1)^2+5*(2*m+1)+m+5)+2 := by
  let a : Config := { s with good := side,coefficient := j.val }
  let pair := (queries rows C H K service.solver (side,j)).cachedMedian B m ω
  have hp : operationalCoefficient (keySize n r) B m ext a=pair := by
    simpa [a,pair] using operationalCoefficient_eq_cachedMedian rows C H K service B m ω D ext hboundary a j.isLt
  have ht : repetitionTime (keySize n r) B ext a (List.range (2*m+1))=
      (QuantumService.coefficient rows C H K service B m ω (side,j)).oracleTime := by
    simpa [a] using repetitionTime_eq_coefficient rows C H K service B m ω D ext hboundary a j.isLt
  have h := coefficient_code_trace (keySize n r) r B m shape ext s side j.val rest hpc hcode
  dsimp only at h
  change ∃ t totals events,
    Trace (keySize n r) r B m shape ext s totals events t ∧
    t.pc=.fetch ∧ t.code=rest ∧ t.good=side ∧ t.coefficient=j.val ∧
    t.selected=(operationalCoefficient (keySize n r) B m ext a).1 ∧
    t.coefficientCalls=(operationalCoefficient (keySize n r) B m ext a).2 ∧ t.trialsRev=[] ∧
    t.goodRev=(if side then operationalCoefficient (keySize n r) B m ext a::s.goodRev else s.goodRev) ∧
    t.badRev=(if side then s.badRev else operationalCoefficient (keySize n r) B m ext a::s.badRev) ∧
    coefficientFrame t=coefficientFrame { s with
      code := rest,good := side,coefficient := j.val,
      trialsRev := [],coefficientCalls := (operationalCoefficient (keySize n r) B m ext a).2,
      goodRev := (if side then operationalCoefficient (keySize n r) B m ext a::s.goodRev else s.goodRev),
      badRev := (if side then s.badRev else operationalCoefficient (keySize n r) B m ext a::s.badRev) } ∧
    totals.calls=(operationalCoefficient (keySize n r) B m ext a).2 ∧
    totals.oracleTime=repetitionTime (keySize n r) B ext a (List.range (2*m+1)) ∧
    totals.endpointTime=0 ∧
    totals.dispatches≤8*(operationalCoefficient (keySize n r) B m ext a).2+
      (5*(keySize n r)+20)*(2*m+1)+(2*(2*m+1)^2+5*(2*m+1)+m+5)+2 at h
  rw [hp,ht] at h
  obtain ⟨t,totals,events,hpath,hpc',hcode',_,_,_,_,_,hgood,hbad,hframe,hcalls,htime,hend,hsteps⟩ := h
  exact ⟨t,totals,events,hpath,hpc',hcode',hgood,hbad,hframe,hcalls,htime,hend,hsteps⟩

end QecReliability.OracleCost.WholeWrapperCandidate
