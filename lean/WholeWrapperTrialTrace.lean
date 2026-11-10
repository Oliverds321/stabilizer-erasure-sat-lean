import WholeWrapperSelectionFrame

/-! Complete scheduled trial: base exactly once, every
scale before selection, false-base no-cell path, one trial commit, exact calls
and service-time sum, and persistent frame. Semantic source identification is
separate below and uses the original cachedTrial, not a replacement estimator. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate
open PrefixEnumeration

def trialAnchor (s : Config) (rep : ℕ) : Config := { s with repetition := rep }

def operationalTrial (q B : ℕ) (ext : External) (s : Config) (rep : ℕ) : Entry :=
  if (ext.sat (ext.compileQuery (baseKey s rep)).bits).value then
    ((ScaleSelection.scan B 0 (cellEntries q B ext (trialAnchor s rep) (List.range (q+1)))).estimate,
      1+cellCallSum q B ext (trialAnchor s rep) (List.range (q+1)))
  else (0,1)

def operationalTrialTime (q B : ℕ) (ext : External) (s : Config) (rep : ℕ) : ℕ :=
  let reply := ext.sat (ext.compileQuery (baseKey s rep)).bits
  reply.time+if reply.value then cellTimeSum q B ext (trialAnchor s rep) (List.range (q+1)) else 0

def TrialEventOrder (q B : ℕ) (ext : External) (s : Config) (rep : ℕ)
    (events : List RequestKey) : Prop :=
  if (ext.sat (ext.compileQuery (baseKey s rep)).bits).value then
    ∃ cells, BatchCellEvents q B ext (trialAnchor s rep) (List.range (q+1)) cells ∧
      events=baseKey s rep::cells
  else events=[baseKey s rep]

/-- All substantive premises describe only the entry instruction/configuration.
Termination, output record, exact calls/time, and event order are constructed. -/
theorem trial_code_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (s : Config) (rep : ℕ) (rest : List Opcode) (hpc : s.pc=.fetch)
    (hcode : s.code=trialCode q rep++rest) :
    let pair := operationalTrial q B ext s rep
    ∃ t totals events,
      Trace q r B m shape ext s totals events t ∧
      t.pc=.fetch ∧ t.code=rest ∧ t.trialsRev=pair::s.trialsRev ∧
      t.coefficientCalls=s.coefficientCalls+pair.2 ∧
      trialFrame t=trialFrame { baseAfter ext s rep rest with
        cellsRev := [],
        trialCalls := pair.2,trialsRev := pair::s.trialsRev,
        coefficientCalls := s.coefficientCalls+pair.2 } ∧
      totals.calls=pair.2 ∧ totals.oracleTime=operationalTrialTime q B ext s rep ∧
      totals.endpointTime=0 ∧ totals.dispatches≤8*pair.2+5*q+20 ∧
      TrialEventOrder q B ext s rep events := by
  let codeTail := (List.range (q+1)).map Opcode.cell++(.select::rest)
  let start := baseAfter ext s rep codeTail
  have hbtrace : Trace q r B m shape ext s (baseTotals ext s rep) [baseKey s rep] start :=
    base_opcode_trace q r B m shape ext s rep codeTail hpc (by
      simpa [trialCode,codeTail,List.append_assoc] using hcode)
  cases hb : (ext.sat (ext.compileQuery (baseKey s rep)).bits).value with
  | false =>
      let mid : Config := { start with code := .select::rest }
      let t : Config := { mid with
        pc := .fetch,code := rest,selected := 0,
        trialsRev := (0,mid.trialCalls)::mid.trialsRev,
        coefficientCalls := mid.coefficientCalls+mid.trialCalls }
      have hskip : LocalTrace q r B m shape ext start (q+1) mid := by
        simpa [mid] using skipped_cells_trace q r B m shape ext (List.range (q+1)) start
          (.select::rest) rfl rfl (by simp [start,baseAfter,hb])
      have hselect : LocalTrace q r B m shape ext mid 2 t :=
        false_select_commit_trace q r B m shape ext mid rest rfl rfl
          (by simp [mid,start,baseAfter,hb])
      have hlocal : LocalTrace q r B m shape ext start (q+3) t := by
        simpa [Nat.add_assoc] using hskip.trans hselect
      refine ⟨t,Totals.append (baseTotals ext s rep) (localTotals (q+3)),[baseKey s rep],
        ?_,rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · simpa using hbtrace.trans hlocal.toTrace
      · simp [t,mid,start,baseAfter,operationalTrial,hb]
      · simp [t,mid,start,baseAfter,operationalTrial,hb]
      · simp [trialFrame,selectionFrame,batchFrame,prefixFrame,t,mid,start,baseAfter,
          operationalTrial,hb]
      · simp [Totals.append,baseTotals,localTotals,operationalTrial,hb]
      · simp [Totals.append,baseTotals,localTotals,operationalTrialTime,hb]
      · simp [Totals.append,baseTotals,localTotals]
      · simp [Totals.append,baseTotals,localTotals,operationalTrial,hb]
        omega
      · simp [TrialEventOrder,hb]
  | true =>
      let anchor := trialAnchor s rep
      let entries := cellEntries q B ext anchor (List.range (q+1))
      let pair := operationalTrial q B ext s rep
      obtain ⟨mid,ct,ce,hcells,hmidpc,hmidcode,hmidcells,hmidtrial,hmidframe,
          hcalls,hservice,hendpoint,hdispatch,hevents⟩ :=
        active_cells_trace q r B m shape ext anchor (List.range (q+1)) start (.select::rest)
          rfl rfl (by simp [start,baseAfter,hb])
          (by simp [CellContextEq,start,baseAfter,anchor,trialAnchor])
      have hmidnonempty : mid.nonempty=true := by
        have hh := congrArg Config.nonempty hmidframe
        simpa [batchFrame,prefixFrame,start,baseAfter,hb] using hh
      obtain ⟨n,t,hselect,htpc,htcode,htempty,htselected,httrials,htcoefficient,htframe,hn⟩ :=
        true_select_commit_trace q r B m shape ext mid rest hmidpc hmidcode hmidnonempty
      have hmidcells' : mid.cellsRev=entries.reverse := by
        simpa [entries,start,baseAfter] using hmidcells
      have hmidtrial' : mid.trialCalls=pair.2 := by
        simpa [pair,operationalTrial,hb,start,baseAfter,anchor] using hmidtrial
      have hmidtrials : mid.trialsRev=s.trialsRev := by
        simpa [batchFrame,prefixFrame,start,baseAfter] using congrArg Config.trialsRev hmidframe
      have hmidcoefficient : mid.coefficientCalls=s.coefficientCalls := by
        simpa [batchFrame,prefixFrame,start,baseAfter] using congrArg Config.coefficientCalls hmidframe
      have hestimate : (ScaleSelection.scan B 0 mid.cellsRev.reverse).estimate=pair.1 := by
        simp [hmidcells',pair,operationalTrial,hb,entries,anchor]
      let totals := Totals.append (baseTotals ext s rep) (Totals.append ct (localTotals n))
      refine ⟨t,totals,baseKey s rep::ce,?_,htpc,htcode,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · simpa [totals] using hbtrace.trans (hcells.trans hselect.toTrace)
      · simpa [hestimate,hmidtrial',hmidtrials] using httrials
      · simpa [hmidcoefficient,hmidtrial'] using htcoefficient
      · have hsframe := congrArg batchFrame htframe
        have hsframe' : trialFrame t=trialFrame { mid with
            code := rest,cellsRev := [],
            trialCalls := pair.2,trialsRev := pair::mid.trialsRev,
            coefficientCalls := mid.coefficientCalls+pair.2 } := by
          simpa [trialFrame,batchFrame,prefixFrame,selectionFrame,hestimate,hmidtrial'] using hsframe
        have hcframe := congrArg (fun a : Config => selectionFrame
          { a with
            code := rest,cellsRev := [],trialCalls := pair.2,
            trialsRev := pair::a.trialsRev,coefficientCalls := a.coefficientCalls+pair.2 }) hmidframe
        have hcframe' : trialFrame { mid with
            code := rest,cellsRev := [],
            trialCalls := pair.2,trialsRev := pair::mid.trialsRev,
            coefficientCalls := mid.coefficientCalls+pair.2 }=
            trialFrame { baseAfter ext s rep rest with
              cellsRev := [],
              trialCalls := pair.2,trialsRev := pair::s.trialsRev,
              coefficientCalls := s.coefficientCalls+pair.2 } := by
          simpa [trialFrame,batchFrame,prefixFrame,selectionFrame,start,baseAfter] using hcframe
        exact hsframe'.trans hcframe'
      · simp [totals,Totals.append,baseTotals,localTotals,pair,operationalTrial,hb,hcalls,anchor]
      · simp [totals,Totals.append,baseTotals,localTotals,operationalTrialTime,hb,hservice,anchor]
      · simp [totals,Totals.append,baseTotals,localTotals,hendpoint]
      · have hlen : mid.cellsRev.length=q+1 := by
          simp [hmidcells',entries,cellEntries]
        simp only [List.length_range] at hdispatch
        change n≤2*mid.cellsRev.length+4 at hn
        simp only [totals,Totals.append,baseTotals,localTotals]
        simp only [pair,operationalTrial,hb,↓reduceIte]
        dsimp only [anchor] at hdispatch
        omega
      · simp only [TrialEventOrder,hb,↓reduceIte]
        exact ⟨ce,hevents,rfl⟩

open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

/-- Source identification of the record computed by the COMPLETE actual
trial trace. It is exactly cachedTrial, including false base and B=0. -/
theorem operationalTrial_eq_cachedTrial {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (service : SATService)
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) (D : ℕ) (ext : External)
    (hboundary : BoundaryCorrect rows C H K service m ω D ext)
    (s : Config) (rep : ℕ) (hj : s.coefficient<r+1) (hrep : rep<2*m+1) :
    operationalTrial (keySize n r) B ext s rep=
      (queries rows C H K service.solver (s.good,⟨s.coefficient,hj⟩)).cachedTrial B (ω ⟨rep,hrep⟩) := by
  let anchor := trialAnchor s rep
  let decision := queries rows C H K service.solver (s.good,⟨s.coefficient,hj⟩)
  have hv : ValidKey (keySize n r) r m (baseKey s rep) := ⟨hj,hrep⟩
  have hbase := hboundary.answer (baseKey s rep) hv
  have hbool : (ext.sat (ext.compileQuery (baseKey s rep)).bits).value=decision.base.answer [] := by
    rw [hbase]
    exact (QuantumService.base_answer rows C H K service (s.good,⟨s.coefficient,hj⟩) []).symm
  have hentries := concrete_cellEntries rows C H K service B m ω D ext hboundary anchor hj hrep
  unfold operationalTrial DecisionQueries.cachedTrial
  rw [hbool]
  cases hc : decision.base.answer [] with
  | false => simp [hc,decision]
  | true =>
      simp only [hc,↓reduceIte]
      rw [cellCallSum_entries,hentries]
      exact Prod.ext (ScaleSelection.select_eq B _)
        (by rfl)

/-- Exact measured-source time for the same trial record. This is equality
with actual invoke charges, not an asymptotic bound or a postulated cost. -/
theorem operationalTrialTime_eq_measured {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (service : SATService)
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) (D : ℕ) (ext : External)
    (hboundary : BoundaryCorrect rows C H K service m ω D ext)
    (s : Config) (rep : ℕ) (hj : s.coefficient<r+1) (hrep : rep<2*m+1) :
    operationalTrialTime (keySize n r) B ext s rep=
      (CachedControl.trial (queries rows C H K service.solver (s.good,⟨s.coefficient,hj⟩))
        B (ω ⟨rep,hrep⟩) (service.run (QuantumService.baseRequest rows C (s.good,⟨s.coefficient,hj⟩) [])).time
        (fun scale pre => (service.run (QuantumService.cellRequest rows C H K
          (s.good,⟨s.coefficient,hj⟩) scale (ω ⟨rep,hrep⟩) pre)).time)).oracleTime := by
  let anchor := trialAnchor s rep
  have hv : ValidKey (keySize n r) r m (baseKey s rep) := ⟨hj,hrep⟩
  have hbase := hboundary.answer (baseKey s rep) hv
  have hbool := QuantumService.base_answer rows C H K service
    (s.good,⟨s.coefficient,hj⟩) []
  have htime := concrete_cellTimeSum rows C H K service B m ω D ext hboundary anchor hj hrep
  unfold operationalTrialTime CachedControl.trial
  rw [hbase,hbool]
  cases hb : (service.run (QuantumService.baseRequest rows C (s.good,⟨s.coefficient,hj⟩) [])).value
  · simp [resolveRequest,baseKey,hb]
  · simpa [resolveRequest,baseKey,hb,anchor,trialAnchor] using
      congrArg (fun x => (service.run (QuantumService.baseRequest rows C (s.good,⟨s.coefficient,hj⟩) [])).time+x) htime

end QecReliability.OracleCost.WholeWrapperCandidate
