import WholeWrapperCoefficientTrace

/-! Both actual coefficient batches accumulate
literal old cached records. All histories below are ghost Trace witnesses;
Config and its finite schedule are unchanged. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

/-- Erase only coefficient-control scratch; raw caches, tables, endpoints,
repair/report/output state, and code remain persistent. -/
def cacheFrame (s : Config) : Config :=
  coefficientFrame { s with good := true,coefficient := 0,coefficientCalls := 0 }

def coefficientLocalBound (q m : ℕ) : ℕ :=
  (5*q+20)*(2*m+1)+(2*(2*m+1)^2+5*(2*m+1)+m+5)+2

variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (service : SATService)
    (B m : ℕ) (ω : Fin (2*m+1) → Ω)

def sideEntries (side : Bool) (js : List (Fin (r+1))) : List Entry :=
  js.map (fun j =>
    let D := queries rows C H K service.solver (side,j)
    CachedAnswers.median D.base.answer (fun s seed => (D.cell s seed).answer) B m ω)

theorem sideEntries_eq_cached (side : Bool) (js : List (Fin (r+1))) :
    sideEntries rows C H K service B m ω side js =
      js.map (fun j => (queries rows C H K service.solver (side,j)).cachedMedian B m ω) := rfl


def sideCalls (side : Bool) (js : List (Fin (r+1))) : ℕ :=
  ((sideEntries rows C H K service B m ω side js).map Prod.snd).sum

def sideTime (side : Bool) (js : List (Fin (r+1))) : ℕ :=
  (js.map (fun j => (QuantumService.coefficient rows C H K service B m ω (side,j)).oracleTime)).sum

variable (D : ℕ) (ext : External)
    (hboundary : BoundaryCorrect rows C H K service m ω D ext)

include hboundary in
/-- Actual arbitrary finite side block. The exact accumulated cache is proved
by induction from the actual individual stores, not a source-cache premise. -/
theorem coefficients_trace (shape : Bool) (side : Bool) (js : List (Fin (r+1)))
    (s : Config) (rest : List Opcode) (hpc : s.pc=.fetch)
    (hcode : s.code=js.flatMap (fun j => coefficientCode (keySize n r) m side j.val)++rest) :
    ∃ t totals events,
      Trace (keySize n r) r B m shape ext s totals events t ∧
      t.pc=.fetch ∧ t.code=rest ∧
      t.goodRev=(if side then (sideEntries rows C H K service B m ω side js).reverse++s.goodRev else s.goodRev) ∧
      t.badRev=(if side then s.badRev else (sideEntries rows C H K service B m ω side js).reverse++s.badRev) ∧
      cacheFrame t=cacheFrame { s with
        code := rest,
        trialsRev := (if js=[] then s.trialsRev else []),
        goodRev := (if side then (sideEntries rows C H K service B m ω side js).reverse++s.goodRev else s.goodRev),
        badRev := (if side then s.badRev else (sideEntries rows C H K service B m ω side js).reverse++s.badRev) } ∧
      totals.calls=sideCalls rows C H K service B m ω side js ∧
      totals.oracleTime=sideTime rows C H K service B m ω side js ∧
      totals.endpointTime=0 ∧
      totals.dispatches≤8*sideCalls rows C H K service B m ω side js+
        coefficientLocalBound (keySize n r) m*js.length := by
  induction js generalizing s with
  | nil =>
      have hc : s.code=rest := by simpa using hcode
      refine ⟨s,{},[],Trace.nil s,hpc,hc,?_,?_,?_,rfl,rfl,rfl,by simp⟩
      · cases side <;> simp [sideEntries_eq_cached]
      · cases side <;> simp [sideEntries_eq_cached]
      · rw [← hc]
        cases side <;> simp [sideEntries_eq_cached]
  | cons j js ih =>
      let tailCode := js.flatMap (fun j => coefficientCode (keySize n r) m side j.val)++rest
      let pair := (queries rows C H K service.solver (side,j)).cachedMedian B m ω
      obtain ⟨mid,htotal,hevents,hhead,hmidpc,hmidcode,hmidgood,hmidbad,hmidframe,
          hheadcalls,hheadtime,hheadendpoint,hheadsteps⟩ :=
        concrete_coefficient_trace rows C H K service B m ω D ext hboundary
          shape s side j tailCode hpc
          (by simpa [tailCode,List.flatMap_cons,List.append_assoc] using hcode)
      have hf : cacheFrame mid=cacheFrame { s with
          code := tailCode,
          trialsRev := [],
          goodRev := (if side then pair::s.goodRev else s.goodRev),
          badRev := (if side then s.badRev else pair::s.badRev) } := by
        have hh := congrArg (fun a : Config =>
          { a with good := true,coefficient := 0,coefficientCalls := 0 }) hmidframe
        simpa [cacheFrame,coefficientFrame,sortWorkFrame,repetitionFrame,trialFrame,
          selectionFrame,batchFrame,prefixFrame,pair] using hh
      obtain ⟨t,ttotal,tevents,ht,htpc,htcode,htgood,htbad,htframe,
          htailcalls,htailtime,htailendpoint,htailsteps⟩ := ih mid hmidpc hmidcode
      refine ⟨t,Totals.append htotal ttotal,hevents++tevents,hhead.trans ht,
        htpc,htcode,?_,?_,?_,?_,?_,?_,?_⟩
      · cases side <;> simpa [sideEntries_eq_cached,List.reverse_cons,List.append_assoc,hmidgood,pair] using htgood
      · cases side <;> simpa [sideEntries_eq_cached,List.reverse_cons,List.append_assoc,hmidbad,pair] using htbad
      · have hh := congrArg (fun a : Config => { a with
          code := rest,
          trialsRev := (if js=[] then a.trialsRev else []),
          goodRev := (if side then (sideEntries rows C H K service B m ω side js).reverse++a.goodRev else a.goodRev),
          badRev := (if side then a.badRev else (sideEntries rows C H K service B m ω side js).reverse++a.badRev) }) hf
        have hh' : cacheFrame { mid with
            code := rest,
            trialsRev := (if js=[] then mid.trialsRev else []),
            goodRev := (if side then (sideEntries rows C H K service B m ω side js).reverse++mid.goodRev else mid.goodRev),
            badRev := (if side then mid.badRev else (sideEntries rows C H K service B m ω side js).reverse++mid.badRev) }=
            cacheFrame { s with
              code := rest,
              trialsRev := [],
              goodRev := (if side then (sideEntries rows C H K service B m ω side (j::js)).reverse++s.goodRev else s.goodRev),
              badRev := (if side then s.badRev else (sideEntries rows C H K service B m ω side (j::js)).reverse++s.badRev) } := by
          cases side <;> cases js <;> simpa [cacheFrame,coefficientFrame,sortWorkFrame,repetitionFrame,
            trialFrame,selectionFrame,batchFrame,prefixFrame,sideEntries_eq_cached,pair,
            List.reverse_cons,List.append_assoc] using hh
        exact htframe.trans hh'
      · simp [Totals.append,sideCalls,sideEntries_eq_cached,hheadcalls,htailcalls]
      · simp [Totals.append,sideTime,hheadtime,htailtime]
      · simp [Totals.append,hheadendpoint,htailendpoint]
      · simp only [Totals.append,sideCalls,sideEntries_eq_cached,List.map_cons,List.sum_cons,List.length_cons]
        change htotal.dispatches+ttotal.dispatches≤
          8*(pair.2+sideCalls rows C H K service B m ω side js)+
            coefficientLocalBound (keySize n r) m*(js.length+1)
        have hheadsteps' : htotal.dispatches≤8*pair.2+coefficientLocalBound (keySize n r) m := by
          simpa only [pair,coefficientLocalBound,Nat.add_assoc] using hheadsteps
        nlinarith

/-- The source CountTable.build list order is exactly the Fin enumeration
used by the actual natural-index schedule. -/
theorem sideEntries_finRange (side : Bool) :
    sideEntries rows C H K service B m ω side (List.finRange (r+1))=
      (CountTable.build (fun j => (queries rows C H K service.solver (side,j)).cachedMedian B m ω)).entries := by
  simp only [sideEntries_eq_cached,CountTable.build,List.ofFn_eq_map]

theorem program_finRange (q r m : ℕ) :
    program q r m=
      (List.finRange (r+1)).flatMap (fun j => coefficientCode q m true j.val)++
      (List.finRange (r+1)).flatMap (fun j => coefficientCode q m false j.val)++[.finish] := by
  have hrange : (List.finRange (r+1)).map Fin.val=List.range (r+1) := by
    apply List.ext_getElem
    · simp only [List.length_map,List.length_finRange,List.length_range]
    · intro i hi hi'
      simp only [List.getElem_map,List.getElem_finRange,List.getElem_range,Fin.val_cast]
  simp only [program,← hrange,List.flatMap_map,Function.comp_def]

end QecReliability.OracleCost.WholeWrapperCandidate
