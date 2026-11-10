import WholeWrapperCacheTrace

/-! Generic operational coefficient batches for the tensor controller. The
schedule length is independent of the number of projected key bits. Every
entry is derived from actual operational trials; source-query identification
is proved separately at the primitive boundary. -/
set_option autoImplicit false
namespace QecReliability.TensorMachine.CountingTrace
open OracleCost OracleCost.WholeWrapperCandidate

variable (q r B m : ℕ) (ext : External)

theorem operationalCoefficient_context {s a : Config} (h : CoefficientContextEq s a) :
    operationalCoefficient q B m ext s = operationalCoefficient q B m ext a := by
  have he : operationalTrial q B ext s = operationalTrial q B ext a :=
    funext (fun rep => operationalTrial_context h q B ext rep)
  simp only [operationalCoefficient, repetitionCalls, repetitionEntries, he]

theorem repetitionTime_context {s a : Config} (h : CoefficientContextEq s a) :
    repetitionTime q B ext s (List.range (2*m+1)) =
      repetitionTime q B ext a (List.range (2*m+1)) := by
  have he : operationalTrialTime q B ext s = operationalTrialTime q B ext a :=
    funext (fun rep => operationalTrialTime_context h q B ext rep)
  simp only [repetitionTime, he]

def entry (side : Bool) (j : Fin (r+1)) : Entry :=
  operationalCoefficient q B m ext { initial q r m with good := side, coefficient := j.val }

def entryTime (side : Bool) (j : Fin (r+1)) : ℕ :=
  repetitionTime q B ext { initial q r m with good := side, coefficient := j.val }
    (List.range (2*m+1))

theorem coefficient_trace (shape : Bool) (s : Config) (side : Bool)
    (j : Fin (r+1)) (rest : List Opcode) (hpc : s.pc=.fetch)
    (hcode : s.code=coefficientCode q m side j.val++rest) :
    let pair := entry q r B m ext side j
    ∃ t totals events,
      Trace q r B m shape ext s totals events t ∧
      t.pc=.fetch ∧ t.code=rest ∧
      t.goodRev=(if side then pair::s.goodRev else s.goodRev) ∧
      t.badRev=(if side then s.badRev else pair::s.badRev) ∧
      coefficientFrame t=coefficientFrame { s with
        code := rest,good := side,coefficient := j.val,
        trialsRev := [],coefficientCalls := pair.2,
        goodRev := (if side then pair::s.goodRev else s.goodRev),
        badRev := (if side then s.badRev else pair::s.badRev) } ∧
      totals.calls=pair.2 ∧
      totals.oracleTime=entryTime q r B m ext side j ∧
      totals.endpointTime=0 ∧
      totals.dispatches≤8*pair.2+(5*q+20)*(2*m+1)+
        (2*(2*m+1)^2+5*(2*m+1)+m+5)+2 := by
  let a : Config := { s with good := side,coefficient := j.val }
  let pair := entry q r B m ext side j
  have hp : operationalCoefficient q B m ext a=pair := by
    exact operationalCoefficient_context q B m ext (s := a)
      (a := { initial q r m with good := side, coefficient := j.val }) ⟨rfl,rfl⟩
  have ht : repetitionTime q B ext a (List.range (2*m+1))=
      entryTime q r B m ext side j := by
    exact repetitionTime_context q B m ext (s := a)
      (a := { initial q r m with good := side, coefficient := j.val }) ⟨rfl,rfl⟩
  have h := coefficient_code_trace q r B m shape ext s side j.val rest hpc hcode
  dsimp only at h
  change ∃ t totals events,
    Trace q r B m shape ext s totals events t ∧
    t.pc=.fetch ∧ t.code=rest ∧ t.good=side ∧ t.coefficient=j.val ∧
    t.selected=(operationalCoefficient q B m ext a).1 ∧
    t.coefficientCalls=(operationalCoefficient q B m ext a).2 ∧ t.trialsRev=[] ∧
    t.goodRev=(if side then operationalCoefficient q B m ext a::s.goodRev else s.goodRev) ∧
    t.badRev=(if side then s.badRev else operationalCoefficient q B m ext a::s.badRev) ∧
    coefficientFrame t=coefficientFrame { s with
      code := rest,good := side,coefficient := j.val,
      trialsRev := [],coefficientCalls := (operationalCoefficient q B m ext a).2,
      goodRev := (if side then operationalCoefficient q B m ext a::s.goodRev else s.goodRev),
      badRev := (if side then s.badRev else operationalCoefficient q B m ext a::s.badRev) } ∧
    totals.calls=(operationalCoefficient q B m ext a).2 ∧
    totals.oracleTime=repetitionTime q B ext a (List.range (2*m+1)) ∧
    totals.endpointTime=0 ∧
    totals.dispatches≤8*(operationalCoefficient q B m ext a).2+
      (5*q+20)*(2*m+1)+(2*(2*m+1)^2+5*(2*m+1)+m+5)+2 at h
  rw [hp,ht] at h
  obtain ⟨t,totals,events,hpath,hpc',hcode',_,_,_,_,_,hgood,hbad,hframe,hcalls,htime,hend,hsteps⟩ := h
  exact ⟨t,totals,events,hpath,hpc',hcode',hgood,hbad,hframe,hcalls,htime,hend,hsteps⟩


def sideEntries (side : Bool) (js : List (Fin (r+1))) : List Entry :=
  js.map (entry q r B m ext side)

theorem sideEntries_eq_cached (side : Bool) (js : List (Fin (r+1))) :
    sideEntries q r B m ext side js =
      js.map (fun j => entry q r B m ext side j) := rfl


def sideCalls (side : Bool) (js : List (Fin (r+1))) : ℕ :=
  ((sideEntries q r B m ext side js).map Prod.snd).sum

def sideTime (side : Bool) (js : List (Fin (r+1))) : ℕ :=
  (js.map (fun j => entryTime q r B m ext side j)).sum

/-- Actual arbitrary finite side block. The exact accumulated cache is proved
by induction from the actual individual stores, not a source-cache premise. -/
theorem coefficients_trace (shape : Bool) (side : Bool) (js : List (Fin (r+1)))
    (s : Config) (rest : List Opcode) (hpc : s.pc=.fetch)
    (hcode : s.code=js.flatMap (fun j => coefficientCode q m side j.val)++rest) :
    ∃ t totals events,
      Trace q r B m shape ext s totals events t ∧
      t.pc=.fetch ∧ t.code=rest ∧
      t.goodRev=(if side then (sideEntries q r B m ext side js).reverse++s.goodRev else s.goodRev) ∧
      t.badRev=(if side then s.badRev else (sideEntries q r B m ext side js).reverse++s.badRev) ∧
      cacheFrame t=cacheFrame { s with
        code := rest,
        trialsRev := (if js=[] then s.trialsRev else []),
        goodRev := (if side then (sideEntries q r B m ext side js).reverse++s.goodRev else s.goodRev),
        badRev := (if side then s.badRev else (sideEntries q r B m ext side js).reverse++s.badRev) } ∧
      totals.calls=sideCalls q r B m ext side js ∧
      totals.oracleTime=sideTime q r B m ext side js ∧
      totals.endpointTime=0 ∧
      totals.dispatches≤8*sideCalls q r B m ext side js+
        coefficientLocalBound q m*js.length := by
  induction js generalizing s with
  | nil =>
      have hc : s.code=rest := by simpa using hcode
      refine ⟨s,{},[],Trace.nil s,hpc,hc,?_,?_,?_,rfl,rfl,rfl,by simp⟩
      · cases side <;> simp [sideEntries_eq_cached]
      · cases side <;> simp [sideEntries_eq_cached]
      · rw [← hc]
        cases side <;> simp [sideEntries_eq_cached]
  | cons j js ih =>
      let tailCode := js.flatMap (fun j => coefficientCode q m side j.val)++rest
      let pair := entry q r B m ext side j
      obtain ⟨mid,htotal,hevents,hhead,hmidpc,hmidcode,hmidgood,hmidbad,hmidframe,
          hheadcalls,hheadtime,hheadendpoint,hheadsteps⟩ :=
        coefficient_trace q r B m ext
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
          goodRev := (if side then (sideEntries q r B m ext side js).reverse++a.goodRev else a.goodRev),
          badRev := (if side then a.badRev else (sideEntries q r B m ext side js).reverse++a.badRev) }) hf
        have hh' : cacheFrame { mid with
            code := rest,
            trialsRev := (if js=[] then mid.trialsRev else []),
            goodRev := (if side then (sideEntries q r B m ext side js).reverse++mid.goodRev else mid.goodRev),
            badRev := (if side then mid.badRev else (sideEntries q r B m ext side js).reverse++mid.badRev) }=
            cacheFrame { s with
              code := rest,
              trialsRev := [],
              goodRev := (if side then (sideEntries q r B m ext side (j::js)).reverse++s.goodRev else s.goodRev),
              badRev := (if side then s.badRev else (sideEntries q r B m ext side (j::js)).reverse++s.badRev) } := by
          cases side <;> cases js <;> simpa [cacheFrame,coefficientFrame,sortWorkFrame,repetitionFrame,
            trialFrame,selectionFrame,batchFrame,prefixFrame,sideEntries_eq_cached,pair,
            List.reverse_cons,List.append_assoc] using hh
        exact htframe.trans hh'
      · simp [Totals.append,sideCalls,sideEntries_eq_cached,hheadcalls,htailcalls]
      · simp [Totals.append,sideTime,hheadtime,htailtime]
      · simp [Totals.append,hheadendpoint,htailendpoint]
      · simp only [Totals.append,sideCalls,sideEntries_eq_cached,List.map_cons,List.sum_cons,List.length_cons]
        change htotal.dispatches+ttotal.dispatches≤
          8*(pair.2+sideCalls q r B m ext side js)+
            coefficientLocalBound q m*(js.length+1)
        have hheadsteps' : htotal.dispatches≤8*pair.2+coefficientLocalBound q m := by
          simpa only [pair,coefficientLocalBound,Nat.add_assoc] using hheadsteps
        nlinarith


end QecReliability.TensorMachine.CountingTrace
