import WholeWrapperConcreteCells

/-! Strengthens the actual selector phase with full
persistent framing, needed to compose source-equal cell tables into trials. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate

def selectionFrame (s : Config) : Config :=
  { s with
    pc := .fetch,pairSrc := [],pairDst := [],selected := 0,
    selectIndex := 0,scaleFactor := 1 }

def trialFrame (s : Config) : Config := selectionFrame (batchFrame s)

theorem selectScan_framed (q r B m : ℕ) (shape : Bool) (ext : External)
    (xs : List Entry) (s : Config) (hpc : s.pc=.selectScan) (hsrc : s.pairSrc=xs)
    (hpower : s.scaleFactor=2^s.selectIndex) :
    ∃ n t, LocalTrace q r B m shape ext s n t ∧ t.pc=.trialCommit ∧
      t.selected=(ScaleSelection.scan B s.selectIndex xs).estimate ∧
      n≤xs.length+1 ∧ selectionFrame t=selectionFrame s := by
  induction xs generalizing s with
  | nil =>
      let t : Config := { s with pc := .trialCommit,selected := 1 }
      refine ⟨1,t,LocalTrace.single ?_,rfl,rfl,by simp,rfl⟩
      simp [step,hpc,hsrc,t,localEdge]
  | cons x xs ih =>
      by_cases hx : x.1≤4*B
      · let t : Config := { s with
          pc := .trialCommit,
          selected := max 1 (s.scaleFactor*x.1),pairSrc := [] }
        refine ⟨1,t,LocalTrace.single ?_,rfl,?_,by simp,rfl⟩
        · simp [step,hpc,hsrc,hx,t,localEdge]
        · simp [t,ScaleSelection.scan,hx,hpower]
      · let nxt : Config := { s with
          pairSrc := xs,
          selectIndex := s.selectIndex+1,scaleFactor := 2*s.scaleFactor }
        have hnextpower : nxt.scaleFactor=2^nxt.selectIndex := by
          simp only [nxt,hpower,pow_succ]
          omega
        obtain ⟨n,t,ht,htpc,htvalue,hn,hframe⟩ := ih nxt
          (by simpa [nxt] using hpc) rfl hnextpower
        refine ⟨n+1,t,LocalTrace.cons ?_ ht,htpc,?_,?_,?_⟩
        · simp [step,hpc,hsrc,hx,nxt,localEdge]
        · simpa [nxt,ScaleSelection.scan,hx] using htvalue
        · simp only [List.length_cons]; omega
        · simpa [selectionFrame,nxt] using hframe

/-- Actual true .select fetch, full reversal, accepted-scale scan, and single
trial commit. No calls occur; the existing cached scan determines the record. -/
theorem true_select_commit_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (s : Config) (rest : List Opcode) (hpc : s.pc=.fetch)
    (hcode : s.code=.select::rest) (hnonempty : s.nonempty=true) :
    let estimate := (ScaleSelection.scan B 0 s.cellsRev.reverse).estimate
    ∃ n t, LocalTrace q r B m shape ext s n t ∧
      t.pc=.fetch ∧ t.code=rest ∧ t.cellsRev=[] ∧ t.selected=estimate ∧
      t.trialsRev=(estimate,s.trialCalls)::s.trialsRev ∧
      t.coefficientCalls=s.coefficientCalls+s.trialCalls ∧
      selectionFrame t=selectionFrame
        { s with
          code := rest,cellsRev := [],
          trialsRev := (estimate,s.trialCalls)::s.trialsRev,
          coefficientCalls := s.coefficientCalls+s.trialCalls } ∧
      n≤2*s.cellsRev.length+4 := by
  let start : Config := { s with
    pc := .reverseCells,code := rest,
    pairSrc := s.cellsRev,pairDst := [],cellsRev := [] }
  let scan : Config := { start with
    pc := .selectScan,pairSrc := s.cellsRev.reverse,
    pairDst := [],selectIndex := 0,scaleFactor := 1 }
  have hstart : step q r B m shape ext s=localEdge start := by
    simp [step,hpc,hcode,hnonempty,start,localEdge]
  have hreverse : LocalTrace q r B m shape ext start (s.cellsRev.length+1) scan := by
    simpa [start,scan] using reverseCells_trace q r B m shape ext s.cellsRev start rfl rfl
  obtain ⟨n,mid,hscan,hmidpc,hvalue,hn,hframe⟩ :=
    selectScan_framed q r B m shape ext s.cellsRev.reverse scan rfl rfl (by simp [scan])
  let estimate := (ScaleSelection.scan B 0 s.cellsRev.reverse).estimate
  have hvalue' : mid.selected=estimate := by simpa [scan] using hvalue
  have hcode' : mid.code=rest := by simpa [selectionFrame,scan,start] using congrArg Config.code hframe
  have hcells : mid.cellsRev=[] := by simpa [selectionFrame,scan,start] using congrArg Config.cellsRev hframe
  have htrials : mid.trialsRev=s.trialsRev := by
    simpa [selectionFrame,scan,start] using congrArg Config.trialsRev hframe
  have htrial : mid.trialCalls=s.trialCalls := by
    simpa [selectionFrame,scan,start] using congrArg Config.trialCalls hframe
  have hcoefficient : mid.coefficientCalls=s.coefficientCalls := by
    simpa [selectionFrame,scan,start] using congrArg Config.coefficientCalls hframe
  let t : Config := { mid with
    pc := .fetch,
    trialsRev := (mid.selected,mid.trialCalls)::mid.trialsRev,
    coefficientCalls := mid.coefficientCalls+mid.trialCalls }
  have hcommit : step q r B m shape ext mid=localEdge t := by
    simp [step,hmidpc,t,localEdge]
  refine ⟨1+(s.cellsRev.length+1+n+1),t,?_,rfl,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (LocalTrace.single hstart).trans
      ((hreverse.trans hscan).trans (LocalTrace.single hcommit))
  · exact hcode'
  · exact hcells
  · exact hvalue'
  · simp [t,hvalue',htrial,htrials,estimate]
  · simp [t,hcoefficient,htrial]
  · have hf := congrArg (fun a : Config =>
        { a with
          trialsRev := (estimate,s.trialCalls)::a.trialsRev,
          coefficientCalls := a.coefficientCalls+s.trialCalls }) hframe
    simpa [selectionFrame,scan,start,t,hvalue',htrial,estimate] using hf
  · simp only [List.length_reverse] at hn
    omega

end QecReliability.OracleCost.WholeWrapperCandidate
