import WholeWrapperRepetitions

/-! Exact duplicate-preserving insertion sorting
and odd median lookup, strengthened with persistent Config frame equalities. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate

def sortWorkFrame (s : Config) : Config :=
  { s with
    pc := .fetch,sortTodo := [],sorted := [],insertLeftRev := [],
    insertRight := [],insertResult := [],insertValue := 0,lookupRemaining := 0,selected := 0 }

def coefficientFrame (s : Config) : Config := sortWorkFrame (repetitionFrame s)

theorem insertScan_framed (q r B m : ℕ) (shape : Bool) (ext : External)
    (xs : List ℕ) (s : Config) (hpc : s.pc=.insertScan) (hsrc : s.insertRight=xs) :
    ∃ n t, LocalTrace q r B m shape ext s n t ∧ t.pc=.sortNext ∧
      t.sortTodo=s.sortTodo ∧
      t.sorted=s.insertLeftRev.reverse++(MedianSort.insert s.insertValue xs).values ∧
      n≤2*xs.length+s.insertLeftRev.length+2 ∧ sortWorkFrame t=sortWorkFrame s := by
  induction xs generalizing s with
  | nil =>
      let nxt : Config := { s with pc := .insertRestore,insertResult := [s.insertValue] }
      have hs : step q r B m shape ext s=localEdge nxt := by
        simp [step,hpc,hsrc,nxt,localEdge]
      have ht := insertRestore_trace q r B m shape ext s.insertLeftRev nxt rfl rfl
      let last : Config := { nxt with
        pc := .sortNext,sorted := s.insertLeftRev.reverse++nxt.insertResult,
        insertLeftRev := [],insertRight := [],insertResult := [] }
      refine ⟨s.insertLeftRev.length+2,last,?_,rfl,rfl,rfl,by simp,?_⟩
      · simpa [last,Nat.add_assoc] using LocalTrace.cons hs ht
      · rfl
  | cons x xs ih =>
      by_cases hx : s.insertValue≤x
      · let nxt : Config := { s with
          pc := .insertRestore,
          insertResult := s.insertValue::s.insertRight }
        have hs : step q r B m shape ext s=localEdge nxt := by
          simp [step,hpc,hsrc,hx,nxt,localEdge]
        have ht := insertRestore_trace q r B m shape ext s.insertLeftRev nxt rfl rfl
        let last : Config := { nxt with
          pc := .sortNext,sorted := s.insertLeftRev.reverse++nxt.insertResult,
          insertLeftRev := [],insertRight := [],insertResult := [] }
        refine ⟨s.insertLeftRev.length+2,last,?_,rfl,rfl,?_,?_,?_⟩
        · simpa [last,Nat.add_assoc] using LocalTrace.cons hs ht
        · simp [last,nxt,hsrc,MedianSort.insert,hx]
        · simp only [List.length_cons]; omega
        · rfl
      · let nxt : Config := { s with insertRight := xs,insertLeftRev := x::s.insertLeftRev }
        have hs : step q r B m shape ext s=localEdge nxt := by
          simp [step,hpc,hsrc,hx,nxt,localEdge]
        obtain ⟨n,t,ht,htpc,httodo,htsorted,hn,hframe⟩ := ih nxt
          (by simpa [nxt] using hpc) rfl
        refine ⟨n+1,t,LocalTrace.cons hs ht,htpc,?_,?_,?_,?_⟩
        · simpa [nxt] using httodo
        · simpa [nxt,MedianSort.insert,hx,List.reverse_cons,List.append_assoc] using htsorted
        · simp only [nxt,List.length_cons] at hn ⊢; omega
        · simpa [sortWorkFrame,nxt] using hframe

theorem sortNext_framed (q r B m : ℕ) (shape : Bool) (ext : External)
    (xs : List ℕ) (s : Config) (hpc : s.pc=.sortNext) (htodo : s.sortTodo=xs) :
    ∃ n t, LocalTrace q r B m shape ext s n t ∧ t.pc=.medianLookup ∧
      t.insertRight=foldInsert xs s.sorted ∧ t.lookupRemaining=m ∧
      n≤xs.length*(2*s.sorted.length+2*xs.length+3)+1 ∧
      sortWorkFrame t=sortWorkFrame s := by
  induction xs generalizing s with
  | nil =>
      let t : Config := { s with pc := .medianLookup,insertRight := s.sorted,lookupRemaining := m }
      refine ⟨1,t,LocalTrace.single ?_,rfl,rfl,rfl,by simp,rfl⟩
      simp [step,hpc,htodo,t,localEdge]
  | cons x xs ih =>
      let nxt : Config := { s with
        pc := .insertScan,sortTodo := xs,
        insertValue := x,insertLeftRev := [],insertRight := s.sorted }
      have hs : step q r B m shape ext s=localEdge nxt := by
        simp [step,hpc,htodo,nxt,localEdge]
      obtain ⟨ni,mid,hi,hmidpc,hmidtodo,hmidsorted,hni,hmidframe⟩ :=
        insertScan_framed q r B m shape ext s.sorted nxt rfl rfl
      have hmidtodo' : mid.sortTodo=xs := by simpa [nxt] using hmidtodo
      have hmidsorted' : mid.sorted=(MedianSort.insert x s.sorted).values := by
        simpa [nxt] using hmidsorted
      obtain ⟨nt,t,ht,htpc,htright,htlookup,hnt,htframe⟩ := ih mid hmidpc hmidtodo'
      refine ⟨1+(ni+nt),t,(LocalTrace.single hs).trans (hi.trans ht),htpc,?_,htlookup,?_,?_⟩
      · rw [hmidsorted'] at htright
        exact htright
      · simp only [nxt,List.length_nil,Nat.add_zero] at hni
        rw [hmidsorted',insert_length] at hnt
        simp only [List.length_cons]
        nlinarith
      · simpa [sortWorkFrame,nxt] using htframe.trans hmidframe

theorem medianLookup_framed (q r B m : ℕ) (shape : Bool) (ext : External)
    (i : ℕ) (xs : List ℕ) (s : Config) (hpc : s.pc=.medianLookup)
    (hright : s.insertRight=xs) (hindex : s.lookupRemaining=i) (hi : i<xs.length) :
    ∃ t, LocalTrace q r B m shape ext s (i+1) t ∧ t.pc=.fetch ∧ t.selected=xs[i] ∧
      t.trialsRev=[] ∧ sortWorkFrame t=sortWorkFrame { s with trialsRev := [] } := by
  induction i generalizing xs s with
  | zero =>
      cases xs with
      | nil => simp at hi
      | cons x xs =>
          let t : Config := { s with
            pc := .fetch,selected := x,
            insertRight := [],sortTodo := [],sorted := [],trialsRev := [] }
          refine ⟨t,LocalTrace.single ?_,rfl,rfl,rfl,rfl⟩
          simp [step,hpc,hright,hindex,t,localEdge]
  | succ i ih =>
      cases xs with
      | nil => simp at hi
      | cons x xs =>
          let nxt : Config := { s with insertRight := xs,lookupRemaining := s.lookupRemaining-1 }
          have hs : step q r B m shape ext s=localEdge nxt := by
            simp [step,hpc,hright,hindex,nxt,localEdge]
          obtain ⟨t,ht,htpc,htvalue,httrials,htframe⟩ := ih xs nxt (by simpa [nxt] using hpc) rfl
            (by simp [nxt,hindex]) (by simpa using hi)
          refine ⟨t,?_,htpc,htvalue,httrials,?_⟩
          · simpa [Nat.add_assoc] using LocalTrace.cons hs ht
          · simpa [sortWorkFrame,nxt] using htframe

/-- Median input length/order is an explicit source table equality, to be
supplied by the actual repetition theorem. No sorting/median contract assumed. -/
theorem median_opcode_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (s : Config) (rest : List Opcode) (f : Fin (2*m+1) → Entry)
    (hpc : s.pc=.fetch) (hcode : s.code=.median::rest)
    (htrials : s.trialsRev=(List.ofFn f).reverse) :
    ∃ n t, LocalTrace q r B m shape ext s n t ∧ t.pc=.fetch ∧ t.code=rest ∧
      t.selected=MedianSort.median (fun i => (f i).1) ∧ t.trialsRev=[] ∧
      sortWorkFrame t=sortWorkFrame { s with code := rest,trialsRev := [] } ∧
      n≤2*(2*m+1)^2+5*(2*m+1)+m+5 := by
  let start : Config := { s with
    pc := .sortNext,code := rest,
    sortTodo := s.trialsRev.map Prod.fst,sorted := [] }
  have hstart : step q r B m shape ext s=localEdge start := by
    simp [step,hpc,hcode,start,localEdge]
  obtain ⟨n,mid,hsort,hmidpc,hmidright,hmidlookup,hn,hmidframe⟩ :=
    sortNext_framed q r B m shape ext start.sortTodo start rfl rfl
  have hright : mid.insertRight=(MedianSort.sort (List.ofFn (fun i => (f i).1))).values := by
    simpa only [start,htrials,List.map_reverse,List.map_ofFn,Function.comp_def,foldInsert_reverse] using hmidright
  have hlen : m<mid.insertRight.length := by
    rw [hright,MedianSort.sort_length,List.length_ofFn]
    omega
  obtain ⟨t,hlookup,htpc,htvalue,httrials,htframe⟩ :=
    medianLookup_framed q r B m shape ext m mid.insertRight mid hmidpc rfl hmidlookup hlen
  have hframe : sortWorkFrame t=sortWorkFrame { s with code := rest,trialsRev := [] } := by
    have hh := congrArg (fun a : Config => { a with trialsRev := [] }) hmidframe
    have hh' : sortWorkFrame { mid with trialsRev := [] }=
        sortWorkFrame { s with code := rest,trialsRev := [] } := by
      simpa [sortWorkFrame,start] using hh
    exact htframe.trans hh'
  refine ⟨1+(n+(m+1)),t,(LocalTrace.single hstart).trans (hsort.trans hlookup),
    htpc,?_,?_,httrials,hframe,?_⟩
  · simpa [sortWorkFrame] using congrArg Config.code hframe
  · simpa [hright,MedianSort.median,List.get_eq_getElem] using htvalue
  · simp [start,htrials] at hn
    nlinarith

end QecReliability.OracleCost.WholeWrapperCandidate
