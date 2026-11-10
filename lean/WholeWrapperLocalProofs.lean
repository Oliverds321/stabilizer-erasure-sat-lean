import WholeWrapperController

/-! Proof bodies for actual controller phases, not an alternative
selector or DFS. `LocalTrace` requires the actual `step` to produce localEdge,
so these traces cannot conceal an external SAT request. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate

inductive LocalTrace (q r B m : ℕ) (shape : Bool) (ext : External) :
    Config → ℕ → Config → Prop
  | nil (s) : LocalTrace q r B m shape ext s 0 s
  | cons {s u t n} (he : step q r B m shape ext s=localEdge u)
      (tail : LocalTrace q r B m shape ext u n t) :
      LocalTrace q r B m shape ext s (n+1) t

def localTotals (n : ℕ) : Totals := { dispatches := n }

theorem LocalTrace.toTrace {q r B m : ℕ} {shape : Bool} {ext : External}
    {s t : Config} {n : ℕ} (h : LocalTrace q r B m shape ext s n t) :
    Trace q r B m shape ext s (localTotals n) [] t := by
  induction h with
  | nil s => exact Trace.nil s
  | @cons s u t n he tail ih =>
      have hs : step q r B m shape ext s=some ⟨u,0,0,0,0,0,none⟩ := he
      simpa [localTotals,Totals.cons] using Trace.cons hs ih

theorem LocalTrace.single {q r B m : ℕ} {shape : Bool} {ext : External}
    {s t : Config} (h : step q r B m shape ext s=localEdge t) :
    LocalTrace q r B m shape ext s 1 t := by
  exact .cons h (.nil t)

theorem LocalTrace.trans {q r B m : ℕ} {shape : Bool} {ext : External}
    {s t u : Config} {a b : ℕ} (h : LocalTrace q r B m shape ext s a t)
    (g : LocalTrace q r B m shape ext t b u) :
    LocalTrace q r B m shape ext s (a+b) u := by
  induction h with
  | nil => simpa using g
  | cons he _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      LocalTrace.cons he (ih g)

/-- The final output reversal is a real loop; it is not a free List.reverse. -/
theorem reverseOutput_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (xs : List RationalOutput.Ratio) (s : Config)
    (hpc : s.pc=.reverseOutput) (hsrc : s.outputRev=xs) :
    LocalTrace q r B m shape ext s (xs.length+1)
      { s with pc := .done, outputRev := [], output := xs.reverse++s.output } := by
  induction xs generalizing s with
  | nil =>
      apply LocalTrace.single
      simp [step,hpc,hsrc,localEdge]
  | cons x xs ih =>
      let nxt : Config := { s with outputRev := xs, output := x::s.output }
      have hs : step q r B m shape ext s=localEdge nxt := by
        simp [step,hpc,hsrc,localEdge,nxt]
      have ht := ih nxt (by simpa [nxt] using hpc) rfl
      simpa [nxt,List.reverse_cons,List.append_assoc] using LocalTrace.cons hs ht

/-- Restore the traversed prefix one cons at a time after insertion. -/
theorem insertRestore_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (xs : List ℕ) (s : Config) (hpc : s.pc=.insertRestore) (hsrc : s.insertLeftRev=xs) :
    LocalTrace q r B m shape ext s (xs.length+1)
      { s with
        pc := .sortNext, sorted := xs.reverse++s.insertResult,
        insertLeftRev := [], insertRight := [], insertResult := [] } := by
  induction xs generalizing s with
  | nil =>
      apply LocalTrace.single
      simp [step,hpc,hsrc,localEdge]
  | cons x xs ih =>
      let nxt : Config := { s with insertLeftRev := xs, insertResult := x::s.insertResult }
      have hs : step q r B m shape ext s=localEdge nxt := by
        simp [step,hpc,hsrc,localEdge,nxt]
      have ht := ih nxt (by simpa [nxt] using hpc) rfl
      simpa [nxt,List.reverse_cons,List.append_assoc] using LocalTrace.cons hs ht

/-- Actual insertion scan plus restoration, with explicit step bound. It
refines the existing measured insertion, preserving every duplicate value. -/
theorem insertScan_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (xs : List ℕ) (s : Config) (hpc : s.pc=.insertScan) (hsrc : s.insertRight=xs) :
    ∃ n t, LocalTrace q r B m shape ext s n t ∧ t.pc=.sortNext ∧
      t.sortTodo=s.sortTodo ∧
      t.sorted=s.insertLeftRev.reverse++(MedianSort.insert s.insertValue xs).values ∧
      n≤2*xs.length+s.insertLeftRev.length+2 := by
  induction xs generalizing s with
  | nil =>
      let nxt : Config := { s with pc := .insertRestore, insertResult := [s.insertValue] }
      have hs : step q r B m shape ext s=localEdge nxt := by
        simp [step,hpc,hsrc,nxt,localEdge]
      have ht := insertRestore_trace q r B m shape ext s.insertLeftRev nxt rfl rfl
      let last : Config := { nxt with
        pc := .sortNext, sorted := s.insertLeftRev.reverse++nxt.insertResult,
        insertLeftRev := [], insertRight := [], insertResult := [] }
      refine ⟨s.insertLeftRev.length+2,last,?_,rfl,rfl,?_,by simp⟩
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
          pc := .sortNext, sorted := s.insertLeftRev.reverse++nxt.insertResult,
          insertLeftRev := [], insertRight := [], insertResult := [] }
        refine ⟨s.insertLeftRev.length+2,last,?_,rfl,rfl,?_,?_⟩
        · simpa [last,Nat.add_assoc] using LocalTrace.cons hs ht
        · simp [last,nxt,hsrc,MedianSort.insert,hx]
        · simp only [List.length_cons]; omega
      · let nxt : Config := { s with
          insertRight := xs,
          insertLeftRev := x::s.insertLeftRev }
        have hs : step q r B m shape ext s=localEdge nxt := by
          simp [step,hpc,hsrc,hx,nxt,localEdge]
        obtain ⟨n,t,ht,htpc,httodo,htsorted,hn⟩ := ih nxt
          (by simpa [nxt] using hpc) rfl
        refine ⟨n+1,t,LocalTrace.cons hs ht,htpc,?_,?_,?_⟩
        · simpa [nxt] using httodo
        · simpa [nxt,MedianSort.insert,hx,List.reverse_cons,List.append_assoc] using htsorted
        · simp only [nxt,List.length_cons] at hn ⊢; omega

/-- Functional specification for successive first-order insertions. -/
def foldInsert (xs acc : List ℕ) : List ℕ :=
  xs.foldl (fun sorted x => (MedianSort.insert x sorted).values) acc

/-- The controller consumes the reverse trial table, so its iterative
insertions exactly reproduce the source's tail-first insertion sort. -/
theorem foldInsert_reverse (xs : List ℕ) :
    foldInsert xs.reverse []=(MedianSort.sort xs).values := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simpa [foldInsert,List.reverse_cons,List.foldl_append,MedianSort.sort] using
        congrArg (fun sorted => (MedianSort.insert x sorted).values) ih

theorem insert_length (x : ℕ) (xs : List ℕ) :
    (MedianSort.insert x xs).values.length=xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      by_cases h : x≤y <;> simp [MedianSort.insert,h,ih]

theorem foldInsert_length (xs acc : List ℕ) :
    (foldInsert xs acc).length=xs.length+acc.length := by
  induction xs generalizing acc with
  | nil => simp [foldInsert]
  | cons x xs ih =>
      change (foldInsert xs (MedianSort.insert x acc).values).length=_
      rw [ih,insert_length]
      simp only [List.length_cons]
      omega

/-- The whole actual sort loop reaches median lookup in polynomially many
local dispatches. It starts with any accumulator, avoiding hidden recursion
or free sorting in the controller semantics. -/
theorem sortNext_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (xs : List ℕ) (s : Config) (hpc : s.pc=.sortNext) (htodo : s.sortTodo=xs) :
    ∃ n t, LocalTrace q r B m shape ext s n t ∧ t.pc=.medianLookup ∧
      t.insertRight=foldInsert xs s.sorted ∧ t.lookupRemaining=m ∧
      n≤xs.length*(2*s.sorted.length+2*xs.length+3)+1 := by
  induction xs generalizing s with
  | nil =>
      let t : Config := { s with
        pc := .medianLookup,
        insertRight := s.sorted, lookupRemaining := m }
      refine ⟨1,t,LocalTrace.single ?_,rfl,rfl,rfl,by simp⟩
      simp [step,hpc,htodo,t,localEdge]
  | cons x xs ih =>
      let nxt : Config := { s with
        pc := .insertScan, sortTodo := xs,
        insertValue := x, insertLeftRev := [], insertRight := s.sorted }
      have hs : step q r B m shape ext s=localEdge nxt := by
        simp [step,hpc,htodo,nxt,localEdge]
      obtain ⟨ni,mid,hi,hmidpc,hmidtodo,hmidsorted,hni⟩ :=
        insertScan_trace q r B m shape ext s.sorted nxt rfl rfl
      have hmidtodo' : mid.sortTodo=xs := by simpa [nxt] using hmidtodo
      have hmidsorted' : mid.sorted=(MedianSort.insert x s.sorted).values := by
        simpa [nxt] using hmidsorted
      obtain ⟨nt,t,ht,htpc,htright,htlookup,hnt⟩ := ih mid hmidpc hmidtodo'
      refine ⟨1+(ni+nt),t,(LocalTrace.single hs).trans (hi.trans ht),htpc,?_,htlookup,?_⟩
      · rw [hmidsorted'] at htright
        exact htright
      · simp only [nxt,List.length_nil,Nat.add_zero] at hni
        rw [hmidsorted',insert_length] at hnt
        simp only [List.length_cons]
        nlinarith

/-- Explicit median traversal: the lookup index decreases once per skipped
entry, and no decision callback occurs. -/
theorem medianLookup_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (i : ℕ) (xs : List ℕ) (s : Config) (hpc : s.pc=.medianLookup)
    (hright : s.insertRight=xs) (hindex : s.lookupRemaining=i) (hi : i<xs.length) :
    ∃ t, LocalTrace q r B m shape ext s (i+1) t ∧ t.pc=.fetch ∧ t.selected=xs[i] := by
  induction i generalizing xs s with
  | zero =>
      cases xs with
      | nil => simp at hi
      | cons x xs =>
          let t : Config := { s with
            pc := .fetch, selected := x,
            insertRight := [], sortTodo := [], sorted := [], trialsRev := [] }
          refine ⟨t,LocalTrace.single ?_,rfl,rfl⟩
          simp [step,hpc,hright,hindex,t,localEdge]
  | succ i ih =>
      cases xs with
      | nil => simp at hi
      | cons x xs =>
          let nxt : Config := { s with
            insertRight := xs,
            lookupRemaining := s.lookupRemaining-1 }
          have hs : step q r B m shape ext s=localEdge nxt := by
            simp [step,hpc,hright,hindex,nxt,localEdge]
          obtain ⟨t,ht,htpc,htvalue⟩ := ih xs nxt (by simpa [nxt] using hpc) rfl
            (by simp [nxt,hindex]) (by simpa using hi)
          refine ⟨t,?_,htpc,?_⟩
          · simpa [Nat.add_assoc] using LocalTrace.cons hs ht
          · exact htvalue

/-- Each reverse move and the exit dispatch is represented. This is the actual
reverseCells phase of the whole wrapper, including its selection registers. -/
theorem reverseCells_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (xs : List Entry) (s : Config) (hpc : s.pc=.reverseCells) (hsrc : s.pairSrc=xs) :
    LocalTrace q r B m shape ext s (xs.length+1)
      { s with
        pc := .selectScan, pairSrc := xs.reverse++s.pairDst,
        pairDst := [], selectIndex := 0, scaleFactor := 1 } := by
  induction xs generalizing s with
  | nil =>
      apply LocalTrace.single
      simp [step,hpc,hsrc,localEdge]
  | cons x xs ih =>
      let nxt : Config := { s with pairSrc := xs, pairDst := x::s.pairDst }
      have hs : step q r B m shape ext s=localEdge nxt := by
        simp [step,hpc,hsrc,localEdge,nxt]
      have ht := ih nxt (by simpa [nxt] using hpc) rfl
      have hc := LocalTrace.cons hs ht
      simpa [nxt,List.reverse_cons,List.append_assoc] using hc

/-- Actual first-accepted-scale scan: no SAT calls, exact existing scan value,
explicit doubling invariant, and at most length+1 dispatches. -/
theorem selectScan_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (xs : List Entry) (s : Config) (hpc : s.pc=.selectScan) (hsrc : s.pairSrc=xs)
    (hpower : s.scaleFactor=2^s.selectIndex) :
    ∃ n t, LocalTrace q r B m shape ext s n t ∧ t.pc=.trialCommit ∧
      t.selected=(ScaleSelection.scan B s.selectIndex xs).estimate ∧ n≤xs.length+1 := by
  induction xs generalizing s with
  | nil =>
      let t : Config := { s with pc := .trialCommit, selected := 1 }
      refine ⟨1,t,LocalTrace.single ?_,rfl,?_,by simp⟩
      · simp [step,hpc,hsrc,localEdge,t]
      · rfl
  | cons x xs ih =>
      by_cases hx : x.1≤4*B
      · let t : Config := { s with
          pc := .trialCommit,
          selected := max 1 (s.scaleFactor*x.1), pairSrc := [] }
        refine ⟨1,t,LocalTrace.single ?_,rfl,?_,by simp⟩
        · simp [step,hpc,hsrc,hx,localEdge,t]
        · simp [t,ScaleSelection.scan,hx,hpower]
      · let nxt : Config := { s with
          pairSrc := xs,
          selectIndex := s.selectIndex+1, scaleFactor := 2*s.scaleFactor }
        have hnextpower : nxt.scaleFactor=2^nxt.selectIndex := by
          simp only [nxt,hpower,pow_succ]
          omega
        obtain ⟨n,t,ht,hpc',hv,hn⟩ := ih nxt
          (by simpa [nxt] using hpc) rfl hnextpower
        refine ⟨n+1,t,LocalTrace.cons ?_ ht,hpc',?_,?_⟩
        · simp [step,hpc,hsrc,hx,localEdge,nxt]
        · simpa [nxt,ScaleSelection.scan,hx] using hv
        · simp only [List.length_cons]; omega

/-- The repaired running maximum retains the previous accumulator denominator,
so the empty suffix agrees with the source's recursive base case. -/
theorem repair_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (gs bs : List Entry) (s : Config) (hpc : s.pc=.repair)
    (hg : s.repairGood=gs) (hb : s.repairBad=bs) (hlen : gs.length=bs.length)
    (hden : s.previous.den≤s.maxAccumulatorDen) :
    ∃ t, LocalTrace q r B m shape ext s (gs.length+1) t ∧ t.pc=.reverseOutput ∧
      let source := RationalOutput.LinearRepair.run shape r s.endpoint0 s.endpoint1
        s.repairIndex s.previous gs bs
      t.outputRev=source.values.reverse++s.outputRev ∧
      t.pairVisits=s.pairVisits+source.pairVisits ∧
      t.ratioBuilds=s.ratioBuilds+source.ratioBuilds ∧
      t.orderComparisons=s.orderComparisons+source.orderComparisons ∧
      t.endpointTests=s.endpointTests+source.endpointTests ∧
      t.maxAccumulatorDen=max s.maxAccumulatorDen source.maxAccumulatorDen := by
  induction gs generalizing bs s with
  | nil =>
      have hbs : bs=[] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      cases hbs
      let t : Config := { s with pc := .reverseOutput, output := [] }
      refine ⟨t,LocalTrace.single ?_,rfl,?_,?_,?_,?_,?_,?_⟩
      · simp [step,hpc,hg,hb,localEdge,t]
      · simp [t,RationalOutput.LinearRepair.run]
      · simp [t,RationalOutput.LinearRepair.run]
      · simp [t,RationalOutput.LinearRepair.run]
      · simp [t,RationalOutput.LinearRepair.run]
      · simp [t,RationalOutput.LinearRepair.run]
      · simp [t,RationalOutput.LinearRepair.run,max_eq_left hden]
  | cons g gs ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          let e := RationalOutput.LinearRepair.sourceEntry r s.endpoint0 s.endpoint1
            s.repairIndex g b
          let current := if s.repairIndex=0 then e else RationalOutput.Ratio.lesser s.previous e
          let out := if shape then RationalOutput.Ratio.greater s.endpoint1 current else e
          let nxt : Config := { s with
            repairGood := gs, repairBad := bs,
            repairIndex := s.repairIndex+1, previous := current, outputRev := out::s.outputRev,
            pairVisits := s.pairVisits+1,
            ratioBuilds := s.ratioBuilds+(if s.repairIndex=0 ∨ s.repairIndex=r then 0 else 1),
            orderComparisons := s.orderComparisons+(if s.repairIndex=0 then 0 else 1)+(if shape then 1 else 0),
            endpointTests := s.endpointTests+(if s.repairIndex=0 then 1 else 2),
            maxAccumulatorDen := max s.maxAccumulatorDen
              (max s.previous.den (max e.den (max current.den out.den))) }
          have hs : step q r B m shape ext s=localEdge nxt := by
            simp [step,hpc,hg,hb,nxt,e,current,out,localEdge]
          have hd : nxt.previous.den≤nxt.maxAccumulatorDen := by
            dsimp only [nxt]
            exact (le_max_left _ _).trans
              ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
          obtain ⟨t,ht,hpc',hvalues,hvisits,hratios,hcomparisons,htests,hmax⟩ :=
            ih bs nxt (by simpa [nxt] using hpc) rfl rfl (by simpa using hlen) hd
          refine ⟨t,?_,hpc',?_,?_,?_,?_,?_,?_⟩
          · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using LocalTrace.cons hs ht
          · simpa [nxt,RationalOutput.LinearRepair.run,e,current,out,
              List.reverse_cons,List.append_assoc] using hvalues
          · simpa [nxt,RationalOutput.LinearRepair.run,e,current,out,Nat.add_assoc,
              Nat.add_comm,Nat.add_left_comm] using hvisits
          · simpa [nxt,RationalOutput.LinearRepair.run,e,current,out,Nat.add_assoc,
              Nat.add_comm,Nat.add_left_comm] using hratios
          · simpa [nxt,RationalOutput.LinearRepair.run,e,current,out,Nat.add_assoc,
              Nat.add_comm,Nat.add_left_comm] using hcomparisons
          · simpa [nxt,RationalOutput.LinearRepair.run,e,current,out,Nat.add_assoc,
              Nat.add_comm,Nat.add_left_comm] using htests
          · simpa [nxt,RationalOutput.LinearRepair.run,e,current,out,max_assoc,
              max_comm,max_left_comm] using hmax

end QecReliability.OracleCost.WholeWrapperCandidate
