import WholeWrapperLocalProofs

/-! Exact framed transitions for the two raw-cache
reversals and both endpoint calls. These bridge missing post-cache phases of
the SAME whole controller, preserving raw tables and charging endpoint edges.
No final-output, runtime, or representation contract is a hypothesis. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate
open RationalOutput

theorem reverseBad_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (xs : List Entry) (s : Config) (hpc : s.pc=.reverseBad) (hsrc : s.pairSrc=xs) :
    LocalTrace q r B m shape ext s (xs.length+1)
      { s with
        pc := .endpointZero, badTable := xs.reverse++s.pairDst,
        pairSrc := [], pairDst := [] } := by
  induction xs generalizing s with
  | nil =>
      apply LocalTrace.single
      simp [step,hpc,hsrc,localEdge]
  | cons x xs ih =>
      let nxt : Config := { s with pairSrc := xs,pairDst := x::s.pairDst }
      have hs : step q r B m shape ext s=localEdge nxt := by
        simp [step,hpc,hsrc,localEdge,nxt]
      have ht := ih nxt (by simpa [nxt] using hpc) rfl
      simpa [nxt,List.reverse_cons,List.append_assoc] using LocalTrace.cons hs ht

theorem reverseGood_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (xs : List Entry) (s : Config) (hpc : s.pc=.reverseGood) (hsrc : s.pairSrc=xs) :
    LocalTrace q r B m shape ext s (xs.length+1)
      { s with
        pc := .reverseBad, goodTable := xs.reverse++s.pairDst,
        pairSrc := s.badRev,pairDst := [],badRev := [] } := by
  induction xs generalizing s with
  | nil =>
      apply LocalTrace.single
      simp [step,hpc,hsrc,localEdge]
  | cons x xs ih =>
      let nxt : Config := { s with pairSrc := xs,pairDst := x::s.pairDst }
      have hs : step q r B m shape ext s=localEdge nxt := by
        simp [step,hpc,hsrc,localEdge,nxt]
      have ht := ih nxt (by simpa [nxt] using hpc) rfl
      simpa [nxt,List.reverse_cons,List.append_assoc] using LocalTrace.cons hs ht

/-- Both raw lists are materialized in forward order by actual one-cons
reverse loops; all other Config fields remain literally framed. -/
theorem finish_tables_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (s : Config) (rest : List Opcode) (hpc : s.pc=.fetch)
    (hcode : s.code=.finish::rest) :
    LocalTrace q r B m shape ext s (s.goodRev.length+s.badRev.length+3)
      { s with
        pc := .endpointZero,code := rest,goodRev := [],badRev := [],
        goodTable := s.goodRev.reverse,badTable := s.badRev.reverse,
        pairSrc := [],pairDst := [] } := by
  let start : Config := { s with
    pc := .reverseGood,code := rest,
    pairSrc := s.goodRev,pairDst := [],goodRev := [] }
  have hstart : step q r B m shape ext s=localEdge start := by
    simp [step,hpc,hcode,start,localEdge]
  let middle : Config := { start with
    pc := .reverseBad,
    goodTable := s.goodRev.reverse,pairSrc := s.badRev,pairDst := [],badRev := [] }
  have hgood : LocalTrace q r B m shape ext start (s.goodRev.length+1) middle := by
    simpa [start,middle] using reverseGood_trace q r B m shape ext s.goodRev start rfl rfl
  have hbad := reverseBad_trace q r B m shape ext s.badRev middle rfl rfl
  have all := (LocalTrace.single hstart).trans (hgood.trans hbad)
  simpa [start,middle,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all

/-- Ghost totals concatenate by addition and peak maximum; nothing is stored
as a runtime history or clock register. -/
def Totals.append (a b : Totals) : Totals :=
  ⟨a.dispatches+b.dispatches,a.calls+b.calls,a.oracleTime+b.oracleTime,
    a.frontendTime+b.frontendTime,a.endpointTime+b.endpointTime,
    max a.boundaryPeak b.boundaryPeak⟩

theorem Trace.trans {q r B m : ℕ} {shape : Bool} {ext : External}
    {s t u : Config} {a b : Totals} {ea eb : List RequestKey}
    (p : Trace q r B m shape ext s a ea t)
    (h : Trace q r B m shape ext t b eb u) :
    Trace q r B m shape ext s (Totals.append a b) (ea++eb) u := by
  induction p with
  | nil s => simpa [Totals.append] using h
  | cons he tail ih =>
      simpa [Totals.append,Totals.cons,List.append_assoc,Nat.add_assoc,
        Nat.add_comm,Nat.add_left_comm,max_assoc] using Trace.cons he (ih h)

/-- Exactly two endpoint boundary edges. Source boundary equality may later
rewrite the two values to the exact old dyadic endpoints; acquisition costs
are already charged once each, not treated as constant-time free values. -/
theorem endpoints_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (s : Config) (hpc : s.pc=.endpointZero) :
    Trace q r B m shape ext s
      { dispatches := 2,
        endpointTime := (ext.endpoint false).time+(ext.endpoint true).time,
        boundaryPeak := max (ext.endpoint false).space (ext.endpoint true).space }
      []
      { s with
        pc := .repair,endpoint0 := (ext.endpoint false).value,
        endpoint1 := (ext.endpoint true).value,previous := (ext.endpoint false).value,
        repairGood := s.goodTable,repairBad := s.badTable,repairIndex := 0,
        outputRev := [],maxAccumulatorDen := (ext.endpoint false).value.den } := by
  let mid : Config := { s with pc := .endpointOne,endpoint0 := (ext.endpoint false).value }
  let last : Config := { s with
    pc := .repair,endpoint0 := (ext.endpoint false).value,
    endpoint1 := (ext.endpoint true).value,previous := (ext.endpoint false).value,
    repairGood := s.goodTable,repairBad := s.badTable,repairIndex := 0,
    outputRev := [],maxAccumulatorDen := (ext.endpoint false).value.den }
  let e0 : Edge := ⟨mid,0,0,0,(ext.endpoint false).time,(ext.endpoint false).space,none⟩
  let e1 : Edge := ⟨last,0,0,0,(ext.endpoint true).time,(ext.endpoint true).space,none⟩
  have h0 : step q r B m shape ext s=some e0 := by
    simp [step,hpc,e0,mid]
  have h1 : step q r B m shape ext mid=some e1 := by
    simp [step,e1,mid,last]
  have path := Trace.cons h0 (Trace.cons h1 (Trace.nil last))
  simpa [e0,e1,mid,last,Totals.cons] using path

/-- Framed post-cache bridge: forward raw lists and exact endpoint costs are
ready for the already existing repair_trace, without assumptions about the
whole final output or total controller runtime. -/
theorem finish_to_repair_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (s : Config) (rest : List Opcode) (hpc : s.pc=.fetch)
    (hcode : s.code=.finish::rest) :
    Trace q r B m shape ext s
      { dispatches := s.goodRev.length+s.badRev.length+5,
        endpointTime := (ext.endpoint false).time+(ext.endpoint true).time,
        boundaryPeak := max (ext.endpoint false).space (ext.endpoint true).space }
      []
      { s with
        pc := .repair,code := rest,goodRev := [],badRev := [],
        goodTable := s.goodRev.reverse,badTable := s.badRev.reverse,pairSrc := [],pairDst := [],
        endpoint0 := (ext.endpoint false).value,endpoint1 := (ext.endpoint true).value,
        previous := (ext.endpoint false).value,repairGood := s.goodRev.reverse,
        repairBad := s.badRev.reverse,repairIndex := 0,outputRev := [],
        maxAccumulatorDen := (ext.endpoint false).value.den } := by
  let middle : Config := { s with
    pc := .endpointZero,code := rest,
    goodRev := [],badRev := [],goodTable := s.goodRev.reverse,
    badTable := s.badRev.reverse,pairSrc := [],pairDst := [] }
  have ht := (finish_tables_trace q r B m shape ext s rest hpc hcode).toTrace
  have he := endpoints_trace q r B m shape ext middle rfl
  have path := ht.trans he
  simpa [middle,Totals.append,localTotals,Nat.add_assoc] using path

end QecReliability.OracleCost.WholeWrapperCandidate
