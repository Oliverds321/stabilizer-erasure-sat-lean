import WholeWrapperFinishTraces
import WholeWrapperRequestBounds

/-! Native PrefixTransitions steps are expanded
into the actual wrapper's interception phases. Persistent registers are framed
by an equality of normalized Configs; only native/callback scratch is erased.
No alternate traversal or final refinement/resource contract is assumed. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate
open RationalOutput

/-- Erases precisely the fields changed inside a cell's native/callback loop.
All code, indices, cells/trials/raw tables, call aggregates, sort/repair data,
and output/report fields remain present in this equality. The canonical erased
pc is fetch, matching selectionFrame so their normalizations commute. -/
def prefixFrame (s : Config) : Config :=
  { s with
    pc := .fetch,prefixState := ⟨.ret 0,[]⟩,cellCalls := 0,
    returnTag := .prefix,request := .base false 0 0,query := [],reply := false }

def cellKey (s : Config) (pre : List Bool) : RequestKey :=
  .cell s.good s.coefficient s.repetition s.scale pre

theorem cellKey_of_frame {s anchor : Config}
    (h : prefixFrame s=prefixFrame anchor) (pre : List Bool) :
    cellKey s pre=cellKey anchor pre := by
  simpa [prefixFrame,cellKey] using congrArg (fun t => cellKey t pre) h

/-- Primitive fidelity only for valid prefixes; concrete BoundaryCorrect
will discharge this. It is not a whole-run simulation or resource premise. -/
def PrefixAgreement (q : ℕ) (ext : External) (anchor : Config)
    (oracle : List Bool → SATReply) : Prop :=
  ∀ pre, pre.length≤q → ext.sat (ext.compileQuery (cellKey anchor pre)).bits=oracle pre

def prefixBoundaryPeak (ext : External) (anchor : Config)
    (oracle : List Bool → SATReply) (pres : List (List Bool)) : ℕ :=
  (pres.map (fun pre => max (ext.compileQuery (cellKey anchor pre)).constructionSpace
    (oracle pre).workspace)).foldr max 0

def prefixTraceTotals (ext : External) (anchor : Config)
    (oracle : List Bool → SATReply) (n : ℕ) (pres : List (List Bool)) : Totals :=
  { dispatches := n+3*pres.length,calls := pres.length,
    oracleTime := (pres.map (fun pre => (oracle pre).time)).sum,
    frontendTime := (pres.map (fun pre =>
      (ext.compileQuery (cellKey anchor pre)).constructionTime)).sum,
    endpointTime := 0,boundaryPeak := prefixBoundaryPeak ext anchor oracle pres }

theorem prefixBoundaryPeak_append (ext : External) (anchor : Config)
    (oracle : List Bool → SATReply) (a b : List (List Bool)) :
    prefixBoundaryPeak ext anchor oracle (a++b)=
      max (prefixBoundaryPeak ext anchor oracle a) (prefixBoundaryPeak ext anchor oracle b) := by
  induction a with
  | nil => simp [prefixBoundaryPeak]
  | cons x xs ih =>
      simpa [prefixBoundaryPeak,max_assoc] using congrArg
        (max (max (ext.compileQuery (cellKey anchor x)).constructionSpace (oracle x).workspace)) ih

theorem prefixTraceTotals_append (ext : External) (anchor : Config)
    (oracle : List Bool → SATReply) (n k : ℕ) (a b : List (List Bool)) :
    prefixTraceTotals ext anchor oracle (n+k) (a++b)=
      Totals.append (prefixTraceTotals ext anchor oracle n a)
        (prefixTraceTotals ext anchor oracle k b) := by
  simp [prefixTraceTotals,Totals.append,prefixBoundaryPeak_append,List.map_append,
    Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

def NativeAwait (s : PrefixTransitions.Config) : Prop :=
  ∃ depth pre cap, s.control=.await depth pre cap

theorem native_nonawait_step_eq (a b : List Bool → SATReply)
    (s : PrefixTransitions.Config) (h : ¬NativeAwait s) :
    PrefixTransitions.step a s=PrefixTransitions.step b s := by
  rcases s with ⟨control,stack⟩
  cases control with
  | enter => rfl
  | ret count => cases stack with
    | nil => rfl
    | cons frame stack => cases frame <;> rfl
  | await depth pre cap => exact False.elim (h ⟨depth,pre,cap,rfl⟩)

theorem native_await_resume {oracle : List Bool → SATReply}
    {s : PrefixTransitions.Config} {e : PrefixTransitions.Edge}
    {depth cap : ℕ} {pre : List Bool}
    (hc : s.control=.await depth pre cap)
    (he : PrefixTransitions.step oracle s=some e) :
    PrefixTransitions.step (fun _ => ⟨(oracle pre).value,0,0⟩) s=
      some ⟨e.next,1,0⟩ := by
  rcases s with ⟨control,stack⟩
  simp only at hc
  subst control
  simp only [PrefixTransitions.step,Option.some.injEq] at he
  subst e
  rfl

/-- One non-Await native transition is exactly one actual local wrapper edge. -/
theorem prefix_nonawait_step (q r B m : ℕ) (shape : Bool) (ext : External)
    (oracle : List Bool → SATReply) (s : Config) (e : PrefixTransitions.Edge)
    (hpc : s.pc=.prefix) (hnot : ¬NativeAwait s.prefixState)
    (he : PrefixTransitions.step oracle s.prefixState=some e) :
    step q r B m shape ext s=localEdge { s with prefixState := e.next } := by
  have hlocal : PrefixTransitions.step (fun _ => emptyReply) s.prefixState=some e := by
    rw [native_nonawait_step_eq _ oracle s.prefixState hnot]
    exact he
  cases hc : s.prefixState.control with
  | enter depth pre cap => simp [step,hpc,hc,hlocal,localEdge]
  | ret count => simp [step,hpc,hc,hlocal,localEdge]
  | await depth pre cap => exact False.elim (hnot ⟨depth,pre,cap,hc⟩)

/-- Exact four-edge interception, including compile/invoke/resume. The one
real invoke edge emits the actual RequestKey and charges the full reply once. -/
theorem prefix_await_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (anchor s : Config) (oracle : List Bool → SATReply)
    (e : PrefixTransitions.Edge) (depth cap : ℕ) (pre : List Bool)
    (hpc : s.pc=.prefix) (hc : s.prefixState.control=.await depth pre cap)
    (hframe : prefixFrame s=prefixFrame anchor)
    (hreply : ext.sat (ext.compileQuery (cellKey anchor pre)).bits=oracle pre)
    (he : PrefixTransitions.step oracle s.prefixState=some e) :
    ∃ t, Trace q r B m shape ext s (prefixTraceTotals ext anchor oracle 1 [pre])
        [cellKey anchor pre] t ∧
      t.pc=.prefix ∧ t.prefixState=e.next ∧ t.cellCalls=s.cellCalls+1 ∧
      prefixFrame t=prefixFrame s := by
  let key := cellKey anchor pre
  let built := ext.compileQuery key
  let s1 : Config := { s with pc := .compile,returnTag := .prefix,request := key }
  let s2 : Config := { s1 with pc := .invoke,query := built.bits }
  let s3 : Config := { s2 with pc := .resume,reply := (oracle pre).value }
  let t : Config := { s3 with
    pc := .prefix,prefixState := e.next,
    cellCalls := s.cellCalls+1,query := [] }
  let e0 : Edge := ⟨s1,0,0,0,0,0,none⟩
  let e1 : Edge := ⟨s2,0,0,built.constructionTime,0,built.constructionSpace,none⟩
  let e2 : Edge := ⟨s3,1,(oracle pre).time,0,0,(oracle pre).workspace,some key⟩
  let e3 : Edge := ⟨t,0,0,0,0,0,none⟩
  have hk : cellKey s pre=key := cellKey_of_frame hframe pre
  have h0 : step q r B m shape ext s=some e0 := by
    simp only [step,hpc,hc]
    change localEdge { s with
      pc := .compile,returnTag := .prefix,
      request := cellKey s pre }=some e0
    rw [hk]
    rfl
  have h1 : step q r B m shape ext s1=some e1 := by
    simp [step,e1,s1,s2,built]
  have h2 : step q r B m shape ext s2=some e2 := by
    simp [step,e2,s3,s2,s1,built,key,hreply]
  have hresume := native_await_resume hc he
  have h3 : step q r B m shape ext s3=some e3 := by
    simp [step,e3,t,s3,s2,s1,hresume,localEdge]
  have path := Trace.cons h0 (Trace.cons h1 (Trace.cons h2 (Trace.cons h3 (Trace.nil t))))
  refine ⟨t,?_,rfl,rfl,rfl,?_⟩
  · simpa [e0,e1,e2,e3,key,built,Totals.cons,prefixTraceTotals,prefixBoundaryPeak,
      Nat.add_assoc] using path
  · rfl

/-- One native transition, with its exact emitted-prefix contribution. The
query fidelity premise is used only where native Valid proves prefix length. -/
theorem prefix_native_step_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (anchor s : Config) (oracle : List Bool → SATReply) (e : PrefixTransitions.Edge)
    (hpc : s.pc=.prefix) (hframe : prefixFrame s=prefixFrame anchor)
    (hvalid : PrefixTransitions.Valid q (4*B+1) s.prefixState)
    (hagrees : PrefixAgreement q ext anchor oracle)
    (he : PrefixTransitions.step oracle s.prefixState=some e) :
    ∃ t, Trace q r B m shape ext s
        (prefixTraceTotals ext anchor oracle 1 (PrefixTransitions.emitted s.prefixState))
        ((PrefixTransitions.emitted s.prefixState).map (cellKey anchor)) t ∧
      t.pc=.prefix ∧ t.prefixState=e.next ∧
      t.cellCalls=s.cellCalls+(PrefixTransitions.emitted s.prefixState).length ∧
      prefixFrame t=prefixFrame s := by
  by_cases hawait : NativeAwait s.prefixState
  · obtain ⟨depth,pre,cap,hc⟩ := hawait
    have hp := native_await_prefix_length hvalid hc
    obtain ⟨t,hpath,hpc',hnative,hcalls,hframe'⟩ :=
      prefix_await_trace q r B m shape ext anchor s oracle e depth cap pre hpc hc hframe
        (hagrees pre hp) he
    exact ⟨t,by simpa [PrefixTransitions.emitted,hc] using hpath,hpc',hnative,
      by simpa [PrefixTransitions.emitted,hc] using hcalls,hframe'⟩
  · have hempty : PrefixTransitions.emitted s.prefixState=[] := by
      cases hc : s.prefixState.control with
      | enter => simp [PrefixTransitions.emitted,hc]
      | ret => simp [PrefixTransitions.emitted,hc]
      | await depth pre cap => exact False.elim (hawait ⟨depth,pre,cap,hc⟩)
    let t : Config := { s with prefixState := e.next }
    have hstep := prefix_nonawait_step q r B m shape ext oracle s e hpc hawait he
    refine ⟨t,?_,?_,rfl,?_,rfl⟩
    · simpa [hempty,prefixTraceTotals,prefixBoundaryPeak,localTotals,t] using
        (LocalTrace.single hstep).toTrace
    · simpa [t] using hpc
    · simp [hempty,t]

/-- Full native EmissionTrace lift, not just output equality. Config framing
makes this usable inside the surrounding scheduled trial/coefficient proof. -/
theorem prefix_emission_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (anchor : Config) (oracle : List Bool → SATReply)
    {start final : PrefixTransitions.Config} {n : ℕ} {pres : List (List Bool)}
    (native : PrefixTransitions.EmissionTrace oracle start n pres final)
    (s : Config) (hpc : s.pc=.prefix) (hstate : s.prefixState=start)
    (hframe : prefixFrame s=prefixFrame anchor)
    (hvalid : PrefixTransitions.Valid q (4*B+1) start)
    (hagrees : PrefixAgreement q ext anchor oracle) :
    ∃ t, Trace q r B m shape ext s (prefixTraceTotals ext anchor oracle n pres)
        (pres.map (cellKey anchor)) t ∧
      t.pc=.prefix ∧ t.prefixState=final ∧ t.cellCalls=s.cellCalls+pres.length ∧
      prefixFrame t=prefixFrame s := by
  induction native generalizing s with
  | nil start =>
      refine ⟨s,?_,hpc,hstate,by simp,rfl⟩
      simpa [prefixTraceTotals,prefixBoundaryPeak] using Trace.nil s
  | @cons start e final n pres he tail ih =>
      have he' : PrefixTransitions.step oracle s.prefixState=some e := by
        rw [hstate]
        exact he
      have hvalid' : PrefixTransitions.Valid q (4*B+1) s.prefixState := by
        rw [hstate]
        exact hvalid
      obtain ⟨mid,hfirst,hmidpc,hmidstate,hmidcalls,hmidframe⟩ :=
        prefix_native_step_trace q r B m shape ext anchor s oracle e hpc hframe
          hvalid' hagrees he'
      have hnext := PrefixTransitions.step_valid oracle hvalid he
      obtain ⟨t,ht,htpc,htstate,htcalls,htframe⟩ :=
        ih mid hmidpc hmidstate (hmidframe.trans hframe) hnext
      refine ⟨t,?_,htpc,htstate,?_,htframe.trans hmidframe⟩
      · have both := hfirst.trans ht
        rw [← prefixTraceTotals_append] at both
        simpa [hstate,List.map_append,Nat.add_comm] using both
      · rw [htcalls,hmidcalls,hstate,List.length_append]
        omega

end QecReliability.OracleCost.WholeWrapperCandidate
