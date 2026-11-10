import WholeWrapperContracts
import WholeWrapperBitLengths

/-!

These are proofs about the ACTUAL 20-tag `step`, not a replacement traversal.
No complete RepresentationInvariant theorem is
claimed: the exact residual scalar-word obligation is stated at the end.
-/
namespace QecReliability.OracleCost.WholeWrapperCandidate

/-- All bounds below concern every finite reachable prefix, including a
prefix ending in the middle of an intercepted SAT invocation. -/
def Reachable (q r B m : ℕ) (shape : Bool) (ext : External) (s : Config) : Prop :=
  ∃ totals events, Trace q r B m shape ext (initial q r m) totals events s

/-- There are always 22 represented fields. This also exhibits why the old
OPEN Claim cannot hold for arbitrary Kfields, e.g. Kfields=0. -/
theorem representation_requires_22 {q B Q K L V : ℕ} {s : Config}
    (h : RepresentationInvariant q B Q K L V s) : 22≤K := by
  simpa only [configFields_length] using h.fields

/-- Native prefix state is initially a valid zero result, before the first
cell has started; validity does not require PC=prefix. -/
theorem initial_prefix_valid (q r B m : ℕ) :
    PrefixTransitions.Valid q (4*B+1) (initial q r m).prefixState := by
  exact ⟨q,0,rfl,PrefixTransitions.StackOK.nil (Nat.zero_le _)⟩

/-- Every wrapper edge either leaves the old native state unchanged, starts
its root, or performs its actual native step. External time is irrelevant. -/
theorem step_prefix_valid {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} {edge : Edge}
    (hs : PrefixTransitions.Valid q (4*B+1) s.prefixState)
    (he : step q r B m shape ext s=some edge) :
    PrefixTransitions.Valid q (4*B+1) edge.next.prefixState := by
  cases hp : s.pc <;> simp only [step,hp] at he
  all_goals try contradiction
  all_goals repeat' first
    | (simp only [localEdge,Option.some.injEq] at he; subst edge)
    | split at he
  all_goals try simp_all only [localEdge,Option.some.injEq]
  all_goals first
    | exact hs
    | exact PrefixTransitions.initial_valid q (4*B+1)
    | exact PrefixTransitions.step_valid (fun _ => emptyReply) hs (by assumption)
    | exact PrefixTransitions.step_valid (fun _ => ⟨s.reply,0,0⟩) hs (by assumption)

/-- Generic invariant induction over the real trace; it adds no invariant
premise to any theorem below, whose base and step are both supplied. -/
theorem Trace.preserves {q r B m : ℕ} {shape : Bool} {ext : External}
    {s t : Config} {totals : Totals} {events : List RequestKey}
    (h : Trace q r B m shape ext s totals events t) (P : Config → Prop)
    (hstep : ∀ a e, P a → step q r B m shape ext a=some e → P e.next)
    (hs : P s) : P t := by
  induction h with
  | nil => exact hs
  | cons he _ ih => exact ih (hstep _ _ hs he)

theorem reachable_prefix_valid {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} (h : Reachable q r B m shape ext s) :
    PrefixTransitions.Valid q (4*B+1) s.prefixState := by
  obtain ⟨totals,events,h⟩ := h
  exact h.preserves (fun s => PrefixTransitions.Valid q (4*B+1) s.prefixState)
    (fun _ _ => step_prefix_valid) (initial_prefix_valid q r B m)

theorem reachable_prefix_bit_bound {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} (h : Reachable q r B m shape ext s) :
    (PrefixTransitions.configBits s.prefixState).length≤
      PrefixTransitions.configBitBound q (4*B+1) :=
  PrefixTransitions.configBits_length (reachable_prefix_valid h)

/-- No edge invents code or expands a continuation. -/
theorem step_code_tail {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} {edge : Edge} (he : step q r B m shape ext s=some edge) :
    s.code=edge.next.code ∨ ∃ op, s.code=op::edge.next.code := by
  cases hp : s.pc <;> simp only [step,hp] at he
  all_goals try contradiction
  all_goals repeat' first
    | (simp only [localEdge,Option.some.injEq] at he; subst edge)
    | split at he
  all_goals try simp_all [localEdge]

theorem Trace.code_suffix {q r B m : ℕ} {shape : Bool} {ext : External}
    {s t : Config} {totals : Totals} {events : List RequestKey}
    (h : Trace q r B m shape ext s totals events t) :
    ∃ consumed, s.code=consumed++t.code := by
  induction h with
  | nil => exact ⟨[],rfl⟩
  | cons he _ ih =>
      obtain ⟨consumed,hconsumed⟩ := ih
      rcases step_code_tail he with hsame | ⟨op,htail⟩
      · exact ⟨consumed,hsame.trans hconsumed⟩
      · exact ⟨op::consumed,by simp only [htail,hconsumed,List.cons_append]⟩

theorem reachable_code_suffix {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} (h : Reachable q r B m shape ext s) :
    ∃ consumed, program q r m=consumed++s.code := by
  obtain ⟨totals,events,h⟩ := h
  exact h.code_suffix

/-- One reserved cell record, not one record per oracle call. -/
def cellPending (s : Config) : ℕ :=
  match s.pc with
  | .prefix => 1
  | .compile | .invoke | .resume =>
      match s.returnTag with | .prefix => 1 | .base => 0
  | _ => 0

/-- One reserved trial record throughout reversal/selection and commit. -/
def trialPending (s : Config) : ℕ :=
  match s.pc with
  | .reverseCells | .selectScan | .trialCommit => 1
  | _ => 0

/-- All Entry lists except repair copies, counted WITHOUT sharing credit. -/
def entryMass (s : Config) : ℕ :=
  s.cellsRev.length+s.pairSrc.length+s.pairDst.length+s.trialsRev.length+
  s.goodRev.length+s.badRev.length+s.goodTable.length+s.badTable.length

def EntryCapacity (P : ℕ) (s : Config) : Prop :=
  s.code.length+entryMass s+cellPending s+trialPending s≤P

/-- This credit invariant needs no SAT exactness, cap bound, call bound,
whole-value refinement, or schedule oracle. Fetching an opcode releases at
most one record credit. Prefix and selection loops merely carry that credit. -/
theorem step_entry_capacity {q r B m P : ℕ} {shape : Bool} {ext : External}
    {s : Config} {edge : Edge} (hs : EntryCapacity P s)
    (he : step q r B m shape ext s=some edge) : EntryCapacity P edge.next := by
  cases hp : s.pc <;> simp only [step,hp] at he
  all_goals try contradiction
  all_goals repeat' first
    | (simp only [localEdge,Option.some.injEq] at he; subst edge)
    | split at he
  all_goals try simp_all [localEdge,EntryCapacity,entryMass,cellPending,trialPending]
  all_goals omega

theorem reachable_entry_capacity {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} (h : Reachable q r B m shape ext s) :
    EntryCapacity (program q r m).length s := by
  obtain ⟨totals,events,h⟩ := h
  apply h.preserves (EntryCapacity (program q r m).length)
    (fun _ _ => step_entry_capacity)
  simp [EntryCapacity,entryMass,cellPending,trialPending,initial]

/-- Sorting has scratch COPIES, not sharing. Each scratch list gets its own
capacity bound. The active insertion includes one reserved inserted element. -/
structure SortCapacity (P : ℕ) (s : Config) : Prop where
  total : s.sortTodo.length+s.sorted.length≤P
  leftZero : s.pc≠.insertScan → s.pc≠.insertRestore → s.insertLeftRev=[]
  resultZero : s.pc≠.insertRestore → s.insertResult=[]
  scan : s.pc=.insertScan →
    s.sortTodo.length+s.insertLeftRev.length+s.insertRight.length+1≤P
  restore : s.pc=.insertRestore →
    s.sortTodo.length+s.insertLeftRev.length+s.insertResult.length≤P
  left : s.insertLeftRev.length≤P
  right : s.insertRight.length≤P
  result : s.insertResult.length≤P

set_option maxHeartbeats 800000 in
theorem step_sort_capacity {q r B m P : ℕ} {shape : Bool} {ext : External}
    {s : Config} {edge : Edge} (hentries : EntryCapacity P s)
    (hs : SortCapacity P s) (he : step q r B m shape ext s=some edge) :
    SortCapacity P edge.next := by
  rcases hs with ⟨htotal,hleftZero,hresultZero,hscan,hrestore,hleft,hright,hresult⟩
  unfold EntryCapacity entryMass at hentries
  cases hp : s.pc <;> simp only [step,hp] at he
  all_goals try contradiction
  all_goals repeat' first
    | (simp only [localEdge,Option.some.injEq] at he; subst edge)
    | split at he
  all_goals try simp_all [localEdge]
  all_goals constructor <;> try simp_all
  all_goals omega

theorem reachable_sort_capacity {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} (h : Reachable q r B m shape ext s) :
    SortCapacity (program q r m).length s := by
  obtain ⟨totals,events,h⟩ := h
  have both := h.preserves
    (fun s => EntryCapacity (program q r m).length s ∧
      SortCapacity (program q r m).length s)
    (by intro s e hs he; exact ⟨step_entry_capacity hs.1 he,
        step_sort_capacity hs.1 hs.2 he⟩)
    (by constructor
        · simp [EntryCapacity,entryMass,cellPending,trialPending,initial]
        · constructor <;> simp [initial])
  exact both.2

/-- Repair copies and both output lists are charged separately from raw
input tables. This one-sided conservation law counts a good input pair as
credit for its eventual output. Bad inputs only shrink. -/
structure RepairCapacity (P : ℕ) (s : Config) : Prop where
  total : s.repairGood.length+s.outputRev.length+s.output.length≤P
  bad : s.repairBad.length≤P
  earlyOutput : s.pc≠.reverseOutput → s.pc≠.done → s.output=[]

theorem step_repair_capacity {q r B m P : ℕ} {shape : Bool} {ext : External}
    {s : Config} {edge : Edge} (hentries : EntryCapacity P s)
    (hs : RepairCapacity P s) (he : step q r B m shape ext s=some edge) :
    RepairCapacity P edge.next := by
  rcases hs with ⟨htotal,hbad,hearly⟩
  unfold EntryCapacity entryMass at hentries
  cases hp : s.pc <;> simp only [step,hp] at he
  all_goals try contradiction
  all_goals repeat' first
    | (simp only [localEdge,Option.some.injEq] at he; subst edge)
    | split at he
  all_goals try simp_all [localEdge]
  all_goals constructor <;> try simp_all
  all_goals omega

theorem reachable_repair_capacity {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} (h : Reachable q r B m shape ext s) :
    RepairCapacity (program q r m).length s := by
  obtain ⟨totals,events,h⟩ := h
  have both := h.preserves
    (fun s => EntryCapacity (program q r m).length s ∧
      RepairCapacity (program q r m).length s)
    (by intro s e hs he; exact ⟨step_entry_capacity hs.1 he,
        step_repair_capacity hs.1 hs.2 he⟩)
    (by constructor
        · simp [EntryCapacity,entryMass,cellPending,trialPending,initial]
        · constructor <;> simp [initial])
  exact both.2

/-- All retained list CARDINALITIES are bounded independently of B and of
any oracle-call total. The opcode list itself is charged in full. -/
theorem reachable_list_capacities {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} (h : Reachable q r B m shape ext s) :
    let P := (program q r m).length
    s.code.length≤P ∧ entryMass s≤P ∧
    s.sortTodo.length≤P ∧ s.sorted.length≤P ∧
    s.insertLeftRev.length≤P ∧ s.insertRight.length≤P ∧ s.insertResult.length≤P ∧
    s.repairGood.length≤P ∧ s.repairBad.length≤P ∧
    s.outputRev.length≤P ∧ s.output.length≤P := by
  have he := reachable_entry_capacity h
  have hs := reachable_sort_capacity h
  have hr := reachable_repair_capacity h
  dsimp only
  unfold EntryCapacity at he
  exact ⟨by omega,by omega,by have := hs.total; omega,
    by have := hs.total; omega,hs.left,hs.right,hs.result,
    by have := hr.total; omega,hr.bad,by have := hr.total; omega,
    by have := hr.total; omega⟩

/-- Exact remaining scalar obligations, not asserted or used as an input
premise to claim reachability. The precise original profile V requires these
for call counters, selector doubling, stored count values, all ratio words,
and repair counters. No opaque whole RepresentationInvariant is assumed. -/
def RemainingWordClaim (q r B m : ℕ) (shape : Bool) (ext : External) : Prop :=
  ∀ s, Reachable q r B m shape ext s →
    ∀ f∈configFields s, ∀ x∈f, x≤stateValueBound q r B m

end QecReliability.OracleCost.WholeWrapperCandidate
