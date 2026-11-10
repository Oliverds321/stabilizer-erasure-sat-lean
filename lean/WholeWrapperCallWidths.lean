import WholeWrapperEncodedSubset

/-! A full-tree potential bounds counter widths even for an
inconsistent callback. This is NOT the sharper exact-SAT CALL/TIME bound.
Numeric counter bounds may be exponential in q; their binary widths are not. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate

def subtreeCalls (depth : ℕ) : ℕ := 2^(depth+1)-1

def nativeControlCredit : PrefixTransitions.Control → ℕ
  | .enter depth _ _ | .await depth _ _ => subtreeCalls depth
  | .ret _ => 0

def nativeFrameCredit : PrefixTransitions.Frame → ℕ
  | .left depth _ _ => subtreeCalls depth
  | .right _ => 0

def nativeRemaining (s : PrefixTransitions.Config) : ℕ :=
  nativeControlCredit s.control+(s.stack.map nativeFrameCredit).sum

/-- A future full binary subtree is reserved by each saved left frame. A
right frame reserves none. Each native await spends at least one unit. -/
theorem native_remaining_step (oracle : List Bool → SATReply)
    {s : PrefixTransitions.Config} {edge : PrefixTransitions.Edge}
    (he : PrefixTransitions.step oracle s=some edge) :
    edge.calls+nativeRemaining edge.next≤nativeRemaining s := by
  rcases s with ⟨control,stack⟩
  cases control with
  | enter depth pre cap =>
      simp only [PrefixTransitions.step,Option.some.injEq] at he
      subst edge
      by_cases hz : cap=0 <;>
        simp [hz,nativeRemaining,nativeControlCredit,subtreeCalls]
  | await depth pre cap =>
      simp only [PrefixTransitions.step,Option.some.injEq] at he
      subst edge
      have hp : 0<2^depth := pow_pos (by decide) _
      cases ho : (oracle pre).value with
      | false =>
          simp [ho,nativeRemaining,nativeControlCredit,subtreeCalls,pow_succ]
          omega
      | true =>
          cases depth with
          | zero =>
              simp [ho,nativeRemaining,nativeControlCredit,subtreeCalls]
          | succ depth =>
              have hd : 0<2^depth := pow_pos (by decide) _
              simp [ho,nativeRemaining,nativeControlCredit,
                nativeFrameCredit,subtreeCalls,pow_succ]
              omega
  | ret count =>
      cases stack with
      | nil => simp [PrefixTransitions.step] at he
      | cons frame stack =>
          cases frame <;>
            simp only [PrefixTransitions.step,Option.some.injEq] at he <;>
            subst edge <;> simp [nativeRemaining,nativeControlCredit,nativeFrameCredit]

theorem native_await_calls_one (oracle : List Bool → SATReply)
    {s : PrefixTransitions.Config} {edge : PrefixTransitions.Edge}
    {depth cap : ℕ} {pre : List Bool}
    (hc : s.control=.await depth pre cap)
    (he : PrefixTransitions.step oracle s=some edge) : edge.calls=1 := by
  rcases s with ⟨control,stack⟩
  simp only at hc
  subst control
  simp only [PrefixTransitions.step,Option.some.injEq] at he
  subst edge
  rfl

/-- Necessary interception invariant: resume-prefix never applies a reply
to a native Enter/Ret state. This is proved from the actual wrapper step. -/
def AwaitSuspended (s : Config) : Prop :=
  match s.pc,s.returnTag with
  | .compile,.prefix | .invoke,.prefix | .resume,.prefix =>
      ∃ depth pre cap, s.prefixState.control=.await depth pre cap
  | _,_ => True

theorem step_await_suspended {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} {edge : Edge} (hs : AwaitSuspended s)
    (he : step q r B m shape ext s=some edge) : AwaitSuspended edge.next := by
  cases hp : s.pc <;> simp only [step,hp] at he
  all_goals try contradiction
  all_goals repeat' first
    | (simp only [localEdge,Option.some.injEq] at he; subst edge)
    | split at he
  all_goals try simp_all [localEdge,AwaitSuspended]
  all_goals aesop

def fullTreeCap (q : ℕ) : ℕ := 2^(q+1)

def CellCallCredit (q : ℕ) (s : Config) : Prop :=
  s.cellCalls+nativeRemaining s.prefixState≤fullTreeCap q

theorem step_cell_call_credit {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} {edge : Edge} (hsuspended : AwaitSuspended s)
    (hs : CellCallCredit q s)
    (he : step q r B m shape ext s=some edge) : CellCallCredit q edge.next := by
  cases hp : s.pc <;> simp only [step,hp] at he
  all_goals try contradiction
  all_goals repeat' first
    | (simp only [localEdge,Option.some.injEq] at he; subst edge)
    | split at he
  all_goals try
    have hn := native_remaining_step (fun _ => emptyReply)
      (s:=s.prefixState) (by assumption)
  all_goals try
    have hn := native_remaining_step (fun _ => ⟨s.reply,0,0⟩)
      (s:=s.prefixState) (by assumption)
  all_goals try simp_all [localEdge,AwaitSuspended,CellCallCredit]
  all_goals try obtain ⟨depth,pre,cap,hawait⟩ := hsuspended
  all_goals try
    have hone := native_await_calls_one (fun _ => ⟨s.reply,0,0⟩)
      hawait (by assumption)
  all_goals try simp_all [nativeRemaining,nativeControlCredit,subtreeCalls,fullTreeCap]
  all_goals omega

/-- Base calls reserve one counter unit while outside the fetch loop. -/
def basePending (s : Config) : ℕ :=
  match s.pc,s.returnTag with
  | .compile,.base | .invoke,.base | .resume,.base => 1
  | _,_ => 0

def TrialCallCredit (q P : ℕ) (s : Config) : Prop :=
  s.trialCalls+basePending s+fullTreeCap q*cellPending s+
    fullTreeCap q*s.code.length≤fullTreeCap q*P

theorem step_trial_call_credit {q r B m P : ℕ} {shape : Bool} {ext : External}
    {s : Config} {edge : Edge} (hcell : CellCallCredit q s)
    (hs : TrialCallCredit q P s)
    (he : step q r B m shape ext s=some edge) : TrialCallCredit q P edge.next := by
  have hpos : 0<fullTreeCap q := pow_pos (by decide) _
  have hc : s.cellCalls≤fullTreeCap q := by unfold CellCallCredit at hcell; omega
  cases hp : s.pc <;> simp only [step,hp] at he
  all_goals try contradiction
  all_goals repeat' first
    | (simp only [localEdge,Option.some.injEq] at he; subst edge)
    | split at he
  all_goals try simp_all [localEdge,TrialCallCredit,basePending,cellPending,Nat.mul_add]
  all_goals cases htag : s.returnTag <;> try simp_all
  all_goals nlinarith

def CoefficientCallCredit (q P : ℕ) (s : Config) : Prop :=
  s.coefficientCalls+(fullTreeCap q*P)*trialPending s+
    (fullTreeCap q*P)*s.code.length≤(fullTreeCap q*P)*P

theorem step_coefficient_call_credit {q r B m P : ℕ} {shape : Bool} {ext : External}
    {s : Config} {edge : Edge} (htrial : TrialCallCredit q P s)
    (hs : CoefficientCallCredit q P s)
    (he : step q r B m shape ext s=some edge) : CoefficientCallCredit q P edge.next := by
  have ht : s.trialCalls≤fullTreeCap q*P := by unfold TrialCallCredit at htrial; omega
  cases hp : s.pc <;> simp only [step,hp] at he
  all_goals try contradiction
  all_goals repeat' first
    | (simp only [localEdge,Option.some.injEq] at he; subst edge)
    | split at he
  all_goals try simp_all [localEdge,CoefficientCallCredit,trialPending,Nat.mul_add]
  all_goals nlinarith

structure AllCallCredits (q P : ℕ) (s : Config) : Prop where
  suspended : AwaitSuspended s
  cell : CellCallCredit q s
  trial : TrialCallCredit q P s
  coefficient : CoefficientCallCredit q P s

theorem reachable_call_credits {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} (h : Reachable q r B m shape ext s) :
    AllCallCredits q (program q r m).length s := by
  obtain ⟨totals,events,h⟩ := h
  apply h.preserves (AllCallCredits q (program q r m).length)
  · intro s e hs he
    exact ⟨step_await_suspended hs.suspended he,
      step_cell_call_credit hs.suspended hs.cell he,
      step_trial_call_credit hs.cell hs.trial he,
      step_coefficient_call_credit hs.trial hs.coefficient he⟩
  · constructor <;> simp [initial,AwaitSuspended,CellCallCredit,TrialCallCredit,
      CoefficientCallCredit,nativeRemaining,nativeControlCredit,basePending,
      cellPending,trialPending]

theorem fullTreeCap_size (q : ℕ) : (fullTreeCap q).size≤q+2 := by
  apply Nat.size_le.mpr
  have hp : 0<2^(q+1) := pow_pos (by decide) _
  change 2^(q+1)<2^((q+1)+1)
  rw [pow_succ]
  omega

/-- The large counter VALUES never become list capacities. No epsilon^-1 or
query-count variable appears in these retained counter WORD widths. -/
theorem reachable_call_counter_sizes {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} (h : Reachable q r B m shape ext s) :
    let P := (program q r m).length
    s.cellCalls.size≤q+2 ∧ s.trialCalls.size≤q+2+P.size ∧
    s.coefficientCalls.size≤q+2+2*P.size := by
  have hs := reachable_call_credits h
  let P := (program q r m).length
  have hc : s.cellCalls≤fullTreeCap q := by have := hs.cell; unfold CellCallCredit at this; omega
  have ht : s.trialCalls≤fullTreeCap q*P := by have htrial : TrialCallCredit q P s := hs.trial; unfold TrialCallCredit at htrial; omega
  have hk : s.coefficientCalls≤(fullTreeCap q*P)*P := by
    have hcoeff : CoefficientCallCredit q P s := hs.coefficient; unfold CoefficientCallCredit at hcoeff; omega
  have hf := fullTreeCap_size q
  have hm := QecReliability.size_mul_bound (fullTreeCap q) P
  have hm2 := QecReliability.size_mul_bound (fullTreeCap q*P) P
  have hcs := Nat.size_le_size hc
  have hts := Nat.size_le_size ht
  have hks := Nat.size_le_size hk
  dsimp only
  change _ ∧ _≤q+2+P.size ∧ _≤q+2+2*P.size
  omega

end QecReliability.OracleCost.WholeWrapperCandidate
