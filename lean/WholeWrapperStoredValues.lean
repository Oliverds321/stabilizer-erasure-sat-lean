import WholeWrapperCallWidths
import PhysicalBridge.LinearRepairBounds

/-!
Actual-step propagation of every stored estimate and
call-count snapshot. No final refinement or resource contract is assumed.
The deliberately broad profile uses P = opcode count, not oracle-call count.
-/
namespace QecReliability.OracleCost.WholeWrapperCandidate
open RationalOutput

/-- Even when B is enormous, only B.size contributes to this word's width. -/
def storedEstimateCap (P B : ℕ) : ℕ := 2^P * (4*B+1)

theorem one_le_storedEstimateCap (P B : ℕ) : 1≤storedEstimateCap P B := by
  have h : 0<2^P := pow_pos (by decide) _
  unfold storedEstimateCap
  nlinarith

theorem native_return_le {q B count : ℕ} {state : PrefixTransitions.Config}
    (h : PrefixTransitions.Valid q (4*B+1) state)
    (hc : state.control=.ret count) : count≤4*B+1 := by
  obtain ⟨depth,budget,hcontrol,hstack⟩ := h
  rw [hc] at hcontrol
  change count=budget at hcontrol
  rw [hcontrol]
  exact hstack.bounds.2.1

/-- The accepted branch itself bounds the multiplicand. It is NOT necessary
to assume every generic pairSrc record is a cell count: in later phases that
same list legitimately contains much larger coefficient estimates. -/
theorem accepted_estimate_le {P B factor index count : ℕ}
    (hfactor : factor=2^index) (hindex : index≤P) (hcount : count≤4*B) :
    max 1 (factor*count)≤storedEstimateCap P B := by
  have hp : factor≤2^P := by
    rw [hfactor]
    exact Nat.pow_le_pow_right (by decide) hindex
  apply max_le (one_le_storedEstimateCap P B)
  exact Nat.mul_le_mul hp (by omega)

/-- Explicit copies all receive their own value bound. -/
structure EstimateWords (E : ℕ) (s : Config) : Prop where
  selected : s.selected≤E
  insertValue : s.insertValue≤E
  cellsRev : ∀ x∈s.cellsRev, x.1≤E
  pairSrc : ∀ x∈s.pairSrc, x.1≤E
  pairDst : ∀ x∈s.pairDst, x.1≤E
  trialsRev : ∀ x∈s.trialsRev, x.1≤E
  goodRev : ∀ x∈s.goodRev, x.1≤E
  badRev : ∀ x∈s.badRev, x.1≤E
  goodTable : ∀ x∈s.goodTable, x.1≤E
  badTable : ∀ x∈s.badTable, x.1≤E
  repairGood : ∀ x∈s.repairGood, x.1≤E
  repairBad : ∀ x∈s.repairBad, x.1≤E
  sortTodo : ∀ x∈s.sortTodo, x≤E
  sorted : ∀ x∈s.sorted, x≤E
  insertLeftRev : ∀ x∈s.insertLeftRev, x≤E
  insertRight : ∀ x∈s.insertRight, x≤E
  insertResult : ∀ x∈s.insertResult, x≤E

set_option maxHeartbeats 800000 in
theorem step_estimate_words {q r B m P : ℕ} {shape : Bool} {ext : External}
    {s : Config} {edge : Edge}
    (hnative : PrefixTransitions.Valid q (4*B+1) s.prefixState)
    (hselection : SelectionCapacity P s)
    (hs : EstimateWords (storedEstimateCap P B) s)
    (he : step q r B m shape ext s=some edge) :
    EstimateWords (storedEstimateCap P B) edge.next := by
  have h1 := one_le_storedEstimateCap P B
  have hcap : 4*B+1≤storedEstimateCap P B := by
    have hp : 1≤2^P := by have hpos : 0<2^P := pow_pos (by decide) _; omega
    unfold storedEstimateCap
    nlinarith
  have hret : ∀ count, s.prefixState.control=.ret count →
      count≤storedEstimateCap P B :=
    fun count hc => (native_return_le hnative hc).trans hcap
  have haccepted : ∀ count, count≤4*B →
      max 1 (s.scaleFactor*count)≤storedEstimateCap P B :=
    fun count hc => accepted_estimate_le hselection.factor hselection.index hc
  rcases hs with ⟨hselected,hvalue,hcells,hsrc,hdst,htrials,hgood,hbad,hgt,hbt,
    hrg,hrb,htodo,hsorted,hleft,hright,hresult⟩
  cases hp : s.pc <;> simp only [step,hp] at he
  all_goals try contradiction
  all_goals repeat' first
    | (simp only [localEdge,Option.some.injEq] at he; subst edge)
    | split at he
  all_goals constructor
  all_goals try assumption
  all_goals try dsimp only
  all_goals try simp_all only [List.forall_mem_cons,List.forall_mem_map,
    List.mem_nil_iff,false_implies,true_implies,forall_const,and_true,true_and,and_self,
    Nat.zero_le,Prod.fst,Prod.snd]
  all_goals first
    | assumption
    | (apply hret; assumption)
    | (apply haccepted; assumption)
    | (intros; trivial)

/-- All first components and every copied sort word, at EVERY suspension. -/
theorem reachable_estimate_words {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} (h : Reachable q r B m shape ext s) :
    EstimateWords (storedEstimateCap (program q r m).length B) s := by
  obtain ⟨totals,events,h⟩ := h
  have all := h.preserves
    (fun s => PrefixTransitions.Valid q (4*B+1) s.prefixState ∧
      EntryCapacity (program q r m).length s ∧
      SelectionCapacity (program q r m).length s ∧
      EstimateWords (storedEstimateCap (program q r m).length B) s)
    (by
      intro s e hs he
      exact ⟨step_prefix_valid hs.1 he,
        step_entry_capacity hs.2.1 he,
        step_selection_capacity hs.2.1 hs.2.2.1 he,
        step_estimate_words hs.1 hs.2.2.1 hs.2.2.2 he⟩)
    (by
      refine ⟨initial_prefix_valid q r B m,?_,?_,?_⟩
      · simp [EntryCapacity,entryMass,cellPending,trialPending,initial]
      · constructor <;> simp [initial]
      · constructor <;> simp [initial])
  exact all.2.2.2

structure SnapshotWords (C : ℕ) (s : Config) : Prop where
  cellsRev : ∀ x∈s.cellsRev, x.2≤C
  pairSrc : ∀ x∈s.pairSrc, x.2≤C
  pairDst : ∀ x∈s.pairDst, x.2≤C
  trialsRev : ∀ x∈s.trialsRev, x.2≤C
  goodRev : ∀ x∈s.goodRev, x.2≤C
  badRev : ∀ x∈s.badRev, x.2≤C
  goodTable : ∀ x∈s.goodTable, x.2≤C
  badTable : ∀ x∈s.badTable, x.2≤C
  repairGood : ∀ x∈s.repairGood, x.2≤C
  repairBad : ∀ x∈s.repairBad, x.2≤C

set_option maxHeartbeats 800000 in
theorem step_snapshot_words {q r B m C : ℕ} {shape : Bool} {ext : External}
    {s : Config} {edge : Edge} (hcell : s.cellCalls≤C)
    (htrial : s.trialCalls≤C) (hcoefficient : s.coefficientCalls≤C)
    (hs : SnapshotWords C s) (he : step q r B m shape ext s=some edge) :
    SnapshotWords C edge.next := by
  rcases hs with ⟨hcells,hsrc,hdst,htrials,hgood,hbad,hgt,hbt,hrg,hrb⟩
  cases hp : s.pc <;> simp only [step,hp] at he
  all_goals try contradiction
  all_goals repeat' first
    | (simp only [localEdge,Option.some.injEq] at he; subst edge)
    | split at he
  all_goals constructor
  all_goals try assumption
  all_goals try dsimp only
  all_goals try simp_all only [List.forall_mem_cons,List.forall_mem_map,
    List.mem_nil_iff,false_implies,true_implies,forall_const,and_true,true_and,and_self,
    Nat.zero_le,Prod.fst,Prod.snd]
  all_goals first | assumption | (intros; trivial)

/-- +1 avoids needing P>0 in reusable local lemmas. This is still a word,
never a list capacity or amount of scratch allocated. -/
def storedCallCap (q P : ℕ) : ℕ := fullTreeCap q*(P+1)*(P+1)

theorem call_credit_words {q P : ℕ} {s : Config} (h : AllCallCredits q P s) :
    s.cellCalls≤storedCallCap q P ∧ s.trialCalls≤storedCallCap q P ∧
    s.coefficientCalls≤storedCallCap q P := by
  have hc : s.cellCalls≤fullTreeCap q := by have := h.cell; unfold CellCallCredit at this; omega
  have ht : s.trialCalls≤fullTreeCap q*P := by have := h.trial; unfold TrialCallCredit at this; omega
  have hk : s.coefficientCalls≤(fullTreeCap q*P)*P := by
    have := h.coefficient; unfold CoefficientCallCredit at this; omega
  unfold storedCallCap
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem reachable_snapshot_words {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} (h : Reachable q r B m shape ext s) :
    SnapshotWords (storedCallCap q (program q r m).length) s := by
  obtain ⟨totals,events,h⟩ := h
  have all := h.preserves
    (fun s => AllCallCredits q (program q r m).length s ∧
      SnapshotWords (storedCallCap q (program q r m).length) s)
    (by
      intro s e hs he
      have hc := call_credit_words hs.1
      exact ⟨⟨step_await_suspended hs.1.suspended he,
          step_cell_call_credit hs.1.suspended hs.1.cell he,
          step_trial_call_credit hs.1.cell hs.1.trial he,
          step_coefficient_call_credit hs.1.trial hs.1.coefficient he⟩,
        step_snapshot_words hc.1 hc.2.1 hc.2.2 hs.2 he⟩)
    (by
      constructor
      · constructor <;> simp [initial,AwaitSuspended,CellCallCredit,TrialCallCredit,
          CoefficientCallCredit,nativeRemaining,nativeControlCredit,basePending,
          cellPending,trialPending]
      · constructor <;> simp [initial])
  exact all.2

theorem step_lookup_bound {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} {edge : Edge} (hs : s.lookupRemaining≤m)
    (he : step q r B m shape ext s=some edge) : edge.next.lookupRemaining≤m := by
  cases hp : s.pc <;> simp only [step,hp] at he
  all_goals try contradiction
  all_goals repeat' first
    | (simp only [localEdge,Option.some.injEq] at he; subst edge)
    | split at he
  all_goals try simp_all [localEdge]
  all_goals omega

theorem reachable_lookup_bound {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} (h : Reachable q r B m shape ext s) : s.lookupRemaining≤m := by
  obtain ⟨totals,events,h⟩ := h
  exact h.preserves (fun s => s.lookupRemaining≤m)
    (fun _ _ => step_lookup_bound) (by simp [initial])

/-- Width bounds for the NEW broad profile, not an assertion of the original
sharper stateValueBound numerical inequality. -/
theorem storedEstimateCap_size (P B : ℕ) :
    (storedEstimateCap P B).size≤P+B.size+6 := by
  have hpow : (2^P).size≤P+1 := by
    apply Nat.size_le.mpr
    rw [pow_succ]
    have hpos : 0<2^P := pow_pos (by decide) _
    omega
  have hcap := cap_bit_length B
  have hmul := QecReliability.size_mul_bound (2^P) (4*B+1)
  unfold storedEstimateCap
  omega

theorem storedCallCap_size (q P : ℕ) :
    (storedCallCap q P).size≤q+2+2*(P+1).size := by
  have h0 := fullTreeCap_size q
  have h1 := QecReliability.size_mul_bound (fullTreeCap q) (P+1)
  have h2 := QecReliability.size_mul_bound (fullTreeCap q*(P+1)) (P+1)
  unfold storedCallCap
  omega

end QecReliability.OracleCost.WholeWrapperCandidate
