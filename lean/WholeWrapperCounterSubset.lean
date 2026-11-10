import WholeWrapperFieldLengths

/-! Actual-step conservation of selection and repair counters.
This does not claim cell/trial/coefficient call-counter bounds. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate

structure SelectionCapacity (P : ℕ) (s : Config) : Prop where
  index : s.selectIndex≤P
  active : s.pc=.selectScan → s.selectIndex+s.pairSrc.length≤P
  factor : s.scaleFactor=2^s.selectIndex

theorem step_selection_capacity {q r B m P : ℕ} {shape : Bool} {ext : External}
    {s : Config} {edge : Edge} (hentries : EntryCapacity P s)
    (hs : SelectionCapacity P s) (he : step q r B m shape ext s=some edge) :
    SelectionCapacity P edge.next := by
  rcases hs with ⟨hindex,hactive,hfactor⟩
  unfold EntryCapacity entryMass at hentries
  cases hp : s.pc <;> simp only [step,hp] at he
  all_goals try contradiction
  all_goals repeat' first
    | (simp only [localEdge,Option.some.injEq] at he; subst edge)
    | split at he
  all_goals try simp_all [localEdge]
  all_goals constructor <;> try simp_all [pow_succ,Nat.mul_comm]
  all_goals omega

theorem reachable_selection_capacity {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} (h : Reachable q r B m shape ext s) :
    SelectionCapacity (program q r m).length s := by
  obtain ⟨totals,events,h⟩ := h
  have both := h.preserves
    (fun s => EntryCapacity (program q r m).length s ∧
      SelectionCapacity (program q r m).length s)
    (by intro s e hs he; exact ⟨step_entry_capacity hs.1 he,
        step_selection_capacity hs.1 hs.2 he⟩)
    (by constructor
        · simp [EntryCapacity,entryMass,cellPending,trialPending,initial]
        · constructor <;> simp [initial])
  exact both.2

/-- Even this deliberately loose exponent is a polynomial-size WORD: P
counts opcodes, not queries. A sharper schedule theorem can replace P by q+1. -/
theorem reachable_scaleFactor_size {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} (h : Reachable q r B m shape ext s) :
    s.scaleFactor.size≤(program q r m).length+1 := by
  have hs := reachable_selection_capacity h
  rw [hs.factor]
  apply Nat.size_le.mpr
  have hp : 2^s.selectIndex≤2^(program q r m).length :=
    Nat.pow_le_pow_right (by decide) hs.index
  have hpos : 0<2^(program q r m).length := pow_pos (by decide) _
  rw [pow_succ]
  omega

structure RepairCounterCapacity (P : ℕ) (s : Config) : Prop where
  credit : s.repairIndex+s.repairGood.length≤P
  visits : s.pairVisits=s.repairIndex
  ratios : s.ratioBuilds≤s.repairIndex
  comparisons : s.orderComparisons≤2*s.repairIndex
  tests : s.endpointTests≤2*s.repairIndex
  early : s.pc≠.repair → s.pc≠.reverseOutput → s.pc≠.done → s.pc≠.fault →
    s.repairIndex=0

theorem step_repair_counter_capacity {q r B m P : ℕ} {shape : Bool} {ext : External}
    {s : Config} {edge : Edge} (hentries : EntryCapacity P s)
    (hs : RepairCounterCapacity P s) (he : step q r B m shape ext s=some edge) :
    RepairCounterCapacity P edge.next := by
  rcases hs with ⟨hcredit,hvisits,hratios,hcomparisons,htests,hearly⟩
  unfold EntryCapacity entryMass at hentries
  cases hp : s.pc <;> simp only [step,hp] at he
  all_goals try contradiction
  all_goals repeat' first
    | (simp only [localEdge,Option.some.injEq] at he; subst edge)
    | split at he
  all_goals try simp_all [localEdge]
  all_goals constructor <;> try simp_all
  all_goals try split_ifs
  all_goals omega

theorem reachable_repair_counter_capacity {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} (h : Reachable q r B m shape ext s) :
    RepairCounterCapacity (program q r m).length s := by
  obtain ⟨totals,events,h⟩ := h
  have both := h.preserves
    (fun s => EntryCapacity (program q r m).length s ∧
      RepairCounterCapacity (program q r m).length s)
    (by intro s e hs he; exact ⟨step_entry_capacity hs.1 he,
        step_repair_counter_capacity hs.1 hs.2 he⟩)
    (by constructor
        · simp [EntryCapacity,entryMass,cellPending,trialPending,initial]
        · constructor <;> simp [initial])
  exact both.2

/-- Nat.size applied to bounds PROVED from actual steps, not supplied desired
counter bounds. The repair report counters remain logarithmic in code size. -/
theorem reachable_repair_counter_sizes {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} (h : Reachable q r B m shape ext s) :
    let P := (program q r m).length
    s.repairIndex.size≤P.size ∧ s.pairVisits.size≤P.size ∧
    s.ratioBuilds.size≤P.size ∧ s.orderComparisons.size≤(2*P).size ∧
    s.endpointTests.size≤(2*P).size := by
  have hs := reachable_repair_counter_capacity h
  have hi : s.repairIndex≤(program q r m).length := by have := hs.credit; omega
  exact ⟨Nat.size_le_size hi,Nat.size_le_size (by rw [hs.visits]; exact hi),
    Nat.size_le_size (hs.ratios.trans hi),
    Nat.size_le_size (hs.comparisons.trans (Nat.mul_le_mul_left 2 hi)),
    Nat.size_le_size (hs.tests.trans (Nat.mul_le_mul_left 2 hi))⟩

/-- The original prefix invariant bounds count/cap WORDS by the cap, not
stack cardinality by cap. Combined with cap_bit_length this is logarithmic B. -/
theorem reachable_native_return_size {q r B m count : ℕ} {shape : Bool} {ext : External}
    {s : Config} (h : Reachable q r B m shape ext s)
    (hc : s.prefixState.control=.ret count) : count.size≤B.size+5 := by
  obtain ⟨depth,budget,hcontrol,hstack⟩ := reachable_prefix_valid h
  rw [hc] at hcontrol
  change count=budget at hcontrol
  have hcount : count≤4*B+1 := by rw [hcontrol]; exact hstack.bounds.2.1
  exact (Nat.size_le_size hcount).trans (cap_bit_length B)

end QecReliability.OracleCost.WholeWrapperCandidate
