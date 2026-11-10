import WholeWrapperRatioWords

/-! Closes the old representation invariant's entire
values component with a new explicit broader profile. It does NOT assert the
old sharper stateValueBound, full source refinement, or physical tape-space. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate
open RationalOutput

/-- Public mirrors make every data word in the old private helpers auditable.
The equality below is definitional, so this is not a replacement encoding. -/
def auditBoolWord (b : Bool) : ℕ := if b then 1 else 0

def auditPcWord : PC → ℕ
  | .fetch => 0 | .prefix => 1 | .compile => 2 | .invoke => 3 | .resume => 4
  | .reverseCells => 5 | .selectScan => 6 | .trialCommit => 7
  | .sortNext => 8 | .insertScan => 9 | .insertRestore => 10 | .medianLookup => 11
  | .reverseGood => 12 | .reverseBad => 13 | .endpointZero => 14 | .endpointOne => 15
  | .repair => 16 | .reverseOutput => 17 | .done => 18 | .fault => 19

def auditOpcodeWords : Opcode → List ℕ
  | .beginCoefficient side j => [0,auditBoolWord side,j]
  | .base rep => [1,rep,0]
  | .cell scale => [2,scale,0]
  | .select => [3,0,0] | .median => [4,0,0] | .store => [5,0,0] | .finish => [6,0,0]

def auditRequestWords : RequestKey → List ℕ
  | .base side j rep => [0,auditBoolWord side,j,rep,0]
  | .cell side j rep scale _ => [1,auditBoolWord side,j,rep,scale]

def auditRequestPrefix : RequestKey → List Bool
  | .base _ _ _ => []
  | .cell _ _ _ _ pre => pre

def auditEntryWords (xs : List Entry) : List ℕ := xs.flatMap (fun x => [x.1,x.2])
def auditRatioWords (xs : List Ratio) : List ℕ := xs.flatMap (fun x => [x.num,x.den])

theorem configFields_public (s : Config) : configFields s=
  [[auditPcWord s.pc,auditBoolWord s.good,s.coefficient,s.repetition,s.scale,
    auditBoolWord s.nonempty,(match s.returnTag with | .base => 0 | .prefix => 1),
    auditBoolWord s.reply,s.cellCalls,s.trialCalls,s.coefficientCalls,s.selected,
    s.selectIndex,s.scaleFactor,s.insertValue,s.lookupRemaining,s.repairIndex,
    s.pairVisits,s.ratioBuilds,s.orderComparisons,s.endpointTests,s.maxAccumulatorDen],
   s.code.flatMap auditOpcodeWords,auditRequestWords s.request,
   (auditRequestPrefix s.request).map auditBoolWord,
   auditEntryWords s.cellsRev,auditEntryWords s.pairSrc,auditEntryWords s.pairDst,
   auditEntryWords s.trialsRev,s.sortTodo,s.sorted,s.insertLeftRev,s.insertRight,s.insertResult,
   auditEntryWords s.goodRev,auditEntryWords s.badRev,auditEntryWords s.goodTable,
   auditEntryWords s.badTable,auditEntryWords s.repairGood,auditEntryWords s.repairBad,
   auditRatioWords [s.endpoint0,s.endpoint1,s.previous],
   auditRatioWords s.outputRev,auditRatioWords s.output] := by rfl

def broadValueBound (q r B m : ℕ) (ext : External) : ℕ :=
  let P := (program q r m).length
  20+q+r+(2*m+1)+2*P+2^P+storedEstimateCap P B+
    storedCallCap q P+storedRatioCap P B ext

theorem audit_bool_le (b : Bool) : auditBoolWord b≤1 := by
  cases b <;> decide

theorem audit_pc_le (pc : PC) : auditPcWord pc≤19 := by
  cases pc <;> decide

theorem audit_entry_words_bound {E C V : ℕ} (xs : List Entry)
    (hf : ∀ x∈xs, x.1≤E) (hs : ∀ x∈xs, x.2≤C) (he : E≤V) (hc : C≤V) :
    ∀ x∈auditEntryWords xs, x≤V := by
  intro x hx
  obtain ⟨entry,hentry,hx⟩ := List.mem_flatMap.mp hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl
  · exact (hf entry hentry).trans he
  · exact (hs entry hentry).trans hc

theorem audit_ratio_words_bound {M V : ℕ} (xs : List Ratio)
    (hden : ∀ x∈xs, x.den≤M) (hM : M≤V) : ∀ x∈auditRatioWords xs, x≤V := by
  intro x hx
  obtain ⟨entry,hentry,hx⟩ := List.mem_flatMap.mp hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl
  · exact (entry.num_le_den.trans (hden entry hentry)).trans hM
  · exact (hden entry hentry).trans hM

/-- EVERY word from the unchanged configFields, for every reachable state.
The only inputs are actual reachability and fixed semantic parameters. -/
theorem reachable_all_field_words {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} (h : Reachable q r B m shape ext s) :
    ∀ f∈configFields s, ∀ x∈f, x≤broadValueBound q r B m ext := by
  let P := (program q r m).length
  let V := broadValueBound q r B m ext
  have hpowpos : 0 < (2^((program q r m).length) : ℕ) := pow_pos (by decide) _
  have h20 : 20≤V := by dsimp only [V,broadValueBound,P]; omega
  have hq : q≤V := by dsimp only [V,broadValueBound,P]; omega
  have hr : r≤V := by dsimp only [V,broadValueBound,P]; omega
  have hR : 2*m+1≤V := by dsimp only [V,broadValueBound,P]; omega
  have hP : 2*P≤V := by dsimp only [V,broadValueBound,P]; omega
  have hpow : 2^P≤V := by dsimp only [V,broadValueBound,P]; omega
  have hE : storedEstimateCap P B≤V := by dsimp only [V,broadValueBound,P]; omega
  have hC : storedCallCap q P≤V := by dsimp only [V,broadValueBound,P]; omega
  have hM : storedRatioCap P B ext≤V := by dsimp only [V,broadValueBound,P]; omega
  have he := reachable_estimate_words h
  have hc := reachable_snapshot_words h
  have hd := reachable_ratio_words h
  have hi := reachable_request_invariant h
  have hcall := call_credit_words (reachable_call_credits h)
  have hsel := reachable_selection_capacity h
  have hrepair := reachable_repair_counter_capacity h
  have hlookup := reachable_lookup_bound h
  have hbool : ∀ b, auditBoolWord b≤V := fun b => (audit_bool_le b).trans (by omega)
  have hpc : auditPcWord s.pc≤V := (audit_pc_le s.pc).trans (by omega)
  have htag : (match s.returnTag with | .base => 0 | .prefix => 1)≤V := by
    cases s.returnTag <;> dsimp only <;> omega
  have hcoeff : s.coefficient≤V := hi.coefficient.trans hr
  have hrep : s.repetition≤V := by have := hi.repetition; omega
  have hscale : s.scale≤V := hi.scale.trans hq
  have hcell : s.cellCalls≤V := hcall.1.trans hC
  have htrial : s.trialCalls≤V := hcall.2.1.trans hC
  have hcoefficient : s.coefficientCalls≤V := hcall.2.2.trans hC
  have hselected : s.selected≤V := he.selected.trans hE
  have hselectIndex : s.selectIndex≤V := by have := hsel.index; omega
  have hscaleFactor : s.scaleFactor≤V := by
    rw [hsel.factor]
    exact (Nat.pow_le_pow_right (by decide) hsel.index).trans hpow
  have hinsert : s.insertValue≤V := he.insertValue.trans hE
  have hlookup' : s.lookupRemaining≤V := by omega
  have hrepairIndex : s.repairIndex≤P := by have := hrepair.credit; omega
  have hri : s.repairIndex≤V := by omega
  have hpv : s.pairVisits≤V := by rw [hrepair.visits]; exact hri
  have hrb : s.ratioBuilds≤V := hrepair.ratios.trans hri
  have hoc : s.orderComparisons≤V := by have := hrepair.comparisons; omega
  have het : s.endpointTests≤V := by have := hrepair.tests; omega
  have hmax : s.maxAccumulatorDen≤V := hd.maximum.trans hM
  intro f hf
  rw [configFields_public] at hf
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · intro x hx
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | assumption | exact hbool _
  · intro x hx
    obtain ⟨op,hop,hx⟩ := List.mem_flatMap.mp hx
    have hbound := hi.code op hop
    cases op <;> simp only [auditOpcodeWords,List.mem_cons,List.mem_nil_iff,or_false] at hx
    all_goals simp only [OpcodeBound] at hbound
    all_goals rcases hx with rfl | rfl | rfl
    all_goals first | exact hbool _ | omega
  · intro x hx
    have hv := hi.request
    cases hk : s.request <;> simp only [hk,auditRequestWords,List.mem_cons,List.mem_nil_iff,or_false] at hx
    all_goals simp only [hk,ValidKey] at hv
    all_goals rcases hx with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hbool _ | omega
  · intro x hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
    exact hbool b
  · exact audit_entry_words_bound _ he.cellsRev hc.cellsRev hE hC
  · exact audit_entry_words_bound _ he.pairSrc hc.pairSrc hE hC
  · exact audit_entry_words_bound _ he.pairDst hc.pairDst hE hC
  · exact audit_entry_words_bound _ he.trialsRev hc.trialsRev hE hC
  · exact fun x hx => (he.sortTodo x hx).trans hE
  · exact fun x hx => (he.sorted x hx).trans hE
  · exact fun x hx => (he.insertLeftRev x hx).trans hE
  · exact fun x hx => (he.insertRight x hx).trans hE
  · exact fun x hx => (he.insertResult x hx).trans hE
  · exact audit_entry_words_bound _ he.goodRev hc.goodRev hE hC
  · exact audit_entry_words_bound _ he.badRev hc.badRev hE hC
  · exact audit_entry_words_bound _ he.goodTable hc.goodTable hE hC
  · exact audit_entry_words_bound _ he.badTable hc.badTable hE hC
  · exact audit_entry_words_bound _ he.repairGood hc.repairGood hE hC
  · exact audit_entry_words_bound _ he.repairBad hc.repairBad hE hC
  · apply audit_ratio_words_bound _ _ hM
    intro x hx
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hd.endpoint0
    · exact hd.endpoint1
    · exact hd.previous
  · exact audit_ratio_words_bound _ hd.outputRev hM
  · exact audit_ratio_words_bound _ hd.output hM

/-- The COMPLETE reachable represented-state invariant for the broader
polynomial-width profile. The frontend premise is a typed query-buffer bound,
not a final resource contract, and the existing concrete encoder discharges it. -/
theorem reachable_full_representation {q r B m Q : ℕ} {shape : Bool} {ext : External}
    {s : Config} (hfront : QueryBound q r m Q ext)
    (h : Reachable q r B m shape ext s) :
    RepresentationInvariant q B Q 22 (stateListBound q r m)
      (broadValueBound q r B m ext) s :=
  ⟨by simp,reachable_field_lengths h,reachable_all_field_words h,
    reachable_query_bound hfront h,reachable_prefix_valid h⟩

theorem reachable_representedBits_bound {q r B m Q : ℕ} {shape : Bool} {ext : External}
    {s : Config} (hfront : QueryBound q r m Q ext)
    (h : Reachable q r B m shape ext s) :
    (representedBits s).length≤
      2*(22:ℕ).size+1+22*(2*(stateListBound q r m).size+1+
        stateListBound q r m*(2*(broadValueBound q r B m ext).size+1))+
      (2*Q.size+1)+Q+PrefixTransitions.configBitBound q (4*B+1) :=
  representedBits_bound _ _ _ _ _ _ _ (reachable_full_representation hfront h)

open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

/-- Concrete source-facing endpoint: the query buffer premise is DISCHARGED
by the unchanged padded serializer, not assumed as an opaque resource bound. -/
theorem reachable_concrete_full_representation {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (service : SATService)
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) (D g : ℕ) (shape : Bool) (ext : External)
    (hboundary : BoundaryCorrect rows C H K service m ω D ext)
    (hg : ∀ scale seed, (K.program scale seed).gates≤g)
    {s : Config} (h : Reachable (keySize n r) r B m shape ext s) :
    RepresentationInvariant (keySize n r) B (QuantumService.engineInputBound rows C D g)
      22 (stateListBound (keySize n r) r m)
      (broadValueBound (keySize n r) r B m ext) s :=
  reachable_full_representation
    (concrete_query_bound rows C H K service m ω D g ext hboundary hg) h

end QecReliability.OracleCost.WholeWrapperCandidate
