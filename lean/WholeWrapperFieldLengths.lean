import WholeWrapperRequestBounds

/-! All 22 field cardinalities for the existing configFields,
including headers' source list lengths and every scratch copy. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate

theorem reachable_field_lengths {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} (h : Reachable q r B m shape ext s) :
    ∀ f∈configFields s, f.length≤stateListBound q r m := by
  have hl := reachable_list_capacities h
  have hi := reachable_request_invariant h
  dsimp only at hl
  rcases hl with ⟨hcode,hentry,htodo,hsorted,hleft,hright,hresult,
    hrepairGood,hrepairBad,houtputRev,houtput⟩
  unfold entryMass at hentry
  have h22 : 22≤stateListBound q r m := by unfold stateListBound; omega
  have h3 : 3*(program q r m).length≤stateListBound q r m := by
    unfold stateListBound; omega
  have hq : q≤stateListBound q r m := by unfold stateListBound; omega
  intro f hf
  unfold configFields at hf
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact h22
  · calc
      _ = s.code.length*3 := flatMap_const_length _ _ 3 (by intro op; cases op <;> rfl)
      _ ≤ stateListBound q r m := by omega
  · cases hk : s.request <;> exact (show 5≤_ by omega)
  · cases hk : s.request with
    | base side j rep => exact Nat.zero_le _
    | cell side j rep scale pre =>
        have hp : pre.length≤q := by
          have hv := hi.request
          rw [hk] at hv
          exact hv.2.2.2
        change (pre.map _).length≤_
        rw [List.length_map]
        omega
  · calc
      _ = s.cellsRev.length*2 := flatMap_const_length _ _ 2 (by intro x; rfl)
      _ ≤ stateListBound q r m := by omega
  · calc
      _ = s.pairSrc.length*2 := flatMap_const_length _ _ 2 (by intro x; rfl)
      _ ≤ stateListBound q r m := by omega
  · calc
      _ = s.pairDst.length*2 := flatMap_const_length _ _ 2 (by intro x; rfl)
      _ ≤ stateListBound q r m := by omega
  · calc
      _ = s.trialsRev.length*2 := flatMap_const_length _ _ 2 (by intro x; rfl)
      _ ≤ stateListBound q r m := by omega
  · exact htodo.trans (by omega)
  · exact hsorted.trans (by omega)
  · exact hleft.trans (by omega)
  · exact hright.trans (by omega)
  · exact hresult.trans (by omega)
  · calc
      _ = s.goodRev.length*2 := flatMap_const_length _ _ 2 (by intro x; rfl)
      _ ≤ stateListBound q r m := by omega
  · calc
      _ = s.badRev.length*2 := flatMap_const_length _ _ 2 (by intro x; rfl)
      _ ≤ stateListBound q r m := by omega
  · calc
      _ = s.goodTable.length*2 := flatMap_const_length _ _ 2 (by intro x; rfl)
      _ ≤ stateListBound q r m := by omega
  · calc
      _ = s.badTable.length*2 := flatMap_const_length _ _ 2 (by intro x; rfl)
      _ ≤ stateListBound q r m := by omega
  · calc
      _ = s.repairGood.length*2 := flatMap_const_length _ _ 2 (by intro x; rfl)
      _ ≤ stateListBound q r m := by omega
  · calc
      _ = s.repairBad.length*2 := flatMap_const_length _ _ 2 (by intro x; rfl)
      _ ≤ stateListBound q r m := by omega
  · exact (show 6≤stateListBound q r m by omega)
  · calc
      _ = s.outputRev.length*2 := flatMap_const_length _ _ 2 (by intro x; rfl)
      _ ≤ stateListBound q r m := by omega
  · calc
      _ = s.output.length*2 := flatMap_const_length _ _ 2 (by intro x; rfl)
      _ ≤ stateListBound q r m := by omega

/-- This is an actual reachable subset of the original OPEN representation
claim: every condition EXCEPT scalar word values is now separated out. -/
structure ReachableRepresentationSubset (q B Q L : ℕ) (s : Config) : Prop where
  fields : (configFields s).length=22
  fieldLengths : ∀ f∈configFields s, f.length≤L
  query : s.query.length≤Q
  «prefix» : PrefixTransitions.Valid q (4*B+1) s.prefixState

theorem reachable_representation_subset {q r B m Q : ℕ} {shape : Bool} {ext : External}
    {s : Config} (hfront : QueryBound q r m Q ext)
    (h : Reachable q r B m shape ext s) :
    ReachableRepresentationSubset q B Q (stateListBound q r m) s :=
  ⟨configFields_length s,reachable_field_lengths h,reachable_query_bound hfront h,
    reachable_prefix_valid h⟩

end QecReliability.OracleCost.WholeWrapperCandidate
