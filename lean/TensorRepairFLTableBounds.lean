import TensorRepairFLOutputBounds

/-! Closed table-size envelopes for the two accumulating repair folds. -/
set_option autoImplicit false
namespace QecReliability.TensorMachine.RepairFL
open FL FL.Lib FL.Lib.LinearRepairFL Trans.Wire
open Trans.Query.Bound Trans.BoundsQH
open Trans.Control (bodySig_cost bodySig_depth bodySig_msize)

variable (L : Lib) (i : Indices)

private theorem tableBound_suffix {D B : ℕ} {xs pre ys : RawTable}
    (h : TableBound D B xs) (he : xs = pre ++ ys) : TableBound D B ys := by
  intro x hx
  apply h x
  rw [he]
  exact List.mem_append.mpr (Or.inr hx)

private theorem suffix_length {α : Type} {xs pre ys : List α}
    (h : xs = pre ++ ys) : ys.length ≤ xs.length := by
  rw [h,List.length_append]
  omega

def tableFoldBudget (D B K N : ℕ) : ℕ := 10*(4*tableStepBudget D B K N+12)*(N+1)

theorem substFold_resources (D B K N : ℕ)
    (keys : KeyResources L i D K) (xs anchors : RawTable)
    (hx : TableBound D B xs) (ha : TableBound D B anchors)
    (hxn : xs.length ≤ N) (han : anchors.length ≤ N) :
    ResBound (foldrF (substStepF L i) i.substFold) (xs,anchors,[])
      (tableFoldBudget D B K N) := by
  let M := 4*tableStepBudget D B K N
  have sa := table_encoded_size ha
  have saN : (TTable.enc anchors).size ≤ (5*D+8*B+6)*N+1 :=
    sa.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) han])
  have hr : ∀ pre ys, xs = pre ++ ys →
      ((Ty.prod TTable TTable).enc (foldrDen (substStepF L i) ys (anchors,[]))).size ≤ M := by
    intro pre ys he
    rw [substFold_den]
    have hs := substituteR_bound (tableBound_suffix hx he) ha
    have ss := table_encoded_size hs
    have hn : (substituteR ys anchors).length ≤ N := by
      simpa only [substituteR,List.length_map] using (suffix_length he).trans hxn
    have ssN : (TTable.enc (substituteR ys anchors)).size ≤ (5*D+8*B+6)*N+1 :=
      ss.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) hn])
    simp only [Ty.enc_prod,Val.size_cons]
    dsimp [M,tableStepBudget]
    simp only [Nat.mul_add,Nat.mul_one] at *
    omega
  have hz : ((Ty.prod TTable TTable).enc (anchors,[])).size ≤ M := by
    have he := hr xs [] (List.append_nil xs).symm
    rw [foldrDen_nil] at he
    exact he
  have hc : ∀ pre x ys, xs = pre ++ x::ys →
      ResBound (substStepF L i) (x,foldrDen (substStepF L i) ys (anchors,[])) M := by
    intro pre x ys he
    have hy := tableBound_suffix hx he
    have hx' := hy x (by simp)
    have hys : TableBound D B ys := fun z hz => hy z (by simp [hz])
    have hsn : (substituteR ys anchors).length ≤ N := by
      simp only [substituteR,List.length_map]
      have := suffix_length he
      simp only [List.length_cons] at this
      omega
    rw [substFold_den]
    exact (substStep_resources L i D B K N keys anchors (substituteR ys anchors) x
      ha (substituteR_bound hys ha) hx' han hsn).mono (by dsimp [M]; omega)
  obtain ⟨fc,fd,fm⟩ := foldr_suffix_resources (substStepF L i) xs (anchors,[]) M M M hz hr hc
  have sx := table_encoded_size hx
  have sxN : (TTable.enc xs).size ≤ (5*D+8*B+6)*N+1 :=
    sx.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) hxn])
  have sxM : (TTable.enc xs).size ≤ M := by
    dsimp [M,tableStepBudget]
    simp only [Nat.mul_add,Nat.mul_one] at *
    omega
  have hcost : (M+12)*xs.length ≤ (M+12)*N := Nat.mul_le_mul_left _ hxn
  have hbase : M ≤ tableFoldBudget D B K N := by
    unfold tableFoldBudget
    change M ≤ 10*(M+12)*(N+1)
    nlinarith
  have sxM' : ((Ty.list TEntry).enc xs).size ≤ M := sxM
  simp only [ResBound,foldrF_cost,foldrF_depth,foldrF_msize]
  change _ ≤ 10*(M+12)*(N+1) ∧ _ ≤ 10*(M+12)*(N+1) ∧ _ ≤ 10*(M+12)*(N+1)
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith


set_option maxHeartbeats 1000000 in
theorem outFold_resources (D B K N : ℕ) (hB : 1 ≤ B)
    (keys : KeyResources L i D K) (xs data anchors : RawTable)
    (hx : TableBound D B xs) (hd : TableBound D B data) (ha : TableBound D B anchors)
    (hxn : xs.length ≤ N) (hdn : data.length ≤ N) (han : anchors.length ≤ N) :
    ResBound (foldrF (outStepF L i) i.outFold) (xs,(data,anchors),[])
      (tableFoldBudget D B K N) := by
  let M := 4*tableStepBudget D B K N
  have sd := table_encoded_size hd
  have sa := table_encoded_size ha
  have sdN : (TTable.enc data).size ≤ (5*D+8*B+6)*N+1 :=
    sd.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) hdn])
  have saN : (TTable.enc anchors).size ≤ (5*D+8*B+6)*N+1 :=
    sa.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) han])
  have bits (ys : RawTable) : ∀ z ∈ ys.map (fun x => pointR data anchors x.1), RB B z := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    exact pointR_bits hB hd ha x.1
  have hr : ∀ pre ys, xs = pre ++ ys →
      (TOutState.enc (foldrDen (outStepF L i) ys ((data,anchors),[]))).size ≤ M := by
    intro pre ys he
    rw [outFold_den]
    have ss := output_encoded_size (bits ys)
    have hn : (ys.map (fun x => pointR data anchors x.1)).length ≤ N := by
      simpa only [List.length_map] using (suffix_length he).trans hxn
    have ssN : (TOutput.enc (ys.map (fun x => pointR data anchors x.1))).size ≤ (8*B+4)*N+1 :=
      ss.trans (by nlinarith [Nat.mul_le_mul_left (8*B+4) hn])
    simp only [TOutState,Ty.enc_prod,Val.size_cons]
    dsimp [M,tableStepBudget]
    nlinarith
  have hz : (TOutState.enc ((data,anchors),[])).size ≤ M := by
    have he := hr xs [] (List.append_nil xs).symm
    rw [foldrDen_nil] at he
    exact he
  have hc : ∀ pre x ys, xs = pre ++ x::ys →
      ResBound (outStepF L i) (x,foldrDen (outStepF L i) ys ((data,anchors),[])) M := by
    intro pre x ys he
    have hy := tableBound_suffix hx he
    have hx' := hy x (by simp)
    have hsn : (ys.map (fun x => pointR data anchors x.1)).length ≤ N := by
      simp only [List.length_map]
      have := suffix_length he
      simp only [List.length_cons] at this
      omega
    rw [outFold_den]
    have hs := outStep_resources L i D B K N hB keys data anchors
      (ys.map (fun x => pointR data anchors x.1)) x hd ha (bits ys) hx' hdn han hsn
    have hM : 3*tableStepBudget D B K N ≤ M := by dsimp [M]; omega
    rcases hs with ⟨hsCost,hsDepth,hsSize⟩
    exact ⟨hsCost.trans hM,hsDepth.trans hM,hsSize.trans hM⟩
  obtain ⟨fc,fd,fm⟩ := foldr_suffix_resources (outStepF L i) xs ((data,anchors),[]) M M M hz hr hc
  have sx := table_encoded_size hx
  have sxN : (TTable.enc xs).size ≤ (5*D+8*B+6)*N+1 :=
    sx.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) hxn])
  have sxM : (TTable.enc xs).size ≤ M := by
    dsimp [M,tableStepBudget]
    simp only [Nat.mul_add,Nat.mul_one] at *
    omega
  have hcost : (M+12)*xs.length ≤ (M+12)*N := Nat.mul_le_mul_left _ hxn
  have sxM' : ((Ty.list TEntry).enc xs).size ≤ M := sxM
  simp only [ResBound,foldrF_cost,foldrF_depth,foldrF_msize]
  change _ ≤ 10*(M+12)*(N+1) ∧ _ ≤ 10*(M+12)*(N+1) ∧ _ ≤ 10*(M+12)*(N+1)
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith


theorem subst_resources (D B K N : ℕ)
    (keys : KeyResources L i D K) (xs anchors : RawTable)
    (hx : TableBound D B xs) (ha : TableBound D B anchors)
    (hxn : xs.length ≤ N) (han : anchors.length ≤ N) :
    ResBound (substF L i) (xs,anchors) (2*tableFoldBudget D B K N+100) := by
  have hf := substFold_resources L i D B K N keys xs anchors hx ha hxn han
  have sx := table_encoded_size hx
  have sa := table_encoded_size ha
  have sxN : (TTable.enc xs).size ≤ (5*D+8*B+6)*N+1 :=
    sx.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) hxn])
  have saN : (TTable.enc anchors).size ≤ (5*D+8*B+6)*N+1 :=
    sa.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) han])
  have hb : (5*D+8*B+6)*N+1 ≤ tableFoldBudget D B K N := by
    unfold tableFoldBudget tableStepBudget
    nlinarith
  simp only [ResBound,foldrF_cost,foldrF_depth,foldrF_msize] at hf
  rcases hf with ⟨fc,fd,fm⟩
  have sxN' : ((Ty.list TEntry).enc xs).size ≤ (5*D+8*B+6)*N+1 := sxN
  have saN' : ((Ty.list TEntry).enc anchors).size ≤ (5*D+8*B+6)*N+1 := saN
  have sempty : (TTable.enc ([] : RawTable)).size = 1 := rfl
  simp only [ResBound,substF,bodySig_cost,bodySig_depth,bodySig_msize,substBody,tm_simp,
    foldrF_cost,foldrF_depth,foldrF_msize,Ty.enc_prod,Ty.enc_list_nil,Val.size_cons,
    Val.size_nil,max_le_iff]
  omega

def repairBudget (D B K N : ℕ) : ℕ := 10*tableFoldBudget D B K N+1000

/-- Complete compiled rational repair, with polynomial resources in table
cardinality and binary operand sizes. The comparator budget K itself is the
fixed polynomial in key structure proved in key_resources. -/
theorem repair_resources (D B K N : ℕ) (hB : 1 ≤ B)
    (keys : KeyResources L i D K) (xs anchors : RawTable)
    (hx : TableBound D B xs) (ha : TableBound D B anchors)
    (hxn : xs.length ≤ N) (han : anchors.length ≤ N) :
    ResBound (repairF L i) (xs,anchors) (repairBudget D B K N) := by
  have hs := subst_resources L i D B K N keys xs anchors hx ha hxn han
  have hc := substituteR_bound hx ha
  have hcn : (substituteR xs anchors).length ≤ N := by
    simpa only [substituteR,List.length_map] using hxn
  have ho := outFold_resources L i D B K N hB keys xs (substituteR xs anchors) anchors
    hx hc ha hxn hcn han
  have sx := table_encoded_size hx
  have sa := table_encoded_size ha
  have sc := table_encoded_size hc
  have sxN : (TTable.enc xs).size ≤ (5*D+8*B+6)*N+1 :=
    sx.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) hxn])
  have saN : (TTable.enc anchors).size ≤ (5*D+8*B+6)*N+1 :=
    sa.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) han])
  have scN : (TTable.enc (substituteR xs anchors)).size ≤ (5*D+8*B+6)*N+1 :=
    sc.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) hcn])
  have hb : (5*D+8*B+6)*N+1 ≤ tableFoldBudget D B K N := by
    unfold tableFoldBudget tableStepBudget
    nlinarith
  rcases hs with ⟨scost,sdepth,sspace⟩
  simp only [ResBound,foldrF_cost,foldrF_depth,foldrF_msize] at ho
  rcases ho with ⟨ocost,odepth,ospace⟩
  have sxN' : ((Ty.list TEntry).enc xs).size ≤ (5*D+8*B+6)*N+1 := sxN
  have saN' : ((Ty.list TEntry).enc anchors).size ≤ (5*D+8*B+6)*N+1 := saN
  have scN' : ((Ty.list TEntry).enc (substituteR xs anchors)).size ≤ (5*D+8*B+6)*N+1 := scN
  have sempty : (TOutput.enc ([] : List RawRatio)).size = 1 := rfl
  simp only [ResBound,repairF,bodySig_cost,bodySig_depth,bodySig_msize,repairBody,tm_simp]
  repeat rw [substF_den]
  simp only [foldrF_cost,foldrF_depth,foldrF_msize,Ty.enc_prod,Ty.enc_list_nil,
    Val.size_cons,Val.size_nil,max_le_iff,repairBudget]
  omega

end QecReliability.TensorMachine.RepairFL
