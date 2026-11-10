import TensorRepairFLBounds

/-! Composition of the compiled scans through cached anchor substitution and
all output slots. Bounds are polynomial in table cardinality, key structure,
and ratio bit length. -/
set_option autoImplicit false

namespace QecReliability.TensorMachine.RepairFL
open FL FL.Lib FL.Lib.LinearRepairFL Trans.Wire
open Trans.Query.Bound Trans.BoundsQH
open Trans.Control (bodySig_cost bodySig_depth bodySig_msize)

variable (L : Lib) (i : Indices)

theorem scanFunctionBudget_mono {D B K n m : ℕ} (h : n ≤ m) :
    scanFunctionBudget D B K n ≤ scanFunctionBudget D B K m := by
  unfold scanFunctionBudget scanBudget
  nlinarith [Nat.mul_le_mul_left (scanStepBudget D B K+12) h,
    Nat.mul_le_mul_left (2*(5*D+8*B+6)) h]

def tableStepBudget (D B K N : ℕ) : ℕ :=
  100*(scanFunctionBudget D B K N+comparisonBitsBudget B+(5*D+8*B+6)*(N+1)+1)

theorem point_resources (D B K N : ℕ) (hB : 1 ≤ B)
    (keys : KeyResources L i D K) (xs anchors : RawTable) (j : Key)
    (hx : TableBound D B xs) (ha : TableBound D B anchors)
    (hxn : xs.length ≤ N) (han : anchors.length ≤ N) (hj : mag TKey j ≤ D) :
    ResBound (pointF L i) (xs,anchors,j) (tableStepBudget D B K N) := by
  have hl := (lower_resources L i D B K hB keys xs j hx hj).mono (scanFunctionBudget_mono hxn)
  have hu := (upper_resources L i D B K hB keys anchors j ha hj).mono (scanFunctionBudget_mono han)
  have bl := lowerR_bits hB hx j
  have bu := upperR_bits hB ha j
  have hg := greater_resources i.greater (upperR anchors j) (lowerR xs j) B bu bl
  have sl := ratio_encoded_size B (lowerR xs j) bl
  have su := ratio_encoded_size B (upperR anchors j) bu
  have sx := table_encoded_size hx
  have sa := table_encoded_size ha
  have sj := key_encoded_size hj
  have sxN : (TTable.enc xs).size ≤ (5*D+8*B+6)*N+1 :=
    sx.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) hxn])
  have saN : (TTable.enc anchors).size ≤ (5*D+8*B+6)*N+1 :=
    sa.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) han])
  rcases hl with ⟨lc,ld,lm⟩
  rcases hu with ⟨uc,ud,um⟩
  rcases hg with ⟨gc,gd,gm⟩
  simp only [TRatio,Ty.enc_prod,Val.size_cons] at sl su
  simp only [ResBound,pointF,bodySig_cost,bodySig_depth,bodySig_msize,pointBody,tm_simp]
  repeat first | rw [upperF_den] | rw [lowerF_den]
  simp only [Ty.enc_prod,Val.size_cons,max_le_iff]
  unfold tableStepBudget
  simp only [Nat.mul_add,Nat.mul_one] at *
  omega

theorem substStep_resources (D B K N : ℕ)
    (keys : KeyResources L i D K) (anchors acc : RawTable) (x : RawEntry)
    (ha : TableBound D B anchors) (hc : TableBound D B acc) (hx : EntryBound D B x)
    (han : anchors.length ≤ N) (hcn : acc.length ≤ N) :
    ResBound (substStepF L i) (x,anchors,acc) (tableStepBudget D B K N) := by
  have hf := (anchor_resources L i D B K keys anchors x.1 x.2 ha hx.1 hx.2).mono
    (scanFunctionBudget_mono han)
  change ResBound (anchorF L i) (anchors,x) (scanFunctionBudget D B K N) at hf
  have hr := anchorR_bits ha x.1 x.2 hx.2
  have sr := ratio_encoded_size B (anchorR anchors x.1 x.2) hr
  have sx := entry_encoded_size hx
  have sj := key_encoded_size hx.1
  have sz := ratio_encoded_size B x.2 hx.2
  have sa := table_encoded_size ha
  have sc := table_encoded_size hc
  have saN : (TTable.enc anchors).size ≤ (5*D+8*B+6)*N+1 :=
    sa.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) han])
  have scN : (TTable.enc acc).size ≤ (5*D+8*B+6)*N+1 :=
    sc.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) hcn])
  have hnew : TableBound D B ((x.1,anchorR anchors x.1 x.2)::acc) := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨hx.1,hr⟩
    · exact hc z hz
  have snew : ((Ty.list TEntry).enc ((x.1,anchorR anchors x.1 x.2)::acc)).size ≤
      (5*D+8*B+6)*(acc.length+1)+1 := by
    simpa only [List.length_cons] using table_encoded_size hnew
  have snewN : ((Ty.list TEntry).enc ((x.1,anchorR anchors x.1 x.2)::acc)).size ≤
      (5*D+8*B+6)*(N+1)+1 := snew.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) hcn])
  have snewN' : (TTable.enc ((x.1,anchorR anchors x.1 x.2)::acc)).size ≤
      (5*D+8*B+6)*(N+1)+1 := snewN
  rcases hf with ⟨fc,fd,fm⟩
  simp only [TRatio,Ty.enc_prod,Val.size_cons] at sr sz
  simp only [ResBound,substStepF,bodySig_cost,bodySig_depth,bodySig_msize,substStepBody,tm_simp]
  repeat rw [anchorF_den]
  simp only [Ty.enc_prod,Ty.enc_list_cons,Val.size_cons,max_le_iff]
  unfold tableStepBudget
  simp only [Nat.mul_add,Nat.mul_one] at *
  omega

theorem output_encoded_size {B : ℕ} {xs : List RawRatio}
    (h : ∀ x ∈ xs, RB B x) : (TOutput.enc xs).size ≤ (8*B+4)*xs.length+1 := by
  induction xs with
  | nil => simp [TOutput,Ty.enc,Enc.list]
  | cons x xs ih =>
    have hx := ratio_encoded_size B x (h x (by simp))
    have ht := ih (fun y hy => h y (by simp [hy]))
    rw [Ty.sz_list_cons]
    simp only [List.length_cons]
    nlinarith


theorem outStep_resources (D B K N : ℕ) (hB : 1 ≤ B)
    (keys : KeyResources L i D K) (data anchors : RawTable) (acc : List RawRatio) (x : RawEntry)
    (hd : TableBound D B data) (ha : TableBound D B anchors)
    (hc : ∀ z ∈ acc, RB B z) (hx : EntryBound D B x)
    (hdn : data.length ≤ N) (han : anchors.length ≤ N) (hcn : acc.length ≤ N) :
    ResBound (outStepF L i) (x,(data,anchors),acc) (3*tableStepBudget D B K N) := by
  have hp := point_resources L i D B K N hB keys data anchors x.1 hd ha hdn han hx.1
  have br := pointR_bits hB hd ha x.1
  have sr := ratio_encoded_size B (pointR data anchors x.1) br
  have sk := key_encoded_size hx.1
  have sd := table_encoded_size hd
  have sa := table_encoded_size ha
  have sc := output_encoded_size hc
  have sdN : (TTable.enc data).size ≤ (5*D+8*B+6)*N+1 :=
    sd.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) hdn])
  have saN : (TTable.enc anchors).size ≤ (5*D+8*B+6)*N+1 :=
    sa.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) han])
  have scN : (TOutput.enc acc).size ≤ (8*B+4)*N+1 :=
    sc.trans (by nlinarith [Nat.mul_le_mul_left (8*B+4) hcn])
  rcases hp with ⟨pc,pd,pm⟩
  simp only [TRatio,Ty.enc_prod,Ty.enc_nat,Val.size_cons] at sr
  change ((Ty.list (.prod .nat .nat)).enc acc).size ≤ (8*B+4)*N+1 at scN
  have hscale : (8*B+4)*N ≤ (5*D+8*B+6)*N := Nat.mul_le_mul_right N (by omega)
  simp only [ResBound,outStepF,bodySig_cost,bodySig_depth,bodySig_msize,outStepBody,tm_simp]
  repeat rw [pointF_den]
  simp only [Ty.enc_prod,Ty.enc_list_cons,Ty.enc_list_cons_nat2,Val.size_cons,max_le_iff]
  unfold tableStepBudget at *
  simp only [Nat.mul_add,Nat.mul_one] at *
  omega

end QecReliability.TensorMachine.RepairFL
