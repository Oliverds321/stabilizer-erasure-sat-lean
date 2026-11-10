import TensorRepairFLScanBounds

/-! Resource composition for the installed rational scans. Parameters D and B
bound key magnitude and ratio component bit length respectively; Q counts
stored entries. All envelopes below bound the real FL measures. -/
set_option autoImplicit false

namespace QecReliability.TensorMachine.RepairFL
open FL FL.Lib FL.Lib.LinearRepairFL Trans.Wire
open Trans.Query.Bound Trans.BoundsQH
open Trans.Control (bodySig_cost bodySig_depth bodySig_msize)

variable (L : Lib) (i : Indices)

def KeyResources (D K : ℕ) : Prop := ∀ a b : Key,
  mag TKey a ≤ D → mag TKey b ≤ D →
  ResBound (keyLeF L i) (a,b) K ∧ ResBound (keyEqF L i) (a,b) K

theorem state_encoded_size {D B : ℕ} {j : Key} {z : RawRatio}
    (hj : mag TKey j ≤ D) (hz : RB B z) :
    (TScanState.enc (j,z)).size ≤ 5*D+8*B+5 := by
  have hk := key_encoded_size hj
  have hr := ratio_encoded_size B z hz
  simp only [TScanState,TRatio,Ty.enc_prod,Ty.enc_nat,Val.size_cons] at hr ⊢
  omega

def scanBudget (D B K Q : ℕ) : ℕ :=
  (scanStepBudget D B K+12)*Q + 2*(5*D+8*B+6)*Q + 2*scanStepBudget D B K+100

theorem lowerFold_resources (D B K : ℕ) (hB : 1 ≤ B)
    (keys : KeyResources L i D K) (xs : RawTable) (j : Key)
    (hx : TableBound D B xs) (hj : mag TKey j ≤ D) :
    ResBound (foldrF (lowerStepF L i) i.lowerFold) (xs,j,(1,1))
      (scanBudget D B K xs.length) := by
  have hz : RB B (1,1) := by simp only [RB,Nat.size_zero,Nat.size_one]; omega
  have hzsize := state_encoded_size hj hz
  let H := scanStepBudget D B K
  have hh : 5*D+8*B+5 ≤ H := by dsimp [H,scanStepBudget]; omega
  obtain ⟨_,_,hc,hd,hm⟩ := foldr_bounds (lowerStepF L i)
    (fun s => s.1 = j ∧ RB B s.2) H H H xs (j,(1,1)) ⟨rfl,hz⟩
    (hzsize.trans hh) (by
      intro x hmem acc hacc hsz
      rcases acc with ⟨k,z⟩
      rcases hacc with ⟨hkj,hz⟩
      simp only [Prod.fst,Prod.snd] at hkj hz
      subst k
      have he := hx x hmem
      have hkey := (keys x.1 j (he.1) hj).1
      have hs := lowerStep_resources L i D B K x.1 j x.2 z he.1 hj he.2 hz hkey
      have hr : RB B (if keyLe x.1 j then lesserR x.2 z else z) := by
        split <;> first | exact lesserR_RB he.2 hz | exact hz
      refine ⟨?_,?_,hs.1,hs.2.1,hs.2.2⟩
      · rw [lowerStepF_den]
        exact ⟨rfl,hr⟩
      · rw [lowerStepF_den]
        exact (state_encoded_size hj hr).trans hh)
  have ht := table_encoded_size hx
  simp only [TTable] at ht
  simp only [ResBound,foldrF_cost,foldrF_depth,foldrF_msize]
  dsimp [H] at hc hd hm
  unfold scanBudget
  simp only [Nat.mul_assoc]
  constructor
  · omega
  constructor
  · have hp : xs.length ≤ (scanStepBudget D B K+12)*xs.length := by
      nlinarith [Nat.zero_le (scanStepBudget D B K)]
    omega
  · omega

theorem upperFold_resources (D B K : ℕ) (hB : 1 ≤ B)
    (keys : KeyResources L i D K) (xs : RawTable) (j : Key)
    (hx : TableBound D B xs) (hj : mag TKey j ≤ D) :
    ResBound (foldrF (upperStepF L i) i.upperFold) (xs,j,(0,1))
      (scanBudget D B K xs.length) := by
  have hz : RB B (0,1) := by simp only [RB,Nat.size_zero,Nat.size_one]; omega
  have hzsize := state_encoded_size hj hz
  let H := scanStepBudget D B K
  have hh : 5*D+8*B+5 ≤ H := by dsimp [H,scanStepBudget]; omega
  obtain ⟨_,_,hc,hd,hm⟩ := foldr_bounds (upperStepF L i)
    (fun s => s.1 = j ∧ RB B s.2) H H H xs (j,(0,1)) ⟨rfl,hz⟩
    (hzsize.trans hh) (by
      intro x hmem acc hacc hsz
      rcases acc with ⟨k,z⟩
      rcases hacc with ⟨hkj,hz⟩
      simp only [Prod.fst,Prod.snd] at hkj hz
      subst k
      have he := hx x hmem
      have hkey := (keys j x.1 hj (he.1)).1
      have hs := upperStep_resources L i D B K x.1 j x.2 z he.1 hj he.2 hz hkey
      have hr : RB B (if keyLe j x.1 then greaterR x.2 z else z) := by
        split <;> first | exact greaterR_RB he.2 hz | exact hz
      refine ⟨?_,?_,hs.1,hs.2.1,hs.2.2⟩
      · rw [upperStepF_den]
        exact ⟨rfl,hr⟩
      · rw [upperStepF_den]
        exact (state_encoded_size hj hr).trans hh)
  have ht := table_encoded_size hx
  simp only [TTable] at ht
  simp only [ResBound,foldrF_cost,foldrF_depth,foldrF_msize]
  dsimp [H] at hc hd hm
  unfold scanBudget
  simp only [Nat.mul_assoc]
  constructor
  · omega
  constructor
  · have hp : xs.length ≤ (scanStepBudget D B K+12)*xs.length := by
      nlinarith [Nat.zero_le (scanStepBudget D B K)]
    omega
  · omega


theorem anchorFold_resources (D B K : ℕ)
    (keys : KeyResources L i D K) (xs : RawTable) (j : Key) (z : RawRatio)
    (hx : TableBound D B xs) (hj : mag TKey j ≤ D) (hz : RB B z) :
    ResBound (foldrF (anchorStepF L i) i.anchorFold) (xs,j,z)
      (scanBudget D B K xs.length) := by
  have hzsize := state_encoded_size hj hz
  let H := scanStepBudget D B K
  have hh : 5*D+8*B+5 ≤ H := by dsimp [H,scanStepBudget]; omega
  obtain ⟨_,_,hc,hd,hm⟩ := foldr_bounds (anchorStepF L i)
    (fun s => s.1 = j ∧ RB B s.2) H H H xs (j,z) ⟨rfl,hz⟩
    (hzsize.trans hh) (by
      intro x hmem acc hacc hsz
      rcases acc with ⟨k,w⟩
      rcases hacc with ⟨hkj,hw⟩
      simp only [Prod.fst,Prod.snd] at hkj hw
      subst k
      have he := hx x hmem
      have hkey := (keys x.1 j he.1 hj).2
      have hs := anchorStep_resources L i D B K x.1 j x.2 w he.1 hj he.2 hw hkey
      have hr : RB B (if keyEq x.1 j then x.2 else w) := by
        split
        · exact he.2
        · exact hw
      refine ⟨?_,?_,hs.1,hs.2.1,hs.2.2⟩
      · rw [anchorStepF_den]
        exact ⟨rfl,hr⟩
      · rw [anchorStepF_den]
        exact (state_encoded_size hj hr).trans hh)
  have ht := table_encoded_size hx
  simp only [TTable] at ht
  simp only [ResBound,foldrF_cost,foldrF_depth,foldrF_msize]
  dsimp [H] at hc hd hm
  unfold scanBudget
  simp only [Nat.mul_assoc]
  constructor
  · omega
  constructor
  · have hp : xs.length ≤ (scanStepBudget D B K+12)*xs.length := by
      nlinarith [Nat.zero_le (scanStepBudget D B K)]
    omega
  · omega

def scanFunctionBudget (D B K Q : ℕ) : ℕ := 4*scanBudget D B K Q+100

theorem lower_resources (D B K : ℕ) (hB : 1 ≤ B)
    (keys : KeyResources L i D K) (xs : RawTable) (j : Key)
    (hx : TableBound D B xs) (hj : mag TKey j ≤ D) :
    ResBound (lowerF L i) (xs,j) (scanFunctionBudget D B K xs.length) := by
  have hf := lowerFold_resources L i D B K hB keys xs j hx hj
  have ht := table_encoded_size hx
  simp only [TTable] at ht
  have hk := key_encoded_size hj
  simp only [ResBound,foldrF_cost,foldrF_depth,foldrF_msize] at hf
  rcases hf with ⟨hc,hd,hm⟩
  simp only [ResBound,lowerF,bodySig_cost,bodySig_depth,bodySig_msize,lowerBody,
    tm_simp,foldrF_cost,foldrF_depth,foldrF_msize,Ty.enc_prod,Ty.enc_nat,
    Val.size_cons,Enc.nat_one_size,Enc.nat_zero_size,max_le_iff]
  unfold scanFunctionBudget scanBudget scanStepBudget at *
  simp only [Nat.mul_assoc] at *
  omega

theorem upper_resources (D B K : ℕ) (hB : 1 ≤ B)
    (keys : KeyResources L i D K) (xs : RawTable) (j : Key)
    (hx : TableBound D B xs) (hj : mag TKey j ≤ D) :
    ResBound (upperF L i) (xs,j) (scanFunctionBudget D B K xs.length) := by
  have hf := upperFold_resources L i D B K hB keys xs j hx hj
  have ht := table_encoded_size hx
  simp only [TTable] at ht
  have hk := key_encoded_size hj
  simp only [ResBound,foldrF_cost,foldrF_depth,foldrF_msize] at hf
  rcases hf with ⟨hc,hd,hm⟩
  simp only [ResBound,upperF,bodySig_cost,bodySig_depth,bodySig_msize,upperBody,
    tm_simp,foldrF_cost,foldrF_depth,foldrF_msize,Ty.enc_prod,Ty.enc_nat,
    Val.size_cons,Enc.nat_one_size,Enc.nat_zero_size,max_le_iff]
  unfold scanFunctionBudget scanBudget scanStepBudget at *
  simp only [Nat.mul_assoc] at *
  omega

theorem anchor_resources (D B K : ℕ)
    (keys : KeyResources L i D K) (xs : RawTable) (j : Key) (z : RawRatio)
    (hx : TableBound D B xs) (hj : mag TKey j ≤ D) (hz : RB B z) :
    ResBound (anchorF L i) (xs,j,z) (scanFunctionBudget D B K xs.length) := by
  have hf := anchorFold_resources L i D B K keys xs j z hx hj hz
  simp only [ResBound,foldrF_cost,foldrF_depth,foldrF_msize] at hf
  rcases hf with ⟨hc,hd,hm⟩
  simp only [ResBound,anchorF,bodySig_cost,bodySig_depth,bodySig_msize,anchorBody,
    tm_simp,foldrF_cost,foldrF_depth,foldrF_msize,max_le_iff]
  unfold scanFunctionBudget
  omega

end QecReliability.TensorMachine.RepairFL
