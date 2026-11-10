import TensorRepairFLCountBounds

/-! Allocation and complete fold bounds for the compiled count-table builder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace QecReliability.TensorMachine.RepairFL
open FL FL.Lib FL.Lib.LinearRepairFL Trans.Wire
open Trans.Query.Bound Trans.BoundsQH
open Trans.Control (bodySig_cost bodySig_depth bodySig_msize)

variable (L : Lib) (wi : WrapperIndices)

theorem countList_tail_length (xs : List RawRatio) : xs.tail.length ≤ xs.length := by simp

private theorem countStep_allocation_scalar (D B N : ℕ) :
    2*((8*B+4)*N+1) + ((5*D+8*(2*B+1)+6)*(N+1)+1) +
      (5*D+1) + (16*B+20) + (8*B+2) + 100*(B+1) + 200 ≤
        1000*(D+B+1)*(N+1) := by
  nlinarith [Nat.zero_le (D*N), Nat.zero_le (B*N)]

set_option maxHeartbeats 1000000 in
theorem countsStep_resources (D B N : ℕ) (gs bs : List RawRatio) (acc : RawTable) (key : Key)
    (hg : CountListBound B gs) (hb : CountListBound B bs) (ha : TableBound D (2*B+1) acc)
    (hgn : gs.length ≤ N) (hbn : bs.length ≤ N) (han : acc.length ≤ N)
    (hk : mag TKey key ≤ D) :
    ResBound (countsStepF wi) ((gs,bs,acc),key) (countStepBudget D B N) := by
  have hgc := headCount_bits hg
  have hbc := headCount_bits hb
  have hr := rawCounts_bits hgc hbc
  have hc := counts_resources wi.countsRatio (gs.headD (0,0)).1 (bs.headD (0,0)).1 B hgc hbc
  have cc := countsStep_cost wi gs bs acc key
  have cd := countsStep_depth wi gs bs acc key
  have sg := output_encoded_size (countList_tail hg)
  have sb := output_encoded_size (countList_tail hb)
  have hgt := (countList_tail_length gs).trans hgn
  have hbt := (countList_tail_length bs).trans hbn
  have sgN : (TOutput.enc gs.tail).size ≤ (8*B+4)*N+1 :=
    sg.trans (by nlinarith [Nat.mul_le_mul_left (8*B+4) hgt])
  have sbN : (TOutput.enc bs.tail).size ≤ (8*B+4)*N+1 :=
    sb.trans (by nlinarith [Nat.mul_le_mul_left (8*B+4) hbt])
  have hnew : TableBound D (2*B+1)
      ((key,countsR (gs.headD (0,0)).1 (bs.headD (0,0)).1)::acc) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨hk,hr⟩
    · exact ha x hx
  have sn := table_encoded_size hnew
  have snN : (TTable.enc ((key,countsR (gs.headD (0,0)).1 (bs.headD (0,0)).1)::acc)).size ≤
      (5*D+8*(2*B+1)+6)*(N+1)+1 := by
    simp only [List.length_cons] at sn
    exact sn.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*(2*B+1)+6) han])
  have sr := ratio_encoded_size (2*B+1) (countsR (gs.headD (0,0)).1 (bs.headD (0,0)).1) hr
  have sk := key_encoded_size hk
  have sha := Enc.nat_size_le (gs.headD (0,0)).1
  have shb := Enc.nat_size_le (bs.headD (0,0)).1
  have hcap := countStep_allocation_scalar D B N
  simp only [TOutput,TTable] at sgN sbN snN
  rcases hc with ⟨fc,fd,fm⟩
  refine ⟨?_,?_,?_⟩
  · unfold countStepBudget
    nlinarith
  · unfold countStepBudget
    nlinarith
  · cases gs <;> cases bs <;>
      simp only [countsStepF_expanded,bodySig_msize,countsStepExpanded,tm_simp,countsF_den,
        List.headD_nil,List.headD_cons,List.tail_nil,List.tail_cons,
        Ty.enc_prod,Ty.enc_nat,Val.size_cons,max_le_iff] at *
    all_goals
      unfold countStepBudget
      simp only [TTable,TOutput] at *
      simp only [Nat.mul_add,Nat.mul_one] at *
      norm_num only [Nat.reduceAdd] at *
      (repeat' apply And.intro) <;> omega


theorem countsState_size (D B N : ℕ) (gs bs : List RawRatio) (acc : RawTable)
    (hg : CountListBound B gs) (hb : CountListBound B bs) (ha : TableBound D (2*B+1) acc)
    (hgn : gs.length ≤ N) (hbn : bs.length ≤ N) (han : acc.length ≤ N) :
    (TCountState.enc (gs,bs,acc)).size ≤ countStepBudget D B N := by
  have sg := output_encoded_size hg
  have sb := output_encoded_size hb
  have sa := table_encoded_size ha
  have sgN : ((Ty.list TRatio).enc gs).size ≤ (8*B+4)*N+1 :=
    sg.trans (by nlinarith [Nat.mul_le_mul_left (8*B+4) hgn])
  have sbN : ((Ty.list TRatio).enc bs).size ≤ (8*B+4)*N+1 :=
    sb.trans (by nlinarith [Nat.mul_le_mul_left (8*B+4) hbn])
  have saN : (TTable.enc acc).size ≤ (5*D+8*(2*B+1)+6)*N+1 :=
    sa.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*(2*B+1)+6) han])
  simp only [TCountState,Ty.enc_prod,Val.size_cons]
  unfold countStepBudget
  nlinarith

def countDataBudget (D B N : ℕ) : ℕ := 20*(countStepBudget D B N+20)*(N+1)+100

private theorem countData_scalar_bounds (H N : ℕ) :
    (H+12)*N+15*N+100≤20*(H+20)*(N+1)+100 ∧
    10*H+20*N+100≤20*(H+20)*(N+1)+100 := by
  constructor <;> nlinarith [Nat.zero_le (H*N)]

theorem countData_resources (D B N : ℕ) (keys : List Key) (gs bs : List RawRatio)
    (hk : ∀ key ∈ keys, mag TKey key ≤ D)
    (hg : CountListBound B gs) (hb : CountListBound B bs)
    (hkn : keys.length ≤ N) (hgn : gs.length ≤ N) (hbn : bs.length ≤ N) :
    ResBound (countDataF L wi) (keys,gs,bs) (countDataBudget D B N) := by
  let H := countStepBudget D B N
  let S : ℕ → TCountState.den → Prop := fun n s =>
    CountListBound B s.1 ∧ CountListBound B s.2.1 ∧ TableBound D (2*B+1) s.2.2 ∧
      s.1.length ≤ N ∧ s.2.1.length ≤ N ∧ s.2.2.length ≤ n
  have stateSize (n : ℕ) (hn : n ≤ N) (acc : TCountState.den) (hacc : S n acc) :
      (TCountState.enc acc).size ≤ H := by
    exact countsState_size D B N acc.1 acc.2.1 acc.2.2 hacc.1 hacc.2.1 hacc.2.2.1
      hacc.2.2.2.1 hacc.2.2.2.2.1 (hacc.2.2.2.2.2.trans hn)
  have hz : S 0 (gs,bs,[]) := ⟨hg,hb,by intro x hx; simp at hx,hgn,hbn,le_rfl⟩
  obtain ⟨hres,hsize,fc,fd,fm⟩ := foldl_bounds_idx (countsStepF wi) S H H H keys.length
    keys (gs,bs,[]) 0 (by simp) hz (stateSize 0 (Nat.zero_le _) _ hz) (by
      intro key hkey n hn acc hacc hsz
      rcases acc with ⟨gg,bb,out⟩
      rcases hacc with ⟨hgg,hbb,hout,hggn,hbbn,houtn⟩
      simp only [Prod.fst,Prod.snd] at hgg hbb hout hggn hbbn houtn
      have hs := countsStep_resources wi D B N gg bb out key hgg hbb hout hggn hbbn
        (houtn.trans (by omega)) (hk key hkey)
      have hnew : S (n+1) ((countsStepF wi).den ((gg,bb,out),key)) := by
        rw [countsStepF_den]
        refine ⟨countList_tail hgg,countList_tail hbb,?_,
          (countList_tail_length gg).trans hggn,(countList_tail_length bb).trans hbbn,?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨hk key hkey,rawCounts_bits (headCount_bits hgg) (headCount_bits hbb)⟩
          · exact hout x hx
        · change out.length+1 ≤ n+1
          omega
      exact ⟨hnew,stateSize (n+1) (by omega) _ hnew,hs.1,hs.2.1,hs.2.2⟩)
  have skmag := mag_list_le TKey keys D hk
  have sk := size_le_mag (.list TKey) keys
  have skH : ((Ty.list TKey).enc keys).size ≤ H := by
    dsimp [H,countStepBudget]
    nlinarith [Nat.mul_le_mul_left (D+1) hkn]
  have sz := stateSize 0 (Nat.zero_le _) _ hz
  have houtsz : (TTable.enc (foldlDen (countsStepF wi) (gs,bs,[]) keys).2.2).size ≤ H := by
    simp only [TCountState,Ty.enc_prod,Val.size_cons] at hsize
    omega
  have houtlen : (foldlDen (countsStepF wi) (gs,bs,[]) keys).2.2.length = keys.length := by
    rw [countsFold_den,countsFoldR]
    simp only [List.append_nil,List.length_reverse,countDataR_length]
  have hfc : (H+12)*keys.length ≤ (H+12)*N := Nat.mul_le_mul_left _ hkn
  have hcaps := countData_scalar_bounds H N
  have hnil : ((Ty.list TEntry).enc []).size = 1 := rfl
  simp only [TCountState,Ty.enc_prod,Val.size_cons,hnil] at sz
  simp only [countsStepF_expanded,countsStepExpanded] at fc fd fm houtsz houtlen
  simp only [TTable] at houtsz
  simp only [ResBound,countDataF,bodySig_cost,bodySig_depth,bodySig_msize,countDataBody,tm_simp,
    reverseF_cost,reverseF_depth,reverseF_msize,foldlF_cost,foldlF_depth,foldlF_msize,
    foldlF_den,Ty.enc_prod,Ty.enc_list_nil,Val.size_cons,Val.size_nil,max_le_iff]
  rw [houtlen]
  simp only [countDataBudget,hnil]
  dsimp only [H] at *
  norm_num only [Nat.reduceAdd]
  (repeat' apply And.intro) <;> omega

end QecReliability.TensorMachine.RepairFL
