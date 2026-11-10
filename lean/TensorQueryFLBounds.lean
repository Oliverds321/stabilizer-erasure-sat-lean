import TensorQueryFLValidity
import Trans.BoundsQH.Compile
import Trans.BoundsQH.HTrans

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Polynomial bounds for the actual multiclass query transcription. The
polynomial is in structural magnitude, including the total number of causes.
It does not treat the binary encoding of an unbounded degree as unary input. -/
namespace QecReliability.TensorQuery.FLCompiler
open FL FL.Lib FL.Tm Trans.Query Trans.Query.Bound Trans.BoundsQH

theorem natList_mag (xs : List ℕ) : mag (.list .nat) xs = xs.sum+xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons r xs ih =>
    change r+1+mag (.list .nat) xs = (r+xs.sum)+(xs.length+1)+1
    rw [ih]
    omega

theorem scan_full (ds js : List ℕ) (off : ℕ) (acc : List Item) :
    ds.foldl scanStep (off,js,acc) =
      (off+ds.sum,js.drop ds.length,(items ds js off).reverse++acc) := by
  induction ds generalizing js off acc with
  | nil => simp [items]
  | cons r ds ih =>
    simp only [List.foldl_cons,scanStep,ih,items,List.reverse_cons,List.append_assoc,
      List.singleton_append,List.sum_cons,List.length_cons,List.drop_drop,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem items_mag (ds js : List ℕ) (off : ℕ) :
    mag (.list TItem) (items ds js off) ≤
      (ds.length+1)*(off+ds.sum+mag (.list .nat) js+4) := by
  induction ds generalizing off js with
  | nil =>
    change 1 ≤ (0+1)*(off+0+mag (.list .nat) js+4)
    omega
  | cons r ds ih =>
    have ht := ih (js.drop 1) (off+r)
    have hd := mag_drop .nat js 1
    have hj := mag_getD .nat js 0 0
    simp only [mag_nat,Nat.add_zero,← List.headD_eq_getD] at hj
    change (r+(off+js.headD 0+1)+1)+1+
      mag (.list TItem) (items ds (js.drop 1) (off+r)) ≤
        (ds.length+1+1)*(off+(r+ds.sum)+mag (.list .nat) js+4)
    let M := off+r+ds.sum+mag (.list .nat) js+4
    have ht' : mag (.list TItem) (items ds (js.drop 1) (off+r)) ≤ (ds.length+1)*M :=
      ht.trans (Nat.mul_le_mul_left (ds.length+1) (by dsimp [M]; omega))
    have hh : r+(off+js.headD 0+1)+1+1 ≤ M := by dsimp [M]; omega
    calc
      _ ≤ M+(ds.length+1)*M := Nat.add_le_add hh ht'
      _ = _ := by dsimp [M]; ring

theorem scan_result_mag (ds : List ℕ) (s : TScan.den) :
    mag TScan (ds.foldl scanStep s) ≤
      G 1 10 (mag (.prod TScan (.list .nat)) (s,ds)) := by
  rcases s with ⟨off,js,acc⟩
  rw [scan_full]
  have hi := items_mag ds js off
  have hd := mag_drop .nat js ds.length
  have ha := mag_append_le TItem (items ds js off).reverse acc
  rw [mag_reverse] at ha
  have hl := mag_list_len .nat ds
  have hn := natList_mag ds
  simp only [TScan,mag_prod,mag_nat]
  change _ ≤ G 1 10 (off+(mag (.list .nat) js+mag (.list TItem) acc+1)+1+
    mag (.list .nat) ds+1)
  rw [G,Function.iterate_one]
  unfold B0
  nlinarith

@[polyB] theorem scanStep_P (x : Ix) (i : Indices) : PolyB (scanStepF x i) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP,scanStepBody,polyB])

@[polyB] theorem scanFold_P (x : Ix) (i : Indices) :
    PolyB (foldlF (scanStepF x i) i.scanFold) := by
  apply foldl_polyB_pre _ _ (scanStep_P x i) (kR:=1) (cR:=10)
  intro s xs ys zs hxs
  rw [scanFold_den]
  apply (scan_result_mag ys s).trans
  apply G_mono le_rfl le_rfl
  have hm := mag_sublist .nat (show ys.Sublist xs by rw [hxs]; exact List.sublist_append_left _ _)
  simp only [mag_prod]
  omega

@[polyB] theorem items_P (x : Ix) (i : Indices) : PolyB (itemsF x i) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP,itemsBody,polyB])

@[polyB] theorem sumFold_P (x : Ix) (idx : ℕ) : PolyB (foldrF (addF x.add) idx) := by
  apply foldr_polyB_res _ _ (addF_P x.add) (kR:=0) (cR:=0)
  intro ds z
  have hs : foldrDen (addF x.add) ds z = ds.sum+z := by
    induction ds with
    | nil => simp [foldrDen]
    | cons r ds ih =>
      change r+foldrDen (addF x.add) ds z = (r+ds.sum)+z
      rw [ih]
      exact (Nat.add_assoc r ds.sum z).symm
  rw [hs,G_zero]
  simp only [mag_prod,mag_nat,natList_mag]
  omega

@[polyB] theorem weight_P (x : Ix) (i : Indices) : PolyB (weightF x i) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP,weightBody,polyB])

@[polyB] theorem weightsStep_P (x : Ix) (i : Indices) : PolyB (weightsStepF x i) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP,weightsStepBody,polyB])

/-- This auxiliary expression is used only to bound the fold's mathematical
result. It does not replace the compiled fold or assert execution of a helper. -/
private def foldResultBody (x : Ix) (i : Indices) :
    Tm [.prod (.list TItem) (.prod .nat TBlock)] (.prod .nat TBlock) :=
  .pair (.fst (.snd v0)) (.app (blockMergeF x) (.pair (.fst (.snd v0))
    (.app (appendF TBlock x.append) (.pair
      (.app (mapEnvF (weightF x i) 0) (.pair (.fst (.snd v0)) (.fst v0)))
      (.lcons (.snd (.snd v0)) .lnil)))))

private theorem foldResult_den (x : Ix) (i : Indices) (as : List Item)
    (v : ℕ) (B : Plain.BlockP) :
    (foldResultBody x i).den (Env.one (as,v,B)) =
      foldrDen (weightsStepF x i) as (v,B) := by
  simp only [foldResultBody,tm_simp,blockMergeF_den,appendF_den,mapEnvF_den]
  rw [weightsFold_den]
  congr 1
  induction as with
  | nil => simp [Plain.blockMerge,Plain.blockAnd,Plain.formS]
  | cons a as ih =>
    simp only [List.map_cons,List.cons_append,Plain.blockMerge,List.foldr_cons,ih]
    exact congrArg (fun W => Plain.blockAnd v W
      (as.foldr (fun a B => Plain.blockAnd v (weightOffset v a) B) B)) (weight_den x i v a)

@[polyB] theorem weightsFold_P (x : Ix) (i : Indices) :
    PolyB (foldrF (weightsStepF x i) i.weightsFold) := by
  have hhelper := polyB_bodySig 0 (foldResultBody x i)
    (by simp [Tm.CallsP,foldResultBody,polyB])
  rcases hhelper with ⟨k,c,hhelper⟩
  apply foldr_polyB_res _ _ (weightsStep_P x i) (kR:=k) (cR:=c)
  intro as s
  rcases s with ⟨v,B⟩
  have hr := (hhelper (as,v,B)).2.2.2
  change mag (.prod .nat TBlock) ((foldResultBody x i).den (Env.one (as,v,B))) ≤ _ at hr
  exact (foldResult_den x i as v B) ▸ hr

@[polyB] theorem weights_P (x : Ix) (i : Indices) : PolyB (weightsF x i) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP,weightsBody,polyB])

@[polyB] theorem layer_P (x : Ix) (i : Indices) : PolyB (layerF x i) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP,layerBody,polyB])

/-- A fixed polynomial bounds all local work and the output word of the
actual compiler, uniformly over class lists, coefficient indices and circuits. -/
theorem query_P (x : Ix) (i : Indices) : PolyB (queryF x i) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP,queryBody,argN,argDs,argRows,argC,argSide,argJs,
    argH,argTarget,argPre,argD,polyB])

theorem query_polynomial (x : Ix) (i : Indices) : ∃ k c : ℕ, ∀ p : TArg.den,
    (queryF x i).cost p ≤ 26^(2^k-1)*(mag TArg p+c+4)^(2^k) ∧
    (queryF x i).depth p ≤ 26^(2^k-1)*(mag TArg p+c+4)^(2^k) ∧
    (queryF x i).msize p ≤ 26^(2^k-1)*(mag TArg p+c+4)^(2^k) ∧
    mag TBits ((queryF x i).den p) ≤ 26^(2^k-1)*(mag TArg p+c+4)^(2^k) := by
  rcases query_P x i with ⟨k,c,h⟩
  refine ⟨k,c,fun p => ?_⟩
  have hb := h p
  have hp := G_poly k c (mag TArg p)
  exact ⟨by omega,by omega,by omega,by omega⟩

end QecReliability.TensorQuery.FLCompiler
