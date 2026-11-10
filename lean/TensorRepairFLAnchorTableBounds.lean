import TensorRepairFLAnchorBounds
import TensorRepairFLTableBounds

/-! Actual exact-anchor table execution with polynomial bit resources. -/
set_option autoImplicit false
namespace QecReliability.TensorMachine.RepairFL
open FL FL.Lib FL.Lib.LinearRepairFL Trans.Wire
open Trans.Query.Bound Trans.BoundsQH
open Trans.Control (bodySig_cost bodySig_depth bodySig_msize)

variable (L : Lib) (ci : CanonicalIndices) (y : Trans.Control.IxR) (ai : AnchorIndices)

theorem anchorDataR_length (ctx : AnchorCtx) (keys : List Key) :
    (anchorDataR ctx keys).length ≤ keys.length := by
  induction keys with
  | nil => exact le_rfl
  | cons key keys ih =>
    rw [anchorDataR]
    split <;> simp only [List.length_cons] <;> omega

theorem anchorDataR_bound (D B : ℕ) (ctx : AnchorCtx) (keys : List Key)
    (hk : ∀ key ∈ keys, mag TKey key ≤ D)
    (hb : ∀ key ∈ keys, RB B (dyadicR ctx key)) : TableBound D B (anchorDataR ctx keys) := by
  induction keys with
  | nil => intro x hx; simp [anchorDataR] at hx
  | cons key keys ih =>
    have ht := ih (fun key h => hk key (by simp [h])) (fun key h => hb key (by simp [h]))
    rw [anchorDataR]
    split
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨hk key (by simp),hb key (by simp)⟩
      · exact ht x hx
    · exact ht

def anchorStepBudget (M B K N : ℕ) : ℕ := 3*K+100*(M+B+1)*(N+1)

private def anchorStepBodyAbstract
    (corner : FnSig (.prod TKey TKey) .bool)
    (dyadic : FnSig (.prod TAnchorCtx TKey) TRatio) :
    FL.Tm [.prod TKey (.prod TAnchorCtx TTable)] (.prod TAnchorCtx TTable) :=
  .pair (.fst (.snd FL.Tm.v0))
    (.ite (.app corner (.pair (.fst (.fst (.snd FL.Tm.v0))) (.fst FL.Tm.v0)))
      (.lcons (.pair (.fst FL.Tm.v0)
        (.app dyadic (.pair (.fst (.snd FL.Tm.v0)) (.fst FL.Tm.v0))))
        (.snd (.snd FL.Tm.v0)))
      (.snd (.snd FL.Tm.v0)))

set_option maxHeartbeats 1000000 in
private theorem anchorStepAbstract_resources
    (corner : FnSig (.prod TKey TKey) .bool)
    (dyadic : FnSig (.prod TAnchorCtx TKey) TRatio) (slot : ℕ)
    (M B K N : ℕ) (ctx : AnchorCtx) (key : Key) (acc : RawTable)
    (hctx : mag TAnchorCtx ctx ≤ M) (hk : mag TKey key ≤ M)
    (ha : TableBound M B acc) (hn : acc.length ≤ N)
    (hd : ResBound dyadic (ctx,key) K)
    (hc : ResBound corner (ctx.1,key) K)
    (hb : RB B (dyadic.den (ctx,key))) :
    ResBound (Trans.Control.bodySig slot (anchorStepBodyAbstract corner dyadic)) (key,ctx,acc) (anchorStepBudget M B K N) := by
  suffices hs : ResBound (Trans.Control.bodySig slot (anchorStepBodyAbstract corner dyadic))
      (key,ctx,acc) (3*K+2*((5*M+8*B+6)*N)+(10*M+16*B+32)) by
    have hbudget : 3*K+2*((5*M+8*B+6)*N)+(10*M+16*B+32) ≤ anchorStepBudget M B K N := by
      unfold anchorStepBudget
      nlinarith
    rcases hs with ⟨hsCost,hsDepth,hsSize⟩
    exact ⟨hsCost.trans hbudget,hsDepth.trans hbudget,hsSize.trans hbudget⟩
  have sc := (size_le_mag TAnchorCtx ctx).trans (show 5*mag TAnchorCtx ctx+1 ≤ 5*M+1 by omega)
  have sc' := sc
  simp only [TAnchorCtx,Ty.enc_prod,Val.size_cons] at sc'
  have sc'' := sc'
  simp only [Ty.enc_nat] at sc''
  have sk := key_encoded_size hk
  have sr := ratio_encoded_size B (dyadic.den (ctx,key)) hb
  have sa := table_encoded_size ha
  have saN : (TTable.enc acc).size ≤ (5*M+8*B+6)*N+1 :=
    sa.trans (by nlinarith [Nat.mul_le_mul_left (5*M+8*B+6) hn])
  have hnew : TableBound M B ((key,dyadic.den (ctx,key))::acc) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨hk,hb⟩
    · exact ha x hx
  have sn := table_encoded_size hnew
  have snN : (TTable.enc ((key,dyadic.den (ctx,key))::acc)).size ≤ (5*M+8*B+6)*(N+1)+1 := by
    simp only [List.length_cons] at sn
    exact sn.trans (by nlinarith [Nat.mul_le_mul_left (5*M+8*B+6) hn])
  have snN' : ((Ty.list TEntry).enc ((key,dyadic.den (ctx,key))::acc)).size ≤ (5*M+8*B+6)*(N+1)+1 := snN
  rcases hd with ⟨dc,dd,dm⟩
  rcases hc with ⟨cc,cd,cm⟩
  have hdepth : max (corner.depth (ctx.1,key))
      (dyadic.depth (ctx,key)) ≤ K := max_le cd dd
  simp only [TRatio,Ty.enc_prod,Val.size_cons] at sr
  simp only [ResBound,bodySig_cost,bodySig_depth,bodySig_msize,
    anchorStepBodyAbstract,tm_simp]
  simp only [Ty.enc_prod,Ty.enc_list_cons,Val.size_cons]
  split_ifs <;> simp only [max_self,zero_max,max_zero,max_le_iff] <;>
    (simp only [Nat.mul_add,Nat.mul_one] at *; omega)


theorem anchorDataStep_resources (M B K N : ℕ) (ctx : AnchorCtx) (key : Key) (acc : RawTable)
    (hctx : mag TAnchorCtx ctx ≤ M) (hk : mag TKey key ≤ M)
    (ha : TableBound M B acc) (hn : acc.length ≤ N)
    (hd : ResBound (dyadicF L ci y ai) (ctx,key) K)
    (hc : ResBound (cornerF L ci) (ctx.1,key) K)
    (hb : RB B (dyadicR ctx key)) :
    ResBound (anchorDataStepF L ci y ai) (key,ctx,acc) (anchorStepBudget M B K N) := by
  have hb' : RB B ((dyadicF L ci y ai).den (ctx,key)) := by
    rw [dyadicF_den]
    exact hb
  exact anchorStepAbstract_resources (cornerF L ci) (dyadicF L ci y ai) ai.step
    M B K N ctx key acc hctx hk ha hn hd hc hb'


def anchorTableBudget (M B K N : ℕ) : ℕ := 20*(anchorStepBudget M B K N+12)*(N+1)+100

set_option maxHeartbeats 1000000 in
theorem anchorData_resources_of_bounds (M B K : ℕ) (ctx : AnchorCtx) (keys : List Key)
    (hctx : mag TAnchorCtx ctx ≤ M) (hk : ∀ key ∈ keys, mag TKey key ≤ M)
    (hd : ∀ key ∈ keys, ResBound (dyadicF L ci y ai) (ctx,key) K)
    (hc : ∀ key ∈ keys, ResBound (cornerF L ci) (ctx.1,key) K)
    (hb : ∀ key ∈ keys, RB B (dyadicR ctx key)) :
    ResBound (anchorDataF L ci y ai) (ctx,keys) (anchorTableBudget M B K keys.length) := by
  let S := anchorStepBudget M B K keys.length
  have sc := (size_le_mag TAnchorCtx ctx).trans (show 5*mag TAnchorCtx ctx+1 ≤ 5*M+1 by omega)
  have sc' := sc
  simp only [TAnchorCtx,Ty.enc_prod,Val.size_cons] at sc'
  have sc'' := sc'
  simp only [Ty.enc_nat] at sc''
  have submem (pre ys : List Key) (he : keys = pre++ys) : ∀ key ∈ ys, key ∈ keys := by
    intro key h
    rw [he]
    exact List.mem_append.mpr (Or.inr h)
  have hlen (pre ys : List Key) (he : keys = pre++ys) : ys.length ≤ keys.length := by
    rw [he,List.length_append]
    omega
  have hr : ∀ pre ys, keys = pre++ys →
      ((Ty.prod TAnchorCtx TTable).enc (foldrDen (anchorDataStepF L ci y ai) ys (ctx,[]))).size ≤ S := by
    intro pre ys he
    rw [anchorDataFold_den]
    have ht := anchorDataR_bound M B ctx ys
      (fun key h => hk key (submem pre ys he key h))
      (fun key h => hb key (submem pre ys he key h))
    have ss := table_encoded_size ht
    have hn := (anchorDataR_length ctx ys).trans (hlen pre ys he)
    have ssN : (TTable.enc (anchorDataR ctx ys)).size ≤ (5*M+8*B+6)*keys.length+1 :=
      ss.trans (by nlinarith [Nat.mul_le_mul_left (5*M+8*B+6) hn])
    simp only [Ty.enc_prod,Val.size_cons]
    dsimp [S,anchorStepBudget]
    nlinarith
  have hz : ((Ty.prod TAnchorCtx TTable).enc (ctx,[])).size ≤ S := by
    have he := hr keys [] (List.append_nil keys).symm
    rw [foldrDen_nil] at he
    exact he
  have hstep : ∀ pre key ys, keys = pre++key::ys →
      ResBound (anchorDataStepF L ci y ai)
        (key,foldrDen (anchorDataStepF L ci y ai) ys (ctx,[])) S := by
    intro pre key ys he
    have hkey := submem pre (key::ys) he key (by simp)
    have htail : ∀ z ∈ ys, z ∈ keys := fun z hz => submem pre (key::ys) he z (by simp [hz])
    have ht := anchorDataR_bound M B ctx ys
      (fun z hz => hk z (htail z hz)) (fun z hz => hb z (htail z hz))
    have hn : (anchorDataR ctx ys).length ≤ keys.length := by
      have := hlen pre (key::ys) he
      have := anchorDataR_length ctx ys
      simp only [List.length_cons] at *
      omega
    rw [anchorDataFold_den]
    exact anchorDataStep_resources L ci y ai M B K keys.length ctx key (anchorDataR ctx ys)
      hctx (hk key hkey) ht hn (hd key hkey) (hc key hkey) (hb key hkey)
  obtain ⟨fc,fd,fm⟩ := foldr_suffix_resources (anchorDataStepF L ci y ai) keys (ctx,[]) S S S hz hr hstep
  have sm := mag_list_le TKey keys M hk
  have sk := size_le_mag (.list TKey) keys
  have skS : ((Ty.list TKey).enc keys).size ≤ S := by
    dsimp [S,anchorStepBudget]
    nlinarith
  have scS : (TAnchorCtx.enc ctx).size ≤ S := by dsimp [S,anchorStepBudget]; nlinarith
  have scS' := scS
  simp only [TAnchorCtx,Ty.enc_prod,Val.size_cons] at scS'
  simp only [ResBound,anchorDataF,bodySig_cost,bodySig_depth,bodySig_msize,anchorDataBody,
    tm_simp,foldrF_cost,foldrF_depth,foldrF_msize,Ty.enc_prod,Ty.enc_list_nil,Val.size_cons,
    Val.size_nil,max_le_iff]
  have sempty : (TTable.enc ([] : RawTable)).size = 1 := rfl
  simp only [max_self,zero_max]
  unfold anchorTableBudget
  (repeat' apply And.intro) <;>
    (change _ ≤ 20*(S+12)*(keys.length+1)+100; nlinarith)

/-- Uniform polynomial resources and bit bounds for the physically computed
anchor table, with constants independent of the code, grid, and key list. -/
theorem anchorData_uniform : ∃ kd cd kc cc, ∀ (M : ℕ) (ctx : AnchorCtx) (keys : List Key),
    mag TAnchorCtx ctx ≤ M → (∀ key ∈ keys, mag TKey key ≤ M) →
    ResBound (anchorDataF L ci y ai) (ctx,keys)
      (anchorTableBudget M (G kd cd (2*M+1)+1)
        (dyadicBudget kd cd (2*M+1)+G kc cc (2*M+1)) keys.length) ∧
    TableBound M (G kd cd (2*M+1)+1) (anchorDataR ctx keys) := by
  obtain ⟨kd,cd,hd⟩ := dyadic_resources L ci y ai
  obtain ⟨kc,cc,hc⟩ := corner_poly L ci
  refine ⟨kd,cd,kc,cc,?_⟩
  intro M ctx keys hctx hk
  have hctx' := hctx
  simp only [TAnchorCtx,mag_prod,mag_nat] at hctx'
  have hdy key (hkey : key ∈ keys) :
      ResBound (dyadicF L ci y ai) (ctx,key) (dyadicBudget kd cd (2*M+1)+G kc cc (2*M+1)) ∧
      RB (G kd cd (2*M+1)+1) (dyadicR ctx key) := by
    obtain ⟨hr,hb⟩ := hd ctx key
    have ha : mag (.prod TAnchorCtx TKey) (ctx,key) ≤ 2*M+1 := by
      simp only [mag_prod,mag_nat]
      have := hk key hkey
      omega
    have hg := G_mono (k := kd) (c := cd) le_rfl le_rfl ha
    have hbudget : dyadicBudget kd cd (mag (.prod TAnchorCtx TKey) (ctx,key)) ≤
        dyadicBudget kd cd (2*M+1)+G kc cc (2*M+1) := by
      unfold dyadicBudget
      have := Nat.mul_le_mul (Nat.add_le_add_right hg 1) (Nat.add_le_add_right hg 1)
      omega
    exact ⟨hr.mono hbudget,⟨hb.1.trans (by omega),hb.2.trans (by omega)⟩⟩
  have hcorner key (hkey : key ∈ keys) :
      ResBound (cornerF L ci) (ctx.1,key) (dyadicBudget kd cd (2*M+1)+G kc cc (2*M+1)) := by
    obtain ⟨rc,rd,rm,_⟩ := hc (ctx.1,key)
    have hck : mag TKey ctx.1 ≤ M := by
      simp only [TAnchorCtx,mag_prod] at hctx
      omega
    have ha : mag (.prod TKey TKey) (ctx.1,key) ≤ 2*M+1 := by
      simp only [mag_prod,mag_nat]
      have := hk key hkey
      omega
    have hg := G_mono (k := kc) (c := cc) le_rfl le_rfl ha
    exact ⟨rc.trans (by omega),rd.trans (by omega),rm.trans (by omega)⟩
  exact ⟨anchorData_resources_of_bounds L ci y ai M _ _ ctx keys hctx hk
      (fun key h => (hdy key h).1) hcorner (fun key h => (hdy key h).2),
    anchorDataR_bound M _ ctx keys hk (fun key h => (hdy key h).2)⟩

end QecReliability.TensorMachine.RepairFL
