import TensorRepairFLBitBounds

/-! Polynomial scan bounds for the actual compiled repair functions. All
large natural components are controlled by their binary lengths. -/
set_option autoImplicit false

namespace QecReliability.TensorMachine.RepairFL
open FL FL.Lib FL.Lib.LinearRepairFL Trans.Wire
open Trans.Query.Bound
open Trans.Control (bodySig_cost bodySig_depth bodySig_msize)

def scanStepBudget (D B K : ℕ) : ℕ := K + comparisonBitsBudget B + 100*(D+B+1)

variable (L : Lib) (i : Indices)

theorem lowerStep_resources (D B K : ℕ) (k j : Key) (x z : RawRatio)
    (hk : mag TKey k ≤ D) (hj : mag TKey j ≤ D) (hx : RB B x) (hz : RB B z)
    (hc : ResBound (keyLeF L i) (k,j) K) :
    ResBound (lowerStepF L i) ((k,x),(j,z)) (scanStepBudget D B K) := by
  have sk := key_encoded_size hk
  have sj := key_encoded_size hj
  have sx := ratio_encoded_size B x hx
  have sz := ratio_encoded_size B z hz
  have sc := lesser_resources i.lesser x z B hx hz
  have ss := ratio_encoded_size B (lesserR x z) (lesserR_RB hx hz)
  simp only [TRatio,Ty.enc_prod,Val.size_cons] at sx sz ss
  rcases sc with ⟨sc,sd,sm⟩
  rcases hc with ⟨hc,hd,hm⟩
  simp only [ResBound,lowerStepF,bodySig_cost,bodySig_depth,bodySig_msize,
    lowerStepBody,tm_simp,Ty.enc_prod,Val.size_cons,lesserF_den,scanStepBudget]
  split_ifs <;> simp only [max_le_iff] <;> omega

theorem upperStep_resources (D B K : ℕ) (k j : Key) (x z : RawRatio)
    (hk : mag TKey k ≤ D) (hj : mag TKey j ≤ D) (hx : RB B x) (hz : RB B z)
    (hc : ResBound (keyLeF L i) (j,k) K) :
    ResBound (upperStepF L i) ((k,x),(j,z)) (scanStepBudget D B K) := by
  have sk := key_encoded_size hk
  have sj := key_encoded_size hj
  have sx := ratio_encoded_size B x hx
  have sz := ratio_encoded_size B z hz
  have sc := greater_resources i.greater x z B hx hz
  have ss := ratio_encoded_size B (greaterR x z) (greaterR_RB hx hz)
  simp only [TRatio,Ty.enc_prod,Val.size_cons] at sx sz ss
  rcases sc with ⟨sc,sd,sm⟩
  rcases hc with ⟨hc,hd,hm⟩
  simp only [ResBound,upperStepF,bodySig_cost,bodySig_depth,bodySig_msize,
    upperStepBody,tm_simp,Ty.enc_prod,Val.size_cons,greaterF_den,scanStepBudget]
  split_ifs <;> simp only [max_le_iff] <;> omega

theorem anchorStep_resources (D B K : ℕ) (k j : Key) (x z : RawRatio)
    (hk : mag TKey k ≤ D) (hj : mag TKey j ≤ D) (hx : RB B x) (hz : RB B z)
    (hc : ResBound (keyEqF L i) (k,j) K) :
    ResBound (anchorStepF L i) ((k,x),(j,z)) (scanStepBudget D B K) := by
  have sk := key_encoded_size hk
  have sj := key_encoded_size hj
  have sx := ratio_encoded_size B x hx
  have sz := ratio_encoded_size B z hz
  simp only [TRatio,Ty.enc_prod,Val.size_cons] at sx sz
  rcases hc with ⟨hc,hd,hm⟩
  simp only [ResBound,anchorStepF,bodySig_cost,bodySig_depth,bodySig_msize,
    anchorStepBody,tm_simp,Ty.enc_prod,Val.size_cons,scanStepBudget]
  split_ifs <;> simp only [max_le_iff] <;> omega

/-- Bounds from the calls made on actual suffixes. This handles accumulating
list folds without postulating that arbitrary length-N accumulators stay at
length N after a cons step. -/
theorem foldr_suffix_resources {a b : Ty} (F : FnSig (.prod a b) b)
    (xs : List a.den) (z : b.den) (K D M : ℕ)
    (hz : (b.enc z).size ≤ M)
    (hr : ∀ pre ys, xs = pre ++ ys → (b.enc (foldrDen F ys z)).size ≤ M)
    (hc : ∀ pre x ys, xs = pre ++ x :: ys →
      F.cost (x,foldrDen F ys z) ≤ K ∧ F.depth (x,foldrDen F ys z) ≤ D ∧
      F.msize (x,foldrDen F ys z) ≤ M) :
    foldrCost F xs z ≤ (K+12)*xs.length+10 ∧
    foldrDepth F xs z ≤ xs.length+D+1 ∧
    foldrMsize F xs z ≤ 2*(Ty.enc (.list a) xs).size+2*M+2 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hr' : ∀ pre ys, xs = pre ++ ys → (b.enc (foldrDen F ys z)).size ≤ M := by
      intro pre ys h
      exact hr (x::pre) ys (by simp [h])
    have hc' : ∀ pre y ys, xs = pre ++ y::ys →
        F.cost (y,foldrDen F ys z) ≤ K ∧ F.depth (y,foldrDen F ys z) ≤ D ∧
        F.msize (y,foldrDen F ys z) ≤ M := by
      intro pre y ys h
      exact hc (x::pre) y ys (by simp [h])
    obtain ⟨ic,id,im⟩ := ih hr' hc'
    obtain ⟨xc,xd,xm⟩ := hc [] x xs rfl
    have sy := hr [x] xs rfl
    refine ⟨?_,?_,?_⟩
    · simp only [foldrCost,List.length_cons]
      nlinarith
    · simp only [foldrDepth,List.length_cons]
      omega
    · simp only [foldrMsize,Ty.enc_prod,Val.size_cons,Ty.sz_list_cons,max_le_iff]
      have hs := Ty.sz_list_cons a x xs
      omega

end QecReliability.TensorMachine.RepairFL
