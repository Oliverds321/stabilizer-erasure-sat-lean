import QecReliability.TensorLatent
import QecReliability.QuantumDecisionBridge

namespace QecReliability.TensorLatent
open TensorBernstein
open scoped BigOperators

def layerIndex : (ds : List ℕ) → CausesGrid ds → Grid ds
  | [], _ => PUnit.unit
  | _ :: ds, b => (hammingLayer b.1, layerIndex ds b.2)

def indexList : (ds : List ℕ) → Grid ds → List ℕ
  | [], _ => []
  | _ :: ds, j => j.1.val :: indexList ds j.2

def layerSize : (ds : List ℕ) → Grid ds → ℕ
  | [], _ => 1
  | r :: ds, j => r.choose j.1.val * layerSize ds j.2

def Layer (ds : List ℕ) (j : Grid ds) := {b : CausesGrid ds // layerIndex ds b = j}

noncomputable instance layerFintype (ds : List ℕ) (j : Grid ds) : Fintype (Layer ds j) := by
  classical
  unfold Layer
  infer_instance

def layerConsEquiv (r : ℕ) (ds : List ℕ) (j : Grid (r :: ds)) :
    Layer (r :: ds) j ≃ {b : Causes r // hammingLayer b = j.1} × Layer ds j.2 where
  toFun b := (⟨b.val.1, congrArg Prod.fst b.property⟩,
    ⟨b.val.2, congrArg Prod.snd b.property⟩)
  invFun b := ⟨(b.1.val, b.2.val), Prod.ext b.1.property b.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem layer_card (ds : List ℕ) (j : Grid ds) : Nat.card (Layer ds j) = layerSize ds j := by
  induction ds with
  | nil =>
    cases j
    change Nat.card {b : PUnit // PUnit.unit = PUnit.unit} = 1
    exact Nat.card_of_subsingleton ⟨PUnit.unit,rfl⟩
  | cons r ds ih =>
    rw [Nat.card_congr (layerConsEquiv r ds j), Nat.card_prod, hamming_layer_card, ih]
    rfl

theorem layerSize_pos (ds : List ℕ) (j : Grid ds) : 0 < layerSize ds j := by
  induction ds with
  | nil => exact Nat.zero_lt_one
  | cons r ds ih =>
    exact Nat.mul_pos (Nat.choose_pos (Nat.le_of_lt_succ j.1.isLt)) (ih j.2)

theorem grid_card (ds : List ℕ) : Fintype.card (Grid ds) = (ds.map (fun r => r+1)).prod := by
  induction ds with
  | nil =>
    change Fintype.card PUnit = 1
    exact Fintype.card_punit
  | cons r ds ih =>
    change Fintype.card (Fin (r+1) × Grid ds) = _
    simp only [Fintype.card_prod,Fintype.card_fin,ih,List.map_cons,List.prod_cons]

noncomputable section

/-- A tensor layer average is the uniform average of its complete cause tuples. -/
theorem layerCoefficients_eq_sum (ds : List ℕ) (f : CausesGrid ds → ℝ) (j : Grid ds) :
    layerCoefficients ds f j = (∑ b : Layer ds j, f b.val) / (layerSize ds j : ℝ) := by
  classical
  induction ds with
  | nil =>
    cases j
    simp only [layerCoefficients, layerSize, Nat.cast_one, div_one]
    symm
    apply Finset.sum_eq_single (⟨PUnit.unit,rfl⟩ : Layer [] PUnit.unit)
    · intro b _ hb
      apply False.elim
      apply hb
      apply Subtype.ext
      exact @Subsingleton.elim PUnit _ _ _
    · intro h
      exact (h (Finset.mem_univ _)).elim
  | cons r ds ih =>
    have hs : (∑ b : Layer (r :: ds) j, f b.val) =
        ∑ b : {b : Causes r // hammingLayer b = j.1},
          ∑ bs : Layer ds j.2, f (b.val,bs.val) := by
      rw [← Equiv.sum_comp (layerConsEquiv r ds j).symm (fun b => f b.val)]
      exact Fintype.sum_prod_type _
    change (∑ b : {b : Causes r // hammingLayer b = j.1},
      layerCoefficients ds (fun bs => f (b.val,bs)) j.2) / (r.choose j.1.val : ℝ) = _
    simp_rw [ih]
    rw [hs]
    simp only [layerSize,Nat.cast_mul,← Finset.sum_div,div_div,mul_comm]

end

/-- The retained class bits form one contiguous word, in class order. -/
def causesBits : (ds : List ℕ) → CausesGrid ds ≃ BitModels ds.sum
  | [] =>
    { toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => PUnit.unit
      left_inv := fun _ => @Subsingleton.elim PUnit _ _ _
      right_inv := fun _ => by funext i; exact Fin.elim0 i }
  | r :: ds => ((Binary.causeBits r).prodCongr (causesBits ds)).trans
      (Binary.appendBits r ds.sum)

def flattenCauses (ds : List ℕ) : CausesGrid ds ≃ Causes ds.sum :=
  (causesBits ds).trans (Binary.causeBits ds.sum).symm

end QecReliability.TensorLatent
