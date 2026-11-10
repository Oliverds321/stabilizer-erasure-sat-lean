import PhysicalBridge.ChannelSums

/-! Uniform channel mixtures, reindexing and product distributions. -/
noncomputable section
namespace QecPhysical
open scoped BigOperators
open Matrix
variable {α β a b c : Type*} [Fintype α] [Fintype β]

def uniformMap (Φ : α → MatrixMap a b) : MatrixMap a b :=
  mixtureMap (fun _ => (Fintype.card α : ℝ)⁻¹) Φ

theorem uniformWeightsAll_nonneg (x : α) : 0 ≤ (fun _ : α => (Fintype.card α : ℝ)⁻¹) x := by positivity

theorem uniformWeightsAll_sum [Nonempty α] : ∑ _ : α, (Fintype.card α : ℝ)⁻¹ = 1 := by
  have h : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero (α := α))
  simp [h]

def uniformChannel [Fintype a] [Fintype b] [Nonempty α] (Φ : α → Channel a b) : Channel a b :=
  mixtureChannel _ uniformWeightsAll_nonneg uniformWeightsAll_sum Φ

theorem uniformMap_reindex (e : α ≃ β) (Φ : β → MatrixMap a b) :
    uniformMap (fun x => Φ (e x)) = uniformMap Φ := by
  unfold uniformMap mixtureMap
  rw [Fintype.card_congr e]
  exact Fintype.sum_bijective e e.bijective _ _ (fun _ => rfl)

theorem uniformMap_product (Φ : α → β → MatrixMap a b) :
    uniformMap (fun t : α×β => Φ t.1 t.2) = uniformMap (fun x => uniformMap (Φ x)) := by
  simp only [uniformMap, mixtureMap, Fintype.card_prod, Fintype.sum_prod_type,
    Nat.cast_mul, _root_.mul_inv_rev, Complex.ofReal_mul, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [mul_comm]

theorem uniformMap_comp (Φ : α → MatrixMap b c) (Ψ : MatrixMap a b) :
    (uniformMap Φ).comp Ψ = uniformMap (fun x => (Φ x).comp Ψ) := by
  ext X i j
  simp [uniformMap, mixtureMap]

theorem comp_uniformMap (Ψ : MatrixMap b c) (Φ : α → MatrixMap a b) :
    Ψ.comp (uniformMap Φ) = uniformMap (fun x => Ψ.comp (Φ x)) :=
  comp_mixtureMap _ _ _

theorem uniformMap_const [Nonempty α] (Φ : MatrixMap a b) :
    uniformMap (fun _ : α => Φ) = Φ := by
  unfold uniformMap mixtureMap
  rw [← Finset.sum_smul, ← Complex.ofReal_sum, uniformWeightsAll_sum]
  simp

theorem fidelity_uniformMap [Fintype a] [DecidableEq a] (Φ : α → MatrixMap a a) :
    entanglementFidelity (uniformMap Φ) =
      ∑ x, (Fintype.card α : ℝ)⁻¹ * entanglementFidelity (Φ x) :=
  entanglementFidelity_mixture _ _

end QecPhysical
