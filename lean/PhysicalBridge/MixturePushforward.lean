import PhysicalBridge.Mixtures

/-! Exact pushforward of error weights, with all repeated source labels retained. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace QecPhysical
open scoped BigOperators
open Matrix
variable {α β a b : Type*} [Fintype α] [Fintype β]

def pushforwardWeights (f : α → β) (p : α → ℝ) (y : β) : ℝ :=
  ∑ x, if f x=y then p x else 0

theorem mixtureMap_pushforward (f : α → β) (p : α → ℝ) (Φ : β → MatrixMap a b) :
    mixtureMap p (fun x => Φ (f x)) = mixtureMap (pushforwardWeights f p) Φ := by
  unfold mixtureMap pushforwardWeights
  simp only [Complex.ofReal_sum, Finset.sum_smul, apply_ite, Complex.ofReal_zero,
    ite_smul, zero_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

omit [Fintype β] in
theorem pushforward_uniform (f : α → β) (y : β) :
    pushforwardWeights f (fun _ => (Fintype.card α : ℝ)⁻¹) y =
      (Nat.card {x : α // f x=y} : ℝ) / (Nat.card α : ℝ) := by
  simp only [pushforwardWeights, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    Nat.card_eq_fintype_card, Fintype.card_subtype, div_eq_mul_inv]

end QecPhysical
