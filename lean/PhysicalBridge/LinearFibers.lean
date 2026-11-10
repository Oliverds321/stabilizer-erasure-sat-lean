import PhysicalBridge.LogicalQuotient

/-! Fiber cardinality is proved by translation, never inferred by dropping
duplicate images of a map. -/
noncomputable section
namespace QecPhysical
open Module LinearMap
variable {F V W : Type*} [Field F] [AddCommGroup V] [AddCommGroup W]
  [Module F V] [Module F W]

def linearFiberEquivKernel (f : V →ₗ[F] W) (v : V) :
    {x : V // f x = f v} ≃ LinearMap.ker f where
  toFun x := ⟨x.val-v, by simp [LinearMap.mem_ker, map_sub, x.property]⟩
  invFun x := ⟨x.val+v, by simp [map_add, LinearMap.mem_ker.mp x.property]⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

theorem linearFiber_card (f : V →ₗ[F] W) (y : W) (hy : y ∈ LinearMap.range f) :
    Nat.card {x : V // f x=y} = Nat.card (LinearMap.ker f) := by
  obtain ⟨v, rfl⟩ := hy
  exact Nat.card_congr (linearFiberEquivKernel f v)

end QecPhysical
