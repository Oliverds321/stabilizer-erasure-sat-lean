import PhysicalBridge.LinearFibers

/-! Explicit affine coordinates on every nonempty linear fiber. -/
noncomputable section
namespace QecPhysical
open Module LinearMap
variable {F V W : Type*} [Field F] [AddCommGroup V] [AddCommGroup W]
  [Module F V] [Module F W]

def rangeRepresentative (f : V →ₗ[F] W) (y : LinearMap.range f) : V :=
  Classical.choose y.property

theorem rangeRepresentative_apply (f : V →ₗ[F] W) (y : LinearMap.range f) :
    f (rangeRepresentative f y) = y.val := Classical.choose_spec y.property

def rangeKernelProduct (f : V →ₗ[F] W) : (LinearMap.range f × LinearMap.ker f) ≃ V where
  toFun t := rangeRepresentative f t.1 + t.2.val
  invFun x := (⟨f x, ⟨x, rfl⟩⟩, ⟨x-rangeRepresentative f ⟨f x, ⟨x,rfl⟩⟩, by
    simp [LinearMap.mem_ker, map_sub, rangeRepresentative_apply]⟩)
  left_inv t := by
    have hy : (⟨f (rangeRepresentative f t.1+t.2.val),
        ⟨rangeRepresentative f t.1+t.2.val,rfl⟩⟩ : LinearMap.range f) = t.1 := by
      apply Subtype.ext
      simp [map_add, rangeRepresentative_apply, LinearMap.mem_ker.mp t.2.property]
    apply Prod.ext
    · exact hy
    · apply Subtype.ext
      dsimp only
      rw [hy]
      abel
  right_inv x := by dsimp only; abel

end QecPhysical
