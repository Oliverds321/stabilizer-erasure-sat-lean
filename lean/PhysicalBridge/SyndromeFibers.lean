import PhysicalBridge.RangeKernelProduct
import PhysicalBridge.EncodedNormalizerNoise

/-! Every populated physical syndrome fiber is an affine copy of N intersect U.
The product equivalence retains every original physical error exactly once. -/
noncomputable section
namespace QecPhysical.Stabilizer
open scoped BigOperators
open Matrix Module
open QecReliability.Binary
open QecPhysical.BinaryPauli
variable {n : ℕ} (S U : Submodule Bit (Pauli n))

instance syndromeFintype : Fintype (S →ₗ[Bit] Bit) :=
  Fintype.ofInjective (fun f : S →ₗ[Bit] Bit => (f : S → Bit)) DFunLike.coe_injective

def subspaceSyndrome : U →ₗ[Bit] (S →ₗ[Bit] Bit) where
  toFun x := errorCharacter S x.val
  map_add' x y := by ext s; exact (symplectic n s.val).map_add x.val y.val
  map_smul' c x := by ext s; exact (symplectic n s.val).map_smul c x.val

abbrev PopulatedSyndrome := LinearMap.range (subspaceSyndrome S U)

instance populatedSyndromeFintype : Fintype (PopulatedSyndrome S U) := Fintype.ofFinite _

def syndromeKernelEquiv : LinearMap.ker (subspaceSyndrome S U) ≃ₗ[Bit]
    (Normalizer S ⊓ U : Submodule Bit (Pauli n)) where
  toFun x := ⟨x.val.val, (errorCharacter_eq_zero_iff x.val.val).mp x.property, x.val.property⟩
  invFun x := ⟨⟨x.val, x.property.2⟩, (errorCharacter_eq_zero_iff x.val).mpr x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def syndromeRepresentative (χ : PopulatedSyndrome S U) : U :=
  rangeRepresentative (subspaceSyndrome S U) χ

theorem syndromeRepresentative_character (χ : PopulatedSyndrome S U) :
    errorCharacter S (syndromeRepresentative S U χ).val = χ.val :=
  rangeRepresentative_apply (subspaceSyndrome S U) χ

def syndromeProductEquiv :
    (PopulatedSyndrome S U × (Normalizer S ⊓ U : Submodule Bit (Pauli n))) ≃ U :=
  (Equiv.prodCongr (Equiv.refl _) (syndromeKernelEquiv S U).symm.toEquiv).trans
    (rangeKernelProduct (subspaceSyndrome S U))

theorem syndromeProductEquiv_val (χ : PopulatedSyndrome S U)
    (x : (Normalizer S ⊓ U : Submodule Bit (Pauli n))) :
    (syndromeProductEquiv S U (χ,x)).val = (syndromeRepresentative S U χ).val + x.val := rfl

theorem subspace_card_syndrome_kernel : Fintype.card U =
    Fintype.card (PopulatedSyndrome S U) * Fintype.card (Normalizer S ⊓ U : Submodule Bit (Pauli n)) := by
  rw [← Fintype.card_congr (syndromeProductEquiv S U), Fintype.card_prod]

end QecPhysical.Stabilizer
