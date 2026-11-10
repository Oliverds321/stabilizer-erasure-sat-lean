import PhysicalBridge.LinearFibers
import PhysicalBridge.LogicalResolution

/-! Logical images of supported normalizer errors have exactly equal fibers.
The kernel is the supported stabilizer space, and the image has size 2^d. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace QecPhysical.Stabilizer
open scoped BigOperators
open Matrix Module
open QecReliability.Binary
open QecPhysical.BinaryPauli
variable {n : ℕ} (S U : Submodule Bit (Pauli n))

def localLogicalMap : (Normalizer S ⊓ U : Submodule Bit (Pauli n)) →ₗ[Bit] LogicalClass S :=
  (stabilizerInNormalizer S).mkQ.comp (Submodule.inclusion inf_le_left)

theorem localLogicalMap_eq_zero (x : (Normalizer S ⊓ U : Submodule Bit (Pauli n))) :
    localLogicalMap S U x = 0 ↔ x.val ∈ S := by
  exact Submodule.Quotient.mk_eq_zero (p := stabilizerInNormalizer S)
    (x := (⟨x.val, x.property.1⟩ : Normalizer S))

def localKernelEquiv (hS : S ≤ Normalizer S) :
    LinearMap.ker (localLogicalMap S U) ≃ₗ[Bit] (S ⊓ U : Submodule Bit (Pauli n)) where
  toFun x := ⟨x.val.val, (localLogicalMap_eq_zero S U x.val).mp (LinearMap.mem_ker.mp x.property),
    x.val.property.2⟩
  invFun x := ⟨⟨x.val, hS x.property.1, x.property.2⟩,
    (localLogicalMap_eq_zero S U _).mpr x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem localLogicalImage_finrank (hS : S ≤ Normalizer S) :
    finrank Bit (LinearMap.range (localLogicalMap S U)) = QecReliability.ambiguity (symplectic n) S U := by
  have h := (localLogicalMap S U).finrank_range_add_finrank_ker
  rw [(localKernelEquiv S U hS).finrank_eq] at h
  exact Nat.eq_sub_of_add_eq h

theorem localLogicalImage_card (hS : S ≤ Normalizer S) :
    Nat.card (LinearMap.range (localLogicalMap S U)) =
      2 ^ QecReliability.ambiguity (symplectic n) S U := by
  rw [Module.natCard_eq_pow_finrank (K := Bit), localLogicalImage_finrank S U hS]
  simp [Bit, Nat.card_eq_fintype_card, ZMod.card]

theorem localLogicalFiber_card (hS : S ≤ Normalizer S) (c : LogicalClass S)
    (hc : c ∈ LinearMap.range (localLogicalMap S U)) :
    Nat.card {x : (Normalizer S ⊓ U : Submodule Bit (Pauli n)) // localLogicalMap S U x=c} =
      2 ^ finrank Bit (S ⊓ U : Submodule Bit (Pauli n)) := by
  rw [linearFiber_card _ c hc, Nat.card_congr (localKernelEquiv S U hS).toEquiv,
    Module.natCard_eq_pow_finrank (K := Bit)]
  simp [Bit, Nat.card_eq_fintype_card, ZMod.card]

def logicalSupport : Finset (LogicalClass S) :=
  Finset.univ.filter (fun c => c ∈ LinearMap.range (localLogicalMap S U))

theorem logicalSupport_card (hS : S ≤ Normalizer S) :
    (logicalSupport S U).card = 2 ^ QecReliability.ambiguity (symplectic n) S U := by
  have h := localLogicalImage_card S U hS
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  exact h

theorem logicalSupport_nonempty : (logicalSupport S U).Nonempty := by
  refine ⟨0, ?_⟩
  simp only [logicalSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨0, (localLogicalMap S U).map_zero⟩

end QecPhysical.Stabilizer
