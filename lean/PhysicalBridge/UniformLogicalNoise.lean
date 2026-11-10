import PhysicalBridge.LocalLogicalFibers
import PhysicalBridge.LogicalPhaseQuotient
import PhysicalBridge.MixturePushforward

/-! Uniform supported normalizer errors push forward to uniform logical
classes only after the exact kernel-fiber cardinality calculation. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace QecPhysical.Stabilizer
open scoped BigOperators
open Matrix Module
open QecReliability.Binary
open QecPhysical.BinaryPauli
variable {n : ℕ} (S U : Submodule Bit (Pauli n))

theorem localLogical_domain_card (hS : S ≤ Normalizer S) :
    Nat.card (Normalizer S ⊓ U : Submodule Bit (Pauli n)) =
      (logicalSupport S U).card * 2 ^ finrank Bit (S ⊓ U : Submodule Bit (Pauli n)) := by
  have h := (localLogicalMap S U).finrank_range_add_finrank_ker
  rw [localLogicalImage_finrank S U hS, (localKernelEquiv S U hS).finrank_eq] at h
  rw [Nat.card_eq_fintype_card, Lift.index_card, logicalSupport_card S U hS, ← pow_add, h]

theorem localLogical_uniformWeights (hS : S ≤ Normalizer S) (c : LogicalClass S) :
    pushforwardWeights (localLogicalMap S U)
      (fun _ => (Fintype.card (Normalizer S ⊓ U : Submodule Bit (Pauli n)) : ℝ)⁻¹) c =
      UnitaryResolution.uniformWeights (logicalSupport S U) c := by
  rw [pushforward_uniform]
  by_cases hc : c ∈ LinearMap.range (localLogicalMap S U)
  · have hm : c ∈ logicalSupport S U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
    rw [UnitaryResolution.uniformWeights, if_pos hm, localLogicalFiber_card S U hS c hc,
      localLogical_domain_card S U hS, Nat.cast_mul]
    have hb : (2 ^ finrank Bit (S ⊓ U : Submodule Bit (Pauli n)) : ℝ) ≠ 0 := by positivity
    push_cast
    rw [mul_comm ((logicalSupport S U).card : ℝ), div_mul_eq_div_div, div_self hb]
    simp
  · have hm : c ∉ logicalSupport S U := by
      simpa only [logicalSupport, Finset.mem_filter, Finset.mem_univ, true_and] using hc
    letI : IsEmpty {x : (Normalizer S ⊓ U : Submodule Bit (Pauli n)) // localLogicalMap S U x=c} :=
      ⟨fun x => hc ⟨x.val, x.property⟩⟩
    simp [UnitaryResolution.uniformWeights, hm]

namespace Lift
variable {S} (L : Lift S)

def localLogicalNoise : MatrixMap L.LogicalIndex L.LogicalIndex :=
  mixtureMap (fun _ : (Normalizer S ⊓ U : Submodule Bit (Pauli n)) =>
      (Fintype.card (Normalizer S ⊓ U : Submodule Bit (Pauli n)) : ℝ)⁻¹)
    (fun x => conjugateMap (L.logicalOp ⟨x.val, x.property.1⟩))

theorem localLogicalNoise_eq_uniform :
    L.localLogicalNoise U =
      (L.logicalResolution.noiseChannel (UnitaryResolution.uniformWeights (logicalSupport S U))
        (UnitaryResolution.uniformWeights_nonneg _) (UnitaryResolution.uniformWeights_sum _ (logicalSupport_nonempty S U))).map := by
  unfold localLogicalNoise
  have hp (x : (Normalizer S ⊓ U : Submodule Bit (Pauli n))) :
      conjugateMap (L.logicalOp ⟨x.val, x.property.1⟩) =
        (L.logicalResolution.errorChannel (localLogicalMap S U x)).map :=
    L.logicalOp_class_channel _
  have hfun := funext hp
  rw [hfun, mixtureMap_pushforward (localLogicalMap S U) _
    (fun c => (L.logicalResolution.errorChannel c).map)]
  have hw := funext (localLogical_uniformWeights S U L.isotropic)
  rw [hw]
  rfl

theorem localLogicalNoise_optimum :
    ∃ R : Channel L.LogicalIndex L.LogicalIndex,
      entanglementFidelity (R.map.comp (L.localLogicalNoise U)) =
        ((2 : ℝ) ^ QecReliability.ambiguity (symplectic n) S U)⁻¹ ∧
      ∀ Q : Channel L.LogicalIndex L.LogicalIndex,
        entanglementFidelity (Q.map.comp (L.localLogicalNoise U)) ≤
          ((2 : ℝ) ^ QecReliability.ambiguity (symplectic n) S U)⁻¹ := by
  obtain ⟨m, hm⟩ := logicalSupport_nonempty S U
  have h := L.logical_uniform_optimal_recovery (logicalSupport S U) (logicalSupport_nonempty S U) m hm
  refine ⟨L.logicalResolution.inverseChannel m, ?_⟩
  rw [logicalSupport_card S U L.isotropic] at h
  simp only [Nat.cast_pow, Nat.cast_ofNat] at h
  simpa only [L.localLogicalNoise_eq_uniform U, Channel.comp] using h

end Lift
end QecPhysical.Stabilizer
