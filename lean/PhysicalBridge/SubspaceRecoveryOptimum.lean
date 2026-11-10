import PhysicalBridge.GlobalSyndromeDecoder

/-! Exact all-CPTP optimal recovery for uniform noise on any binary physical
Pauli subspace. The upper bound does not assume syndrome-measuring recovery. -/
noncomputable section
namespace QecPhysical.Stabilizer.Lift
open scoped BigOperators
open Matrix Module
open QecReliability.Binary
open QecPhysical.BinaryPauli
variable {n : ℕ} {S : Submodule Bit (Pauli n)} (L : Lift S)

theorem subspaceNoise_upper_bound (U : Submodule Bit (Pauli n))
    (R : Channel (Word n) L.LogicalIndex) :
    entanglementFidelity (R.comp (L.subspaceNoise U)).map ≤
      ((2 : ℝ) ^ QecReliability.ambiguity (symplectic n) S U)⁻¹ := by
  obtain ⟨_, _, hbound⟩ := L.localLogicalNoise_optimum U
  change entanglementFidelity (R.map.comp (L.subspaceNoise U).map) ≤ _
  rw [L.subspaceNoise_decomposition, comp_uniformMap, fidelity_uniformMap]
  calc
    _ ≤ ∑ _ : PopulatedSyndrome S U, (Fintype.card (PopulatedSyndrome S U) : ℝ)⁻¹ *
        ((2 : ℝ) ^ QecReliability.ambiguity (symplectic n) S U)⁻¹ := by
      apply Finset.sum_le_sum
      intro χ _
      apply mul_le_mul_of_nonneg_left _ (uniformWeightsAll_nonneg χ)
      exact hbound (R.comp (L.syndromeEmbedding U χ))
    _ = _ := by rw [← Finset.sum_mul, uniformWeightsAll_sum, one_mul]

theorem subspaceNoise_optimum (U : Submodule Bit (Pauli n)) :
    ∃ R : Channel (Word n) L.LogicalIndex,
      entanglementFidelity (R.comp (L.subspaceNoise U)).map =
        ((2 : ℝ) ^ QecReliability.ambiguity (symplectic n) S U)⁻¹ ∧
      ∀ Q : Channel (Word n) L.LogicalIndex,
        entanglementFidelity (Q.comp (L.subspaceNoise U)).map ≤
          ((2 : ℝ) ^ QecReliability.ambiguity (symplectic n) S U)⁻¹ := by
  obtain ⟨R, hR, _⟩ := L.localLogicalNoise_optimum U
  refine ⟨R.comp (L.globalSyndromeDecoder U), ?_, L.subspaceNoise_upper_bound U⟩
  change entanglementFidelity ((R.map.comp (L.globalSyndromeDecoder U).map).comp
    (L.subspaceNoise U).map) = _
  rw [LinearMap.comp_assoc, L.globalSyndromeDecoder_subspaceNoise]
  exact hR

end QecPhysical.Stabilizer.Lift
