import PhysicalBridge.IsometryDecoder
import PhysicalBridge.SubspaceNoiseDecomposition

/-! A global CPTP syndrome decoder, with a trace-preserving completion on
every unused branch. Its action on each populated branch is proved exactly. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace QecPhysical.Stabilizer.Lift
open scoped BigOperators
open Matrix Module
open QecReliability.Binary
open QecPhysical.BinaryPauli
variable {n : ℕ} {S : Submodule Bit (Pauli n)} (L : Lift S)

theorem allSyndrome_projectors_sum : ∑ χ : S →ₗ[Bit] Bit, (L.twist χ).projector = 1 := by
  let b := Module.finBasis Bit S
  have h := Fintype.sum_bijective (basisCharacter b)
    ⟨basisCharacter_injective b, basisCharacter_surjective b⟩
    (fun a => (L.twist (basisCharacter b a)).projector)
    (fun χ => (L.twist χ).projector) (fun _ => rfl)
  exact h.symm.trans (L.syndrome_projectors_sum b)

theorem allSyndrome_projectors_gram :
    ∑ χ : S →ₗ[Bit] Bit, ((L.twist χ).projector)ᴴ * (L.twist χ).projector = 1 := by
  have h (χ : S →ₗ[Bit] Bit) : ((L.twist χ).projector)ᴴ * (L.twist χ).projector =
      (L.twist χ).projector := by
    rw [(L.twist χ).projector_hermitian.eq, (L.twist χ).projector_idempotent]
  simp_rw [h]
  exact L.allSyndrome_projectors_sum

def syndromeBranchDecoder (U : Submodule Bit (Pauli n)) (χ : S →ₗ[Bit] Bit) :
    Channel (Word n) L.LogicalIndex :=
  if h : χ ∈ PopulatedSyndrome S U then
    isometryDecoder (L.errorEncoding (syndromeRepresentative S U ⟨χ,h⟩).val)
      (L.errorEncoding_isometry _)
  else fillChannel

def globalSyndromeDecoder (U : Submodule Bit (Pauli n)) : Channel (Word n) L.LogicalIndex :=
  projectiveRecovery (fun χ : S →ₗ[Bit] Bit => (L.twist χ).projector)
    L.allSyndrome_projectors_gram (L.syndromeBranchDecoder U)

theorem globalSyndromeDecoder_embedding (U : Submodule Bit (Pauli n)) (χ : PopulatedSyndrome S U) :
    (L.globalSyndromeDecoder U).map.comp (L.syndromeEmbedding U χ).map = LinearMap.id := by
  have hW (ψ : S →ₗ[Bit] Bit) :
      (L.twist ψ).projector * L.errorEncoding (syndromeRepresentative S U χ).val =
        if ψ=χ.val then L.errorEncoding (syndromeRepresentative S U χ).val else 0 := by
    have h := L.error_encoding_block ψ (syndromeRepresentative S U χ).val
    rw [syndromeRepresentative_character] at h
    exact h
  change (projectiveRecovery _ _ (L.syndromeBranchDecoder U)).map.comp
    (conjugateMap (L.errorEncoding (syndromeRepresentative S U χ).val)) = _
  rw [projectiveRecovery_branch _ _ _ χ.val _ hW]
  simp only [syndromeBranchDecoder, dif_pos χ.property]
  exact isometryDecoder_left_inverse _ _

theorem globalSyndromeDecoder_subspaceNoise (U : Submodule Bit (Pauli n)) :
    (L.globalSyndromeDecoder U).map.comp (L.subspaceNoise U).map = L.localLogicalNoise U := by
  rw [L.subspaceNoise_decomposition, comp_uniformMap]
  have h (χ : PopulatedSyndrome S U) :
      (L.globalSyndromeDecoder U).map.comp
        ((L.syndromeEmbedding U χ).map.comp (L.localLogicalNoise U)) = L.localLogicalNoise U := by
    rw [← LinearMap.comp_assoc, L.globalSyndromeDecoder_embedding, LinearMap.id_comp]
  rw [funext h, uniformMap_const]

end QecPhysical.Stabilizer.Lift
