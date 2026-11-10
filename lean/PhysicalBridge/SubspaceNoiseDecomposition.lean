import PhysicalBridge.UniformMixtures
import PhysicalBridge.SyndromeFibers

/-! The exact physical channel decomposition follows from the affine fiber
equivalence and Pauli multiplication, with source multiplicities preserved. -/
noncomputable section
namespace QecPhysical
open scoped BigOperators
open Matrix Module
open QecReliability.Binary
open QecPhysical.BinaryPauli

theorem conjugateMap_bitSign {a b : Type*} [Fintype a] (s : Bit) (A : Matrix b a ℂ) :
    conjugateMap (bitSign s • A) = conjugateMap A := by
  ext X i j
  simp only [conjugateMap, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, bitSign_star, bitSign_square, one_smul]

namespace Stabilizer.Lift
variable {n : ℕ} {S : Submodule Bit (Pauli n)} (L : Lift S)

theorem encoded_add_normalizer (r : Pauli n) (x : Normalizer S) :
    conjugateMap (pauli (r+x.val) * L.encoding) =
      (conjugateMap (pauli r * L.encoding)).comp (conjugateMap (L.logicalOp x)) := by
  rw [conjugateMap_comp, Matrix.mul_assoc, L.logicalOp_intertwine,
    ← Matrix.mul_assoc, pauli_mul, Matrix.smul_mul, conjugateMap_bitSign]

def subspaceNoise (U : Submodule Bit (Pauli n)) : Channel L.LogicalIndex (Word n) :=
  L.encodedPauliChannel (fun e : U => e.val) (fun _ => (Fintype.card U : ℝ)⁻¹)
    uniformWeightsAll_nonneg uniformWeightsAll_sum

def syndromeEmbedding (U : Submodule Bit (Pauli n)) (χ : PopulatedSyndrome S U) :
    Channel L.LogicalIndex (Word n) :=
  isometryChannel (L.errorEncoding (syndromeRepresentative S U χ).val)
    (L.errorEncoding_isometry _)

theorem subspaceNoise_decomposition (U : Submodule Bit (Pauli n)) :
    (L.subspaceNoise U).map =
      uniformMap (fun χ : PopulatedSyndrome S U =>
        (L.syndromeEmbedding U χ).map.comp (L.localLogicalNoise U)) := by
  change uniformMap (fun e : U => conjugateMap (pauli e.val * L.encoding)) = _
  rw [← uniformMap_reindex (syndromeProductEquiv S U) (fun e : U =>
    conjugateMap (pauli e.val * L.encoding))]
  have hf : (fun t => conjugateMap (pauli (syndromeProductEquiv S U t).val * L.encoding)) =
      (fun t : PopulatedSyndrome S U × (Normalizer S ⊓ U : Submodule Bit (Pauli n)) =>
        (L.syndromeEmbedding U t.1).map.comp (conjugateMap (L.logicalOp ⟨t.2.val,t.2.property.1⟩))) := by
    funext t
    obtain ⟨χ,x⟩ := t
    rw [syndromeProductEquiv_val]
    change conjugateMap (pauli ((syndromeRepresentative S U χ).val+x.val) * L.encoding) =
      (conjugateMap (pauli (syndromeRepresentative S U χ).val * L.encoding)).comp
        (conjugateMap (L.logicalOp ⟨x.val,x.property.1⟩))
    exact L.encoded_add_normalizer _ ⟨x.val,x.property.1⟩
  rw [hf, uniformMap_product (fun χ (x : (Normalizer S ⊓ U : Submodule Bit (Pauli n))) =>
    (L.syndromeEmbedding U χ).map.comp (conjugateMap (L.logicalOp ⟨x.val,x.property.1⟩)))]
  congr 1
  funext χ
  exact (comp_uniformMap (L.syndromeEmbedding U χ).map _).symm

end Stabilizer.Lift
end QecPhysical
