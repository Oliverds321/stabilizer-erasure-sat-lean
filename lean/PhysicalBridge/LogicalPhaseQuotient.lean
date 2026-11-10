import PhysicalBridge.LogicalResolution
import PhysicalBridge.ScalarUnitary

/-! Logical conjugation channels descend to normalizer cosets. Equality up
to phase is proved explicitly, so representative choices do not alter noise. -/
noncomputable section
namespace QecPhysical.Stabilizer
open scoped BigOperators
open Matrix Module
open QecReliability.Binary
open QecPhysical.BinaryPauli
variable {n : ℕ} {S : Submodule Bit (Pauli n)}

theorem logicalClass_eq_iff (e f : Normalizer S) :
    (stabilizerInNormalizer S).mkQ e = (stabilizerInNormalizer S).mkQ f ↔ e.val+f.val ∈ S := by
  change Submodule.Quotient.mk e = Submodule.Quotient.mk f ↔ _
  rw [Submodule.Quotient.eq]
  change e.val-f.val ∈ S ↔ _
  have hneg : -f.val = f.val := (eq_neg_of_add_eq_zero_left (pauliLabel_add_self f.val)).symm
  simp only [sub_eq_add_neg, hneg]

namespace Lift
variable (L : Lift S)

theorem logicalOp_stabilizer_scalar (e : Normalizer S) (he : e.val ∈ S) :
    ∃ c : ℂ, L.logicalOp e = c • (1 : Square L.LogicalIndex) := by
  let s : S := ⟨e.val, he⟩
  have h := congrArg (fun A => L.encodingᴴ * A) (L.encoding_intertwines s)
  rw [L.op_eq_phase, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc,
    L.encoding_isometry] at h
  change L.phase s • L.logicalOp e = 1 at h
  refine ⟨(L.phase s)⁻¹, ?_⟩
  have hi := congrArg (fun A : Square L.LogicalIndex => (L.phase s)⁻¹ • A) h
  simpa only [smul_smul, inv_mul_cancel₀ (L.phase_ne_zero s), one_smul] using hi

theorem logicalOp_same_class_scalar (e f : Normalizer S)
    (h : (stabilizerInNormalizer S).mkQ e = (stabilizerInNormalizer S).mkQ f) :
    ∃ c : ℂ, L.logicalOp e = c • L.logicalOp f := by
  let s : Normalizer S := e+f
  have hsS : s.val ∈ S := (logicalClass_eq_iff e f).mp h
  obtain ⟨c, hc⟩ := L.logicalOp_stabilizer_scalar s hsS
  have hs : s+f=e := by
    apply Subtype.ext
    change (e.val+f.val)+f.val=e.val
    simp [add_assoc]
  have hp := L.logicalOp_mul s f
  rw [hc, Matrix.smul_mul, Matrix.one_mul, hs] at hp
  let b := bitSign (wordDot s.val.2 f.val.1)
  refine ⟨b*c, ?_⟩
  have hi := congrArg (fun A : Square L.LogicalIndex => b • A) hp
  simpa only [smul_smul, b, bitSign_square, one_smul] using hi.symm

theorem logicalOp_same_class_channel (e f : Normalizer S)
    (h : (stabilizerInNormalizer S).mkQ e = (stabilizerInNormalizer S).mkQ f) :
    conjugateMap (L.logicalOp e) = conjugateMap (L.logicalOp f) := by
  obtain ⟨c, hc⟩ := L.logicalOp_same_class_scalar e f h
  exact unitary_same_channel_of_smul _ _ (L.logicalOp_unitary f) (L.logicalOp_unitary e) c hc

theorem logicalOp_class_channel (e : Normalizer S) :
    conjugateMap (L.logicalOp e) =
      conjugateMap (L.logicalClassOp ((stabilizerInNormalizer S).mkQ e)) := by
  apply L.logicalOp_same_class_channel
  rw [logicalRepresentative_class]

end Lift
end QecPhysical.Stabilizer
