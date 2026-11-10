import PhysicalBridge.GeneralStabilizer

/-! Character twists and the actual stabilizer eigenspace projectors. -/
noncomputable section
namespace QecPhysical.Stabilizer
open scoped BigOperators
open Matrix Module
open QecReliability.Binary
open QecPhysical.BinaryPauli
variable {n : ℕ} {S : Submodule Bit (Pauli n)}

theorem bitSign_injective : Function.Injective bitSign := by
  intro a b h
  have hc : bitSign (a+b) = 1 := by rw [bitSign_add, h, bitSign_square]
  have hab := (bitSign_eq_one_iff (a+b)).mp hc
  calc
    a = (a+b)+b := by simp [add_assoc, CharTwo.add_self_eq_zero]
    _ = b := by rw [hab, zero_add]

namespace Lift
variable (L : Lift S)

def twist (χ : S →ₗ[Bit] Bit) : Lift S where
  op s := bitSign (χ s) • L.op s
  phase s := bitSign (χ s) * L.phase s
  op_eq_phase s := by rw [L.op_eq_phase, smul_smul]
  map_zero := by simp [L.map_zero]
  map_add s t := by
    simp only [χ.map_add, L.map_add, bitSign_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    ring
  unitary s := by
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      bitSign_star, bitSign_square, L.unitary, one_smul]

theorem twist_projector_left (χ : S →ₗ[Bit] Bit) (s : S) :
    L.op s * (L.twist χ).projector = bitSign (χ s) • (L.twist χ).projector := by
  have h := congrArg (fun M : Square (Word n) => bitSign (χ s) • M)
    ((L.twist χ).projector_left_fixed s)
  change bitSign (χ s) • ((bitSign (χ s) • L.op s) * (L.twist χ).projector) = _ at h
  simpa only [Matrix.smul_mul, smul_smul, bitSign_square, one_smul] using h

theorem twist_projector_right (χ : S →ₗ[Bit] Bit) (s : S) :
    (L.twist χ).projector * L.op s = bitSign (χ s) • (L.twist χ).projector := by
  have h := congrArg Matrix.conjTranspose (L.twist_projector_left χ s)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul,
    (L.twist χ).projector_hermitian.eq, (L.operator_hermitian s).eq, bitSign_star] using h

theorem twist_projectors_orthogonal (χ ψ : S →ₗ[Bit] Bit) (hne : χ ≠ ψ) :
    (L.twist χ).projector * (L.twist ψ).projector = 0 := by
  obtain ⟨s, hs⟩ : ∃ s, χ s ≠ ψ s := by
    by_contra h
    apply hne
    ext s
    by_contra hs
    exact h ⟨s, hs⟩
  have hsign : bitSign (χ s) ≠ bitSign (ψ s) := fun h => hs (bitSign_injective h)
  have h : bitSign (χ s) • ((L.twist χ).projector * (L.twist ψ).projector) =
      bitSign (ψ s) • ((L.twist χ).projector * (L.twist ψ).projector) := by
    rw [← Matrix.smul_mul, ← L.twist_projector_right χ s, Matrix.mul_assoc,
      L.twist_projector_left ψ s, Matrix.mul_smul]
  have hz : (bitSign (χ s) - bitSign (ψ s)) •
      ((L.twist χ).projector * (L.twist ψ).projector) = 0 := by
    rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hsign)

end Lift
end QecPhysical.Stabilizer
