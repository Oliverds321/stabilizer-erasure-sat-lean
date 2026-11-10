import PhysicalBridge.SyndromeResolution

/-! Physical Pauli errors shift the constructed stabilizer syndrome projectors.
The syndrome is derived from the binary symplectic pairing. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace QecPhysical.Stabilizer
open scoped BigOperators
open Matrix Module
open QecReliability.Binary
open QecPhysical.BinaryPauli
variable {n : ℕ} {S : Submodule Bit (Pauli n)}

def errorCharacter (S : Submodule Bit (Pauli n)) (e : Pauli n) : S →ₗ[Bit] Bit :=
  ((symplectic n).flip e).comp S.subtype

theorem errorCharacter_apply (e : Pauli n) (s : S) :
    errorCharacter S e s = symplectic n s.val e := rfl

def errorCoordinates {r : ℕ} (b : Basis (Fin r) Bit S) (e : Pauli n) : Word r :=
  fun i => symplectic n (b i).val e

theorem basisCharacter_errorCoordinates {r : ℕ} (b : Basis (Fin r) Bit S) (e : Pauli n) :
    basisCharacter b (errorCoordinates b e) = errorCharacter S e := by
  apply b.ext
  intro i
  rw [basisCharacter_basis]
  rfl

theorem pauli_unitary_right (e : Pauli n) : pauli e * (pauli e)ᴴ = 1 := by
  rw [pauli_adjoint, Matrix.mul_smul, pauli_mul, smul_smul]
  simp

namespace Lift
variable (L : Lift S)

theorem operator_pauli_commutation (s : S) (e : Pauli n) :
    L.op s * pauli e = bitSign (errorCharacter S e s) • (pauli e * L.op s) := by
  rw [L.op_eq_phase, Matrix.smul_mul, pauli_commutation, Matrix.mul_smul, smul_smul, smul_smul]
  change (L.phase s * bitSign (symplectic n s.val e)) • _ =
    (bitSign (symplectic n s.val e) * L.phase s) • _
  rw [mul_comm (L.phase s)]

theorem pauli_projector_intertwine (χ : S →ₗ[Bit] Bit) (e : Pauli n) :
    pauli e * (L.twist χ).projector =
      (L.twist (χ + errorCharacter S e)).projector * pauli e := by
  unfold projector
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  change pauli e * (bitSign (χ s) • L.op s) =
    (bitSign ((χ + errorCharacter S e) s) • L.op s) * pauli e
  rw [Matrix.mul_smul, Matrix.smul_mul, L.operator_pauli_commutation]
  simp only [LinearMap.add_apply, bitSign_add, smul_smul]
  rw [mul_assoc, bitSign_square, mul_one]

theorem pauli_projector_conjugate (χ : S →ₗ[Bit] Bit) (e : Pauli n) :
    pauli e * (L.twist χ).projector * (pauli e)ᴴ =
      (L.twist (χ + errorCharacter S e)).projector := by
  rw [L.pauli_projector_intertwine, Matrix.mul_assoc, pauli_unitary_right, Matrix.mul_one]

theorem twist_zero_projector : (L.twist 0).projector = L.projector := by
  simp [projector, twist]

theorem projector_encoding : L.projector * L.encoding = L.encoding := by
  rw [← L.encoding_projector, Matrix.mul_assoc, L.encoding_isometry, Matrix.mul_one]

theorem error_encoding_fixed (e : Pauli n) :
    (L.twist (errorCharacter S e)).projector * (pauli e * L.encoding) =
      pauli e * L.encoding := by
  have h := L.pauli_projector_intertwine 0 e
  rw [L.twist_zero_projector, zero_add] at h
  rw [← Matrix.mul_assoc, ← h, Matrix.mul_assoc, L.projector_encoding]

theorem error_encoding_block (χ : S →ₗ[Bit] Bit) (e : Pauli n) :
    (L.twist χ).projector * (pauli e * L.encoding) =
      if χ = errorCharacter S e then pauli e * L.encoding else 0 := by
  classical
  by_cases h : χ = errorCharacter S e
  · rw [if_pos h, h, L.error_encoding_fixed]
  · rw [if_neg h, ← L.error_encoding_fixed e, ← Matrix.mul_assoc,
      L.twist_projectors_orthogonal χ _ h, Matrix.zero_mul]

end Lift
end QecPhysical.Stabilizer
