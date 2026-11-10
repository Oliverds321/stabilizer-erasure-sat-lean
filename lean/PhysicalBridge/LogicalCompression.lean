import PhysicalBridge.SyndromeMixture

/-! Normalizer Paulis have explicitly intertwined unitary coordinates in the
codespace. No canonical tensor-Pauli identification of this basis is assumed. -/
noncomputable section
namespace QecPhysical.Stabilizer
open scoped BigOperators
open Matrix Module
open QecReliability.Binary
open QecPhysical.BinaryPauli
variable {n : ℕ} {S : Submodule Bit (Pauli n)}

abbrev Normalizer (S : Submodule Bit (Pauli n)) := QecReliability.normalizer (symplectic n) S

theorem errorCharacter_eq_zero_iff (e : Pauli n) : errorCharacter S e = 0 ↔ e ∈ Normalizer S := by
  constructor
  · intro h s hs
    have he := congrArg (fun χ : S →ₗ[Bit] Bit => χ ⟨s, hs⟩) h
    exact he
  · intro h
    ext s
    exact h s.val s.property

namespace Lift
variable (L : Lift S)

abbrev LogicalIndex := Fin (finrank ℂ L.hilbertCodeSpace)

def logicalOp (e : Normalizer S) : Square L.LogicalIndex :=
  L.encodingᴴ * pauli e.val * L.encoding

theorem normalizer_encoding_fixed (e : Normalizer S) :
    L.projector * (pauli e.val * L.encoding) = pauli e.val * L.encoding := by
  have h := L.error_encoding_fixed e.val
  rw [(errorCharacter_eq_zero_iff e.val).mpr e.property, L.twist_zero_projector] at h
  exact h

/-- The actual physical/logical intertwining identity for the chosen isometry. -/
theorem logicalOp_intertwine (e : Normalizer S) :
    L.encoding * L.logicalOp e = pauli e.val * L.encoding := by
  unfold logicalOp
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, L.encoding_projector, Matrix.mul_assoc]
  exact L.normalizer_encoding_fixed e

theorem logicalOp_unitary (e : Normalizer S) : (L.logicalOp e)ᴴ * L.logicalOp e = 1 := by
  have h := congrArg (fun A => Aᴴ * A) (L.logicalOp_intertwine e)
  have he := L.errorEncoding_isometry e.val
  change (pauli e.val * L.encoding)ᴴ * (pauli e.val * L.encoding) = 1 at he
  rw [he] at h
  simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc L.encodingᴴ L.encoding,
    L.encoding_isometry, Matrix.one_mul] using h

theorem logicalOp_zero : L.logicalOp 0 = 1 := by
  simp only [logicalOp, ZeroMemClass.coe_zero, pauli_zero, Matrix.mul_one, L.encoding_isometry]

theorem logicalOp_mul (e f : Normalizer S) :
    L.logicalOp e * L.logicalOp f =
      bitSign (wordDot e.val.2 f.val.1) • L.logicalOp (e+f) := by
  calc
    _ = L.encodingᴴ * pauli e.val * (L.encoding * L.logicalOp f) := by
      simp only [logicalOp, Matrix.mul_assoc]
    _ = L.encodingᴴ * (pauli e.val * pauli f.val) * L.encoding := by
      rw [L.logicalOp_intertwine]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [pauli_mul, Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem logicalOp_adjoint (e : Normalizer S) :
    (L.logicalOp e)ᴴ = bitSign (wordDot e.val.2 e.val.1) • L.logicalOp e := by
  simp only [logicalOp, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    pauli_adjoint, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

theorem logicalOp_trace (e : Normalizer S) :
    (L.logicalOp e).trace = (pauli e.val * L.projector).trace := by
  rw [logicalOp, Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  rw [L.encoding_projector]

theorem logicalOp_trace_zero (e : Normalizer S) (he : e.val ∉ S) : (L.logicalOp e).trace = 0 := by
  rw [L.logicalOp_trace, projector, Matrix.mul_smul, Matrix.mul_sum,
    Matrix.trace_smul, Matrix.trace_sum]
  have hzero (s : S) : (pauli e.val * L.op s).trace = 0 := by
    rw [L.op_eq_phase, Matrix.mul_smul, pauli_mul, smul_smul, Matrix.trace_smul, pauli_trace]
    have hne : e.val + s.val ≠ 0 := by
      intro h
      have heq : e.val = s.val := by
        calc
          e.val = (e.val+s.val)+s.val := by simp [add_assoc]
          _ = s.val := by rw [h, zero_add]
      exact he (heq ▸ s.property)
    rw [if_neg hne, smul_zero]
  simp only [hzero, Finset.sum_const_zero, smul_zero]

theorem logicalOp_trace_inner_zero (e f : Normalizer S) (h : e.val+f.val ∉ S) :
    ((L.logicalOp e)ᴴ * L.logicalOp f).trace = 0 := by
  rw [L.logicalOp_adjoint, Matrix.smul_mul, L.logicalOp_mul, smul_smul, Matrix.trace_smul,
    L.logicalOp_trace_zero (e+f) h, smul_zero]

end Lift
end QecPhysical.Stabilizer
