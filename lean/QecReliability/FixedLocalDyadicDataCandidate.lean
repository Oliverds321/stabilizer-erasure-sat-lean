import QecReliability.FixedLocalEncoderClosureCandidate
import DyadicEncoderDataCandidate

/-!


Its direct adapter import is `DyadicEncoderDataCandidate`.

This fills that adapter's semantic/circuit data from the actual same-certificate
emitter and recursive constructor. It does NOT prove finite-machine generation.
-/

set_option autoImplicit false
noncomputable section
namespace QecReliability.SharedCircuit.FixedLocalEmitter
open CodeHash EncoderSemantics SerializedDyadicEncoder
open FiniteLocalSelectorCandidate

/-- No caller-supplied encoder family or encoder-distance property. Every field
is the projection of the one actually defined same-certificate recursive code. -/
def concreteDyadicData {D t : Nat} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) : UniformAdapter.DyadicXorData where
  base := 64 * D
  base_pos := Nat.mul_pos (by decide) (FixedWitnessEncoder.degree_pos hD)
  base_four := ⟨16 * D, by ring⟩
  num := 1
  den := 16777216
  gateConstant := 2 * D
  num_pos := by decide
  num_le_den := by decide
  encoder ell := (concreteExactEncoder hD hd A ell).toLinear
  program ell := (concreteExactEncoder hD hd A ell).toProgram
  xorOnly ell := XorCircuit.toCircuit_xorOnly _
  correct ell x i :=
    (congrFun ((concreteExactEncoder hD hd A ell).toLinear_bool x) i).symm
  distance ell x hx := by
    simpa only [alpha, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
      concreteExactEncoder_distance hD hd A ell x hx
  gates_le ell := concreteExactEncoder_gates hD hd A ell

/-- Literal program projection, not just semantic equality. -/
@[simp] theorem concreteDyadicData_program {D t : Nat} (hD : D = 16 ^ 384)
    (hd : D = 256 * t) (A : CertifiedParity (512 * t) (64 * t) t) (ell : Nat) :
    (concreteDyadicData hD hd A).program ell =
      (concreteExactEncoder hD hd A ell).toProgram := rfl

/-- The adapter's once-shifted data still call this SAME emitter at ell+1. -/
theorem concreteDyadicData_shift_program {D t : Nat} (hD : D = 16 ^ 384)
    (hd : D = 256 * t) (A : CertifiedParity (512 * t) (64 * t) t) (ell : Nat) :
    (concreteDyadicData hD hd A).shift.program ell =
      (concreteDyadicData hD hd A).shiftedProgram ell := rfl

/-- Symbolic certificate dimensions avoid closed-numeral normalization. -/
theorem exists_concreteDyadicData_generic {D t : Nat}
    (hD : D = 16 ^ 384) (hd : D = 256 * t) (ht : 0 < t) :
    ∃ A : CertifiedParity (512 * t) (64 * t) t,
    ∃ X : UniformAdapter.DyadicXorData,
      X = concreteDyadicData hD hd A := by
  obtain ⟨A⟩ := ExpanderWalk.FixedWitnessSparseAmplifier.exists_certificate t ht
  exact ⟨A, concreteDyadicData hD hd A, rfl⟩

/-- Existence only, with one certificate before the entire data/program family.
No semantic family is accepted from the caller, but no machine is concluded. -/
theorem exists_one_fixed_concreteDyadicData :
    ∃ A : CertifiedParity (512 * 2 ^ 1528) (64 * 2 ^ 1528) (2 ^ 1528),
    ∃ X : UniformAdapter.DyadicXorData,
      X = concreteDyadicData (D := 16 ^ 384) rfl
        FiniteLocalCountingCandidate.fixed_degree_reparametrization A := by
  exact exists_concreteDyadicData_generic rfl
    FiniteLocalCountingCandidate.fixed_degree_reparametrization
    (pow_pos (by decide : 0 < (2 : Nat)) _)

end QecReliability.SharedCircuit.FixedLocalEmitter
