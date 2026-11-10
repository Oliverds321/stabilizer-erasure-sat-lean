import PhysicalBridge.PauliTrace
import PhysicalBridge.TraceResolution

/-! A complete operator resolution for the same binary-labelled Paulis used
by the stabilizer and coordinate-erasure constructions. -/
noncomputable section
namespace QecPhysical.BinaryPauli
open Matrix
open QecReliability.Binary

theorem pauli_trace_inner {n : ℕ} (u v : Pauli n) :
    ((pauli u)ᴴ * pauli v).trace = if u=v then (Fintype.card (Word n) : ℂ) else 0 := by
  by_cases h : u=v
  · subst v
    simp [pauli_unitary]
  · have huv : u+v ≠ 0 := by
      intro hz
      have hh := congrArg (fun t : Pauli n => t+v) hz
      simp only [add_assoc, pauliLabel_add_self, add_zero, zero_add] at hh
      exact h hh
    rw [pauli_adjoint, Matrix.smul_mul, pauli_mul, smul_smul, Matrix.trace_smul,
      pauli_trace]
    simp [h, huv]

def binaryResolution (n : ℕ) : UnitaryResolution (Word n) (Pauli n) :=
  UnitaryResolution.ofTraceOrthogonal pauli pauli_unitary
    (Fintype.card_prod _ _) pauli_trace_inner

end QecPhysical.BinaryPauli
