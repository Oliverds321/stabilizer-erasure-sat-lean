import PhysicalBridge.RationalOutputStorage
import PhysicalBridge.PhysicalCachedTails

/-! A direct zero-cause semantic branch. It performs only the existing circuit
evaluation and exact binary-rank score computation, never a SAT cache run.
Compiling this branch to the uniform finite-tape machine remains separate.
-/
set_option autoImplicit false
namespace QecReliability.LatentMachine
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open RationalOutput QecPhysical QecPhysical.Stabilizer

/-- n is unrestricted: zero latent causes does NOT mean zero physical qubits. -/
def zeroLatentOutput {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program 0 n) : Vector 0 :=
  Vector.build (fun _ => Ratio.dyadic rows (circuitMap C ∅))

theorem zeroLatentOutput_entry {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program 0 n) (j : Fin 1) :
    (zeroLatentOutput rows C).get j = Ratio.dyadic rows (circuitMap C ∅) := by
  simp [zeroLatentOutput]

theorem zeroLatentOutput_den {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program 0 n) (j : Fin 1) :
    ((zeroLatentOutput rows C).get j).den =
      2 ^ BinaryElimination.ambiguityRank rows (circuitMap C ∅) := by
  rw [zeroLatentOutput_entry]
  rfl

theorem zeroLatentOutput_curve {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program 0 n) (p : ℝ) :
    (zeroLatentOutput rows C).curve p = score (rowSpace rows) (circuitMap C ∅) := by
  simp [Vector.curve, zeroLatentOutput, bernsteinCurve, average, bernsteinWeight,
    Ratio.dyadic_value]

theorem zeroLatentOutput_payload {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program 0 n) (j : Fin 1) :
    ((zeroLatentOutput rows C).get j).payload ≤ 2 * (2 ^ (2*n)).size := by
  apply Ratio.payload_le
  rw [zeroLatentOutput_den]
  exact Nat.pow_le_pow_right (by omega) (ambiguityRank_le rows (circuitMap C ∅))

end QecReliability.LatentMachine
