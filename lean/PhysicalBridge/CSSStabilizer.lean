import PhysicalBridge.StabilizerProjector

/-! Constructing a phase-consistent stabilizer lift directly from orthogonal
binary X and Z check spaces. No lift is assumed for this CSS subclass. -/
noncomputable section
namespace QecPhysical.Stabilizer
open scoped BigOperators ComplexOrder
open Matrix
open QecReliability.Binary
open QecPhysical.BinaryPauli

variable {n : ℕ}

def liftOfCrossZero (S : Submodule Bit (Pauli n))
    (h : ∀ s t : S, wordDot s.val.2 t.val.1 = 0) : Lift S where
  op s := pauli s.val
  phase _ := 1
  op_eq_phase _ := by simp
  map_zero := pauli_zero n
  map_add s t := by
    rw [pauli_mul, h s t, bitSign_zero, one_smul]
    rfl
  unitary s := pauli_unitary s.val

/-- Orthogonal X and Z binary check spaces determine a concrete CSS stabilizer group. -/
def cssLift (X Z : Submodule Bit (Word n))
    (hXZ : ∀ x ∈ X, ∀ z ∈ Z, wordDot z x = 0) : Lift (X.prod Z) :=
  liftOfCrossZero (X.prod Z) (fun s t => hXZ t.val.1 t.property.1 s.val.2 s.property.2)

/-- The actual CSS codespace dimension, derived through the concrete Pauli projector. -/
theorem css_codeSpace_finrank (X Z : Submodule Bit (Word n))
    (hXZ : ∀ x ∈ X, ∀ z ∈ Z, wordDot z x = 0) :
    Module.finrank ℂ (cssLift X Z hXZ).codeSpace =
      2 ^ (n - Module.finrank Bit (X.prod Z)) :=
  (cssLift X Z hXZ).codeSpace_finrank_exact

end QecPhysical.Stabilizer
