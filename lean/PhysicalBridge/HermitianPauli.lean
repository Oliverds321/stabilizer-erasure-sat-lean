import PhysicalBridge.PauliTrace

/-! A Hermitian unitary representative of each binary Pauli label. Choosing
these representatives individually does not assert group consistency. -/
noncomputable section
namespace QecPhysical.BinaryPauli
open scoped BigOperators ComplexOrder
open Matrix
open QecReliability.Binary

def hermitianPhase (b : Bit) : ℂ := if b = 0 then 1 else Complex.I

theorem hermitianPhase_norm (b : Bit) : star (hermitianPhase b) * hermitianPhase b = 1 := by
  fin_cases b <;> norm_num [hermitianPhase, Complex.star_def]

theorem hermitianPhase_adjoint (b : Bit) :
    star (hermitianPhase b) * bitSign b = hermitianPhase b := by
  fin_cases b <;> norm_num [hermitianPhase, bitSign, Complex.star_def]

def hermitianPauli {n : ℕ} (u : Pauli n) : Square (Word n) :=
  hermitianPhase (wordDot u.2 u.1) • pauli u

theorem hermitianPauli_hermitian {n : ℕ} (u : Pauli n) : (hermitianPauli u).IsHermitian := by
  change (hermitianPauli u)ᴴ = hermitianPauli u
  rw [hermitianPauli, Matrix.conjTranspose_smul, pauli_adjoint, smul_smul, hermitianPhase_adjoint]

theorem hermitianPauli_unitary {n : ℕ} (u : Pauli n) :
    (hermitianPauli u)ᴴ * hermitianPauli u = 1 := by
  rw [hermitianPauli, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, pauli_unitary, hermitianPhase_norm, one_smul]

theorem hermitianPauli_commute {n : ℕ} (u v : Pauli n) (h : symplectic n u v = 0) :
    Commute (hermitianPauli u) (hermitianPauli v) := by
  change hermitianPauli u * hermitianPauli v = hermitianPauli v * hermitianPauli u
  simp only [hermitianPauli, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [(pauli_commute_of_symplectic_zero u v h).eq]
  congr 1
  ring

theorem isotropic_hermitian_commute {n : ℕ} (S : Submodule Bit (Pauli n))
    (hS : S ≤ QecReliability.normalizer (symplectic n) S) (u v : S) :
    Commute (hermitianPauli u.val) (hermitianPauli v.val) := by
  apply hermitianPauli_commute
  exact hS v.property u.val u.property

end QecPhysical.BinaryPauli
