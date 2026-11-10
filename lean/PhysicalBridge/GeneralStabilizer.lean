import PhysicalBridge.BinaryProducts

/-! A phase-consistent lift constructed from every isotropic binary subspace.
The proof uses a chosen basis, not an additional phase-consistency premise. -/
noncomputable section
namespace QecPhysical.Stabilizer
open scoped BigOperators
open Matrix Module
open QecReliability.Binary
open QecPhysical.BinaryPauli

variable {n : ℕ} {S : Submodule Bit (Pauli n)}
variable {ι : Type*} [Fintype ι] (b : Basis ι Bit S)

def basisFactor (s : S) (i : ι) : Square (Word n) :=
  binaryPower (hermitianPauli (b i).val) (b.repr s i)

def basisOperator (s : S) : Square (Word n) :=
  (Finset.univ.toList.map (basisFactor b s)).prod

omit [Fintype ι] in
theorem basisFactor_add (s t : S) (i : ι) :
    basisFactor b (s+t) i = basisFactor b s i * basisFactor b t i := by
  unfold basisFactor
  rw [map_add, Finsupp.add_apply]
  apply binaryPower_add
  simpa only [(hermitianPauli_hermitian (b i).val).eq] using hermitianPauli_unitary (b i).val

omit [Fintype ι] in
theorem basisFactor_commute (hS : S ≤ QecReliability.normalizer (symplectic n) S)
    (s t : S) (i j : ι) : Commute (basisFactor b s i) (basisFactor b t j) :=
  binaryPower_commute _ _ (isotropic_hermitian_commute S hS (b i) (b j)) _ _

theorem basisOperator_zero : basisOperator b 0 = 1 := by
  have h : basisFactor b 0 = fun _ => 1 := by
    funext i
    simp [basisFactor, binaryPower]
  simp [basisOperator, h]

theorem basisOperator_add (hS : S ≤ QecReliability.normalizer (symplectic n) S) (s t : S) :
    basisOperator b (s+t) = basisOperator b s * basisOperator b t := by
  unfold basisOperator
  have h : basisFactor b (s+t) = fun i => basisFactor b s i * basisFactor b t i :=
    funext (basisFactor_add b s t)
  rw [h]
  exact list_product_mul _ _ _ (basisFactor_commute b hS s t)

theorem basisOperator_unitary (s : S) : (basisOperator b s)ᴴ * basisOperator b s = 1 := by
  apply list_product_unitary
  intro i
  unfold basisFactor binaryPower
  split_ifs
  · simp
  · exact hermitianPauli_unitary _

theorem basisOperator_phase (s : S) : ∃ c : ℂ, basisOperator b s = c • pauli s.val := by
  have h := list_product_pauli_phase Finset.univ.toList (basisFactor b s)
    (fun i => b.repr s i • (b i).val) (fun i => binaryPower_pauli_phase (b i).val (b.repr s i))
  have hs : (∑ i, b.repr s i • (b i).val) = s.val := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using congrArg Subtype.val (b.sum_repr s)
  simpa only [Finset.sum_map_toList, hs, basisOperator] using h

def liftFromBasis (hS : S ≤ QecReliability.normalizer (symplectic n) S) : Lift S where
  op := basisOperator b
  phase s := Classical.choose (basisOperator_phase b s)
  op_eq_phase s := Classical.choose_spec (basisOperator_phase b s)
  map_zero := basisOperator_zero b
  map_add := basisOperator_add b hS
  unitary := basisOperator_unitary b

/-- Every binary isotropic subspace has a phase-consistent Hilbert-space lift. -/
def isotropicLift (S : Submodule Bit (Pauli n))
    (hS : S ≤ QecReliability.normalizer (symplectic n) S) : Lift S :=
  liftFromBasis (Module.finBasis Bit S) hS

theorem isotropic_codeSpace_finrank (S : Submodule Bit (Pauli n))
    (hS : S ≤ QecReliability.normalizer (symplectic n) S) :
    Module.finrank ℂ (isotropicLift S hS).codeSpace = 2 ^ (n - Module.finrank Bit S) :=
  (isotropicLift S hS).codeSpace_finrank_exact

end QecPhysical.Stabilizer
