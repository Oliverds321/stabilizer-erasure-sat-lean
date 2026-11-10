import PhysicalBridge.SyndromeCharacters

/-! All syndrome projectors, indexed by binary character coordinates, resolve
the physical identity. This is derived from finite character cancellation. -/
noncomputable section
namespace QecPhysical.Stabilizer
open scoped BigOperators
open Matrix Module
open QecReliability.Binary
open QecPhysical.BinaryPauli
variable {n r : ℕ} {S : Submodule Bit (Pauli n)}

def basisCharacter (b : Basis (Fin r) Bit S) (a : Word r) : S →ₗ[Bit] Bit :=
  ∑ i, a i • b.coord i

theorem basisCharacter_apply (b : Basis (Fin r) Bit S) (a : Word r) (s : S) :
    basisCharacter b a s = wordDot a (fun i => b.repr s i) := by
  simp [basisCharacter, wordDot, Basis.coord]

theorem basisCharacter_basis (b : Basis (Fin r) Bit S) (a : Word r) (i : Fin r) :
    basisCharacter b a (b i) = a i := by
  simp [basisCharacter_apply, wordDot, Finsupp.single_apply]

theorem basisCharacter_injective (b : Basis (Fin r) Bit S) :
    Function.Injective (basisCharacter b) := by
  intro a c h
  funext i
  have hi := congrArg (fun χ : S →ₗ[Bit] Bit => χ (b i)) h
  simpa only [basisCharacter_basis] using hi

theorem basisCharacter_surjective (b : Basis (Fin r) Bit S) :
    Function.Surjective (basisCharacter b) := by
  intro χ
  refine ⟨fun i => χ (b i), ?_⟩
  apply b.ext
  intro i
  exact basisCharacter_basis b _ i

theorem basisCharacter_sum (b : Basis (Fin r) Bit S) (s : S) :
    (∑ a : Word r, bitSign (basisCharacter b a s)) =
      if s=0 then (Fintype.card (Word r) : ℂ) else 0 := by
  have hs : (fun i => b.repr s i) = 0 ↔ s=0 := by
    constructor
    · intro h
      apply b.repr.injective
      ext i
      simpa using congrFun h i
    · intro h
      subst s
      funext i
      simp
  have hterm (a : Word r) : bitSign (basisCharacter b a s) =
      bitSign (wordDot (fun i => b.repr s i) a) := by
    rw [basisCharacter_apply, wordDot_comm]
  simp only [hterm]
  rw [character_sum]
  simp only [hs]

theorem basis_card_eq (b : Basis (Fin r) Bit S) : Fintype.card S = Fintype.card (Word r) := by
  rw [Lift.index_card, card_word, Module.finrank_eq_card_basis b, Fintype.card_fin]

namespace Lift
variable (L : Lift S)

theorem syndrome_projectors_sum (b : Basis (Fin r) Bit S) :
    ∑ a : Word r, (L.twist (basisCharacter b a)).projector = 1 := by
  classical
  simp only [projector, twist]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have hsum (s : S) :
      (∑ a : Word r, bitSign (basisCharacter b a s) • L.op s) =
        (if s=0 then (Fintype.card S : ℂ) else 0) • L.op s := by
    rw [← Finset.sum_smul, basisCharacter_sum, ← basis_card_eq b]
  simp_rw [hsum]
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, L.map_zero]
  rw [smul_smul, inv_mul_cancel₀ (card_ne_zero (S := S)), one_smul]

theorem syndrome_projectors_orthogonal (b : Basis (Fin r) Bit S) (a c : Word r) (h : a≠c) :
    (L.twist (basisCharacter b a)).projector * (L.twist (basisCharacter b c)).projector = 0 :=
  L.twist_projectors_orthogonal _ _ (fun he => h (basisCharacter_injective b he))

end Lift
end QecPhysical.Stabilizer
