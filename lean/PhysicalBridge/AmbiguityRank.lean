import PhysicalBridge.RestrictedRankBridge
import PhysicalBridge.CoordinateSplit

/-! Exact ambiguity from computed binary row ranks, with grouped natural
subtraction. No isotropy is needed for the dimension equalities; isotropy
ensures the final difference has its intended nonnegative quotient meaning. -/
namespace QecReliability.BinaryElimination
open Binary SharedCircuit Module

theorem supported_finrank {n : ℕ} (E : Finset (Fin n)) : finrank Bit (supported E)=2*E.card := by
  have h := Nat.card_congr (QecPhysical.BinaryPauli.supportedLabelEquiv E)
  have hp : Nat.card (Pauli (Fintype.card E))=2^(2*E.card) := by
    rw [Module.natCard_eq_pow_finrank (K:=Bit)]
    simp [two_mul]
  have hs : Nat.card (supported E)=2^finrank Bit (supported E) := by
    rw [Module.natCard_eq_pow_finrank (K:=Bit)]
    simp
  rw [hp,hs] at h
  exact (Nat.pow_right_injective (by omega : 2≤2) h).symm

theorem localized_dimension {n : ℕ} (S : Submodule Bit (Pauli n)) (E : Finset (Fin n)) :
    finrank Bit (localized (symplectic n) S (supported E))=
      2*E.card-finrank Bit (S.map (mask n E)) := by
  have hs := Submodule.finrank_sup_add_finrank_inf_eq S (supported Eᶜ)
  have hm := mask_rank_nullity S E
  have ho := finrank_normalizer (S ⊔ supported Eᶜ)
  have he : normalizer (symplectic n) (S ⊔ supported Eᶜ)=localized (symplectic n) S (supported E) := by
    rw [normalizer,orthogonal_sup,orthogonal_supported,compl_compl]
    rfl
  rw [he] at ho
  rw [supported_finrank] at hs
  have hcard : E.card+Eᶜ.card=n := by simp
  have hle : finrank Bit (S ⊔ supported Eᶜ : Submodule Bit (Pauli n))≤2*n := by
    simpa [two_mul] using Submodule.finrank_le (S ⊔ supported Eᶜ : Submodule Bit (Pauli n))
  omega

theorem restrictedRank_le_coordinates {n : ℕ} (rows : List (List (PauliCoord n)))
    (E : Finset (Fin n)) : restrictedRank rows E≤2*E.card := by
  rw [restrictedRank_correct,←supported_finrank E]
  apply Submodule.finrank_mono
  rintro x ⟨y,_,rfl⟩
  intro i hi
  simp [mask,hi]

def ambiguityRank {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) : ℕ :=
  (2*E.card-restrictedRank rows E)-(sparseRank rows-restrictedRank rows Eᶜ)

theorem ambiguityRank_correct {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) :
    ambiguityRank rows E=ambiguity (symplectic n) (rowSpace rows) (supported E) := by
  rw [ambiguityRank,ambiguity,localized_dimension,sparse_supported_dimension,restrictedRank_correct]

theorem ambiguity_subtraction_safe {n : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows≤normalizer (symplectic n) (rowSpace rows)) (E : Finset (Fin n)) :
    sparseRank rows-restrictedRank rows Eᶜ≤2*E.card-restrictedRank rows E := by
  rw [←sparse_supported_dimension,restrictedRank_correct,←localized_dimension]
  exact Submodule.finrank_mono (fun x hx => ⟨hS hx.1,hx.2⟩)

end QecReliability.BinaryElimination
