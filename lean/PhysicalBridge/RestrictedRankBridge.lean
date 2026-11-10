import PhysicalBridge.SparseBinaryRank

/-! The stabilizer-side rank-nullity bridge for exact endpoint acquisition.
This does not yet identify the supported-normalizer dimension. -/
namespace QecReliability.BinaryElimination
open Binary SharedCircuit Module

def maskRestrictedKernelEquiv {n : ℕ} (S : Submodule Bit (Pauli n)) (E : Finset (Fin n)) :
    LinearMap.ker ((mask n E).domRestrict S) ≃ₗ[Bit]
      (S ⊓ LinearMap.ker (mask n E) : Submodule Bit (Pauli n)) where
  toFun x := ⟨x.val.val,x.val.property,x.property⟩
  invFun x := ⟨⟨x.val,x.property.1⟩,x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem mask_rank_nullity {n : ℕ} (S : Submodule Bit (Pauli n)) (E : Finset (Fin n)) :
    finrank Bit (S.map (mask n E))+finrank Bit (S ⊓ supported Eᶜ : Submodule Bit (Pauli n))=
      finrank Bit S := by
  have h := ((mask n E).domRestrict S).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict,(maskRestrictedKernelEquiv S E).finrank_eq,mask_kernel] at h
  exact h

theorem sparse_supported_dimension {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) :
    finrank Bit (rowSpace rows ⊓ supported E : Submodule Bit (Pauli n))=
      sparseRank rows-restrictedRank rows Eᶜ := by
  have h := mask_rank_nullity (rowSpace rows) Eᶜ
  rw [compl_compl,←sparseRank_correct,←restrictedRank_correct] at h
  omega

theorem restrictedRank_le_sparseRank {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) :
    restrictedRank rows E≤sparseRank rows := by
  have h := mask_rank_nullity (rowSpace rows) E
  rw [←sparseRank_correct,←restrictedRank_correct] at h
  omega

end QecReliability.BinaryElimination
