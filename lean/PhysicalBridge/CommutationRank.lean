import PhysicalBridge.AmbiguityRank

/-! Restricted commutation constraints have exactly the computed restricted
coordinate rank. No independence of the supplied generator rows is required. -/
namespace QecReliability.BinaryElimination
open Binary SharedCircuit Module

def restrictedCommutation {n : ℕ} (rows : List (List (PauliCoord n)))
    (E : Finset (Fin n)) : supported E →ₗ[Bit] (Fin rows.length → Bit) :=
  LinearMap.pi (fun i => ((symplectic n) (decodeRow (rows.get i))).comp (supported E).subtype)

theorem commutation_kernel_iff {n : ℕ} (rows : List (List (PauliCoord n)))
    (E : Finset (Fin n)) (x : supported E) :
    x ∈ LinearMap.ker (restrictedCommutation rows E) ↔
      x.val ∈ normalizer (symplectic n) (rowSpace rows) := by
  rw [mem_normalizer_rows]
  change (fun i => symplectic n (decodeRow (rows.get i)) x.val)=0 ↔ _
  constructor
  · intro h row hr
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hr
    rw [←hi]
    exact congrFun h i
  · intro h
    funext i
    exact h _ (List.get_mem rows i)

def commutationKernelEquiv {n : ℕ} (rows : List (List (PauliCoord n)))
    (E : Finset (Fin n)) : LinearMap.ker (restrictedCommutation rows E) ≃ₗ[Bit]
      localized (symplectic n) (rowSpace rows) (supported E) where
  toFun x := ⟨x.val.val,(commutation_kernel_iff rows E x.val).mp x.property,x.val.property⟩
  invFun x := ⟨⟨x.val,x.property.2⟩,
    (commutation_kernel_iff rows E ⟨x.val,x.property.2⟩).mpr x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restrictedCommutation_rank {n : ℕ} (rows : List (List (PauliCoord n)))
    (E : Finset (Fin n)) :
    finrank Bit (LinearMap.range (restrictedCommutation rows E))=restrictedRank rows E := by
  have h := (restrictedCommutation rows E).finrank_range_add_finrank_ker
  rw [(commutationKernelEquiv rows E).finrank_eq,localized_dimension,
    supported_finrank,←restrictedRank_correct] at h
  have hb := restrictedRank_le_coordinates rows E
  omega

end QecReliability.BinaryElimination
