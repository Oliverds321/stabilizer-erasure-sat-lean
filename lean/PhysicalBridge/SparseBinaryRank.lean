import PhysicalBridge.BinaryMatrixRank
import QecReliability.SparseGenerators

/-! Actual elimination of the source sparse Pauli rows. decodeRow sums entries
in F2, so duplicate indices cancel and redundant generator rows remain valid. -/
namespace QecReliability.BinaryElimination
open Binary SharedCircuit Module

def flatten (n : ℕ) : Pauli n ≃ₗ[Bit] Row (n+n) where
  toFun x := Fin.addCases x.1 x.2
  invFun x := (fun i => x (Fin.castAdd n i),fun i => x (Fin.natAdd n i))
  left_inv x := by
    apply Prod.ext <;> funext i
    · change Fin.addCases x.1 x.2 (Fin.castAdd n i)=x.1 i
      exact Fin.addCases_left i
    · change Fin.addCases x.1 x.2 (Fin.natAdd n i)=x.2 i
      exact Fin.addCases_right i
  right_inv x := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Fin.addCases_left,Fin.addCases_right]
  map_add' x y := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Fin.addCases_left,Fin.addCases_right,Prod.fst_add,Prod.snd_add,Pi.add_apply]
  map_smul' c x := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left,Pi.smul_apply]
      rfl
    · simp only [Fin.addCases_right,Pi.smul_apply]
      rfl

def decodedRows {n : ℕ} (rows : List (List (PauliCoord n))) : List (Row (n+n)) :=
  rows.map (fun row => cacheRow (flatten n (decodeRow row)))

def sparseRank {n : ℕ} (rows : List (List (PauliCoord n))) : ℕ := rank (n+n) (decodedRows rows)

theorem decodedRows_span {n : ℕ} (rows : List (List (PauliCoord n))) :
    spanRows (decodedRows rows)=(rowSpace rows).map (flatten n).toLinearMap := by
  unfold spanRows rowSpace
  rw [Submodule.map_span]
  congr 1
  ext x
  simp [decodedRows]

theorem sparseRank_correct {n : ℕ} (rows : List (List (PauliCoord n))) :
    sparseRank rows=finrank Bit (rowSpace rows) := by
  rw [sparseRank,rank_correct,decodedRows_span,LinearEquiv.finrank_map_eq]

def mask (n : ℕ) (E : Finset (Fin n)) : Pauli n →ₗ[Bit] Pauli n where
  toFun x := (fun i => if i∈E then x.1 i else 0,fun i => if i∈E then x.2 i else 0)
  map_add' x y := by
    apply Prod.ext <;> funext i <;> by_cases h : i∈E <;> simp [h]
  map_smul' c x := by
    apply Prod.ext <;> funext i <;> by_cases h : i∈E <;> simp [h]

/-- Zero-padding unselected columns retains the original explicit 2n-column layout. -/
def restrictedRows {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) :
    List (Row (n+n)) := rows.map (fun row => cacheRow (flatten n (mask n E (decodeRow row))))

def restrictedRank {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) : ℕ :=
  rank (n+n) (restrictedRows rows E)

theorem restrictedRows_span {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) :
    spanRows (restrictedRows rows E)=((rowSpace rows).map (mask n E)).map (flatten n).toLinearMap := by
  unfold spanRows rowSpace
  rw [Submodule.map_span,Submodule.map_span]
  congr 1
  ext x
  simp [restrictedRows]

theorem restrictedRank_correct {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) :
    restrictedRank rows E=finrank Bit ((rowSpace rows).map (mask n E)) := by
  rw [restrictedRank,rank_correct,restrictedRows_span,LinearEquiv.finrank_map_eq]

theorem mask_kernel (n : ℕ) (E : Finset (Fin n)) : LinearMap.ker (mask n E)=supported Eᶜ := by
  ext x
  constructor
  · intro hx i hi
    have hiE : i∈E := by simpa using hi
    have h := congrArg (fun y : Pauli n => (y.1 i,y.2 i)) hx
    simpa [mask,hiE] using h
  · intro hx
    change mask n E x=0
    apply Prod.ext <;> funext i <;> by_cases hi : i∈E
    · simp [mask,hi,(hx i (by simpa using hi)).1]
    · simp [mask,hi]
    · simp [mask,hi,(hx i (by simpa using hi)).2]
    · simp [mask,hi]

theorem decodeRow_double_entry {n : ℕ} (i : PauliCoord n) (row : List (PauliCoord n)) :
    decodeRow (i::i::row)=decodeRow row := by
  simp only [decodeRow,List.map_cons,List.sum_cons]
  have h : coordPauli i+coordPauli i=0 := by
    apply Prod.ext <;> funext j <;> exact CharTwo.add_self_eq_zero _
  rw [←add_assoc,h,zero_add]

end QecReliability.BinaryElimination
