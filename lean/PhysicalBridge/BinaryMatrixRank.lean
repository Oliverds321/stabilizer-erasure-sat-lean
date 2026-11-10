import PhysicalBridge.BinaryElimination
import Mathlib.LinearAlgebra.Matrix.Rank

/-! A computable binary matrix rank, proved equal to mathlib's semantic rank. -/
namespace QecReliability.BinaryElimination
open Binary Module

def matrixRank {m n : ℕ} (A : Matrix (Fin m) (Fin n) Bit) : ℕ :=
  rank n ((List.ofFn A).map (fun x => cacheRow x))

theorem matrixRank_correct {m n : ℕ} (A : Matrix (Fin m) (Fin n) Bit) :
    matrixRank A=A.rank := by
  have hs : spanRows ((List.ofFn A).map (fun x => cacheRow x))=
      Submodule.span Bit (Set.range A.row) := by
    unfold spanRows
    apply congrArg (Submodule.span Bit)
    ext x
    change x ∈ (List.ofFn (fun i => A i)).map (fun y => cacheRow y) ↔ ∃ i, A i = x
    constructor
    · intro hx
      obtain ⟨y, hy, he⟩ := List.mem_map.mp hx
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hy
      exact ⟨i, hi.trans ((cacheRow_eq y).symm.trans he)⟩
    · rintro ⟨i, hi⟩
      exact List.mem_map.mpr
        ⟨A i, List.mem_ofFn.mpr ⟨i, rfl⟩, (cacheRow_eq (A i)).trans hi⟩
  rw [matrixRank,rank_correct,hs,Matrix.rank_eq_finrank_span_row]

theorem matrixRank_le_columns {m n : ℕ} (A : Matrix (Fin m) (Fin n) Bit) :
    matrixRank A≤n := rank_le_columns _ _

theorem matrixRank_transpose {m n : ℕ} (A : Matrix (Fin m) (Fin n) Bit) :
    matrixRank A.transpose=matrixRank A := by
  simp only [matrixRank_correct,Matrix.rank_transpose]

end QecReliability.BinaryElimination
