import PhysicalBridge.CommutationRank
import PhysicalBridge.PhysicalCachedShape
import QecReliability.LatentEncoder

/-! Computed dyadic scores and endpoints, from the input rows and actual
shared-wire circuit evaluation. No rank certificates or exact interior layers
are inputs to these functions. -/
namespace QecReliability.BinaryElimination
open Binary SharedCircuit SharedCircuit.LatentEncoding

def scorePair {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) : ℕ × ℕ :=
  (1,2^ambiguityRank rows E)

def scoreRat {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) : ℚ :=
  (scorePair rows E).1/(scorePair rows E).2

theorem scorePair_valid {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) :
    0<(scorePair rows E).2 ∧ (scorePair rows E).1≤(scorePair rows E).2 := by
  exact ⟨Nat.pow_pos (by omega),Nat.one_le_pow _ _ (by omega)⟩

theorem scorePair_correct {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) :
    ((scorePair rows E).1:ℝ)/(scorePair rows E).2=score (rowSpace rows) E := by
  simp [scorePair,score,ambiguityRank_correct,one_div]

theorem scoreRat_correct {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) :
    (scoreRat rows E:ℝ)=score (rowSpace rows) E := by
  simpa [scoreRat] using scorePair_correct rows E

def exactEndpoints {n r : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n) :
    (ℕ × ℕ) × (ℕ × ℕ) :=
  (scorePair rows (circuitMap C ∅),scorePair rows (circuitMap C Finset.univ))

theorem exactEndpoints_correct {n r : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n) :
    ((exactEndpoints rows C).1.1:ℝ)/(exactEndpoints rows C).1.2=
      score (rowSpace rows) (circuitMap C ∅) ∧
    ((exactEndpoints rows C).2.1:ℝ)/(exactEndpoints rows C).2.2=
      score (rowSpace rows) (circuitMap C Finset.univ) :=
  ⟨scorePair_correct _ _,scorePair_correct _ _⟩

theorem exactEndpoints_zero {n : ℕ} (rows : List (List (PauliCoord n))) (C : Program 0 n) :
    (exactEndpoints rows C).1=(exactEndpoints rows C).2 := by
  have h : (∅ : Causes 0)=Finset.univ := by ext x; exact Fin.elim0 x
  simp only [exactEndpoints,h]

end QecReliability.BinaryElimination
