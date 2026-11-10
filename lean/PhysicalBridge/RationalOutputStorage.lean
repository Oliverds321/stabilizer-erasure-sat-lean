import PhysicalBridge.ExecutablePhysicalOutput

/-! Storage of the additional materialized coefficient vector is accounted for
separately from the raw SAT cache. Bounds concern binary payload, not heap or
temporary arithmetic/elimination workspace. -/
namespace QecReliability.RationalOutput
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open scoped BigOperators

namespace Ratio

theorem counts_den_le {a b M : ℕ} (h1 : 1≤M) (h : a+b≤M) : (counts a b).den≤M := by
  unfold counts
  split_ifs
  · exact h1
  · exact h

theorem lesser_den_le {x y : Ratio} {M : ℕ} (hx : x.den≤M) (hy : y.den≤M) :
    (lesser x y).den≤M := by unfold lesser; split_ifs <;> assumption

theorem greater_den_le {x y : Ratio} {M : ℕ} (hx : x.den≤M) (hy : y.den≤M) :
    (greater x y).den≤M := by unfold greater; split_ifs <;> assumption

theorem prefixMinimum_den_le (e : ℕ → Ratio) {M : ℕ} (h : ∀ j, (e j).den≤M) (j : ℕ) :
    (prefixMinimum e j).den≤M := by
  induction j with
  | zero => exact h 0
  | succ j ih => exact lesser_den_le ih (h (j+1))

theorem payload_le {x : Ratio} {M : ℕ} (h : x.den≤M) : x.payload≤2*M.size := by
  have hden := Nat.size_le_size h
  have hnum := Nat.size_le_size (x.num_le_den.trans h)
  unfold payload
  omega

end Ratio

theorem endpointEntry_den_le {r M : ℕ} (a ell : Ratio) (T : CoefficientTable r)
    (ha : a.den≤M) (hell : ell.den≤M) (h1 : 1≤M)
    (hT : ∀ j, (T.good.get j).1+(T.bad.get j).1≤M) (j : ℕ) :
    (endpointEntry a ell T j).den≤M := by
  unfold endpointEntry
  split_ifs
  · exact ha
  · exact hell
  · exact Ratio.counts_den_le h1 (hT _)

theorem Vector.payload_build {r : ℕ} (f : Fin (r+1) → Ratio) :
    (Vector.build f).payload=∑ j, (f j).payload := by
  simp [Vector.payload,Vector.build,List.map_ofFn,List.sum_ofFn,Fin.sum_univ_succ]

theorem Vector.payload_build_le {r M : ℕ} (f : Fin (r+1) → Ratio)
    (h : ∀ j, (f j).den≤M) : (Vector.build f).payload≤(r+1)*(2*M.size) := by
  rw [Vector.payload_build]
  simpa using Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => Ratio.payload_le (h j))

theorem ambiguityRank_le {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) :
    BinaryElimination.ambiguityRank rows E≤2*n := by
  have h : E.card≤n := by simpa using Finset.card_le_univ E
  unfold BinaryElimination.ambiguityRank
  omega

theorem dyadic_den_bound {n r : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) (B : ℕ) :
    (Ratio.dyadic rows E).den≤2*trialValueBound (keySize n r) B := by
  have hpow : 2^BinaryElimination.ambiguityRank rows E≤2^(keySize n r) :=
    Nat.pow_le_pow_right (by omega) ((ambiguityRank_le rows E).trans (by simp [keySize]; omega))
  change 2^BinaryElimination.ambiguityRank rows E≤_
  unfold trialValueBound
  exact hpow.trans ((Nat.le_mul_of_pos_right _ (by omega)).trans
    (Nat.le_mul_of_pos_left _ (by omega)))

theorem vector_den_bound {n r B : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (T : CoefficientTable r)
    (hT : ∀ j, (T.good.get j).1≤trialValueBound (keySize n r) B ∧
      (T.bad.get j).1≤trialValueBound (keySize n r) B) :
    (∀ j, ((endpointVector rows C T).get j).den≤2*trialValueBound (keySize n r) B) ∧
    (∀ j, ((shapeVector rows C T).get j).den≤2*trialValueBound (keySize n r) B) := by
  have h1 : 1≤2*trialValueBound (keySize n r) B := by
    have : 0<trialValueBound (keySize n r) B := by unfold trialValueBound; positivity
    omega
  have he := endpointEntry_den_le _ _ T (dyadic_den_bound (r:=r) rows (circuitMap C ∅) B)
    (dyadic_den_bound (r:=r) rows (circuitMap C Finset.univ) B) h1
    (fun j => by have hj := hT j; omega)
  constructor
  · intro j
    simpa only [endpointVector,Vector.get_build] using he j.val
  · intro j
    simp only [shapeVector,Vector.get_build]
    exact Ratio.greater_den_le (dyadic_den_bound (r:=r) rows _ B) (Ratio.prefixMinimum_den_le _ he _)

theorem vector_payload_bound {n r B : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (T : CoefficientTable r)
    (hT : ∀ j, (T.good.get j).1≤trialValueBound (keySize n r) B ∧
      (T.bad.get j).1≤trialValueBound (keySize n r) B) :
    (endpointVector rows C T).payload≤(r+1)*(2*(keySize n r+(4*B+1).size+1)) ∧
    (shapeVector rows C T).payload≤(r+1)*(2*(keySize n r+(4*B+1).size+1)) := by
  have hsize : (2*trialValueBound (keySize n r) B).size≤keySize n r+(4*B+1).size+1 := by
    apply Nat.size_le.mpr
    change 2*(2^(keySize n r)*(4*B+1))<2^(keySize n r+(4*B+1).size+1)
    calc
      _ < 2*(2^(keySize n r)*2^(4*B+1).size) :=
        Nat.mul_lt_mul_of_pos_left
          (Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self _) (by positivity)) (by omega)
      _ = _ := by
        rw [pow_add 2 (keySize n r+(4*B+1).size) 1,
          pow_add 2 (keySize n r) (4*B+1).size]
        ring
  have hb := vector_den_bound rows C T hT
  have hp0 := Vector.payload_build_le _ (by simpa only [endpointVector,Vector.get_build] using hb.1)
  have hp1 := Vector.payload_build_le _ (by simpa only [shapeVector,Vector.get_build] using hb.2)
  exact ⟨hp0.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 hsize)),
    hp1.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 hsize))⟩

theorem prepare_count_bounds {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) (j : Fin (r+1)) :
    ((prepare rows C H K solver B m ω).good.get j).1≤trialValueBound (keySize n r) B ∧
    ((prepare rows C H K solver B m ω).bad.get j).1≤trialValueBound (keySize n r) B := by
  simp only [prepare,CountTable.get_build]
  exact ⟨((queries rows C H K solver (true,j)).cachedMedian_bounds B m ω).1,
    ((queries rows C H K solver (false,j)).cachedMedian_bounds B m ω).1⟩

theorem prepared_vector_payload {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) :
    (endpointVector rows C (prepare rows C H K solver B m ω)).payload≤
      (r+1)*(2*(keySize n r+(4*B+1).size+1)) ∧
    (shapeVector rows C (prepare rows C H K solver B m ω)).payload≤
      (r+1)*(2*(keySize n r+(4*B+1).size+1)) :=
  vector_payload_bound rows C _ (prepare_count_bounds rows C H K solver B m ω)

end QecReliability.RationalOutput
