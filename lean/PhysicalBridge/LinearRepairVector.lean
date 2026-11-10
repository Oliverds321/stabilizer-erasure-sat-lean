import PhysicalBridge.LinearRepairScan

/-! A single traversal of the actual cache lists, followed by one output-array
conversion. No repeated List.get or function-valued prefix recomputation occurs. -/
namespace QecReliability.RationalOutput.LinearRepair
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

variable {n r : ℕ}

def fromCache (shape : Bool) (rows : List (List (PauliCoord n))) (C : Program r n)
    (T : CoefficientTable r) : Result :=
  let a := Ratio.dyadic rows (circuitMap C ∅)
  let ell := Ratio.dyadic rows (circuitMap C Finset.univ)
  run shape r a ell 0 a T.good.entries T.bad.entries

theorem fromCache_length (shape : Bool) (rows : List (List (PauliCoord n))) (C : Program r n)
    (T : CoefficientTable r) : (fromCache shape rows C T).values.length=r+1 := by
  simp [fromCache,run_length,T.good.length_eq,T.bad.length_eq]

theorem cache_sourceEntry (a ell : Ratio) (T : CoefficientTable r) (j : ℕ)
    (hg : j<T.good.entries.length) (hb : j<T.bad.entries.length) :
    sourceEntry r a ell j T.good.entries[j] T.bad.entries[j]=endpointEntry a ell T j := by
  have hj : j≤r := by rw [T.good.length_eq] at hg; omega
  simp only [sourceEntry,endpointEntry,min_eq_left hj]
  split_ifs <;> rfl

theorem fromCache_values (shape : Bool) (rows : List (List (PauliCoord n))) (C : Program r n)
    (T : CoefficientTable r) :
    (fromCache shape rows C T).values=List.ofFn (fun j : Fin (r+1) =>
      if shape then (shapeVector rows C T).get j else (endpointVector rows C T).get j) := by
  let a := Ratio.dyadic rows (circuitMap C ∅)
  let ell := Ratio.dyadic rows (circuitMap C Finset.univ)
  have h := run_semantics shape r a ell (endpointEntry a ell T) T.good.entries T.bad.entries 0 a
    (fun i hg hb => by simpa using cache_sourceEntry a ell T i hg hb) (by simp)
  simpa only [T.good.length_eq,T.bad.length_eq,min_self,zero_add,
    shapeVector,endpointVector,Vector.get_build,Fin.val_cast,fromCache,a,ell] using h

def vector (shape : Bool) (rows : List (List (PauliCoord n))) (C : Program r n)
    (T : CoefficientTable r) : Vector r :=
  let result := fromCache shape rows C T
  ⟨result.values.toArray,by simp [result,fromCache_length]⟩

theorem vector_eq (shape : Bool) (rows : List (List (PauliCoord n))) (C : Program r n)
    (T : CoefficientTable r) :
    vector shape rows C T=if shape then shapeVector rows C T else endpointVector rows C T := by
  unfold vector
  simp only [fromCache_values,List.toArray_ofFn]
  cases shape <;> simp only [Bool.false_eq_true,↓reduceIte,Vector.get_build,shapeVector,endpointVector]
  all_goals rfl

theorem fromCache_visits (shape : Bool) (rows : List (List (PauliCoord n))) (C : Program r n)
    (T : CoefficientTable r) : (fromCache shape rows C T).pairVisits=r+1 := by
  simp [fromCache,run_visits,T.good.length_eq,T.bad.length_eq]

theorem fromCache_bounds (shape : Bool) (rows : List (List (PauliCoord n))) (C : Program r n)
    (T : CoefficientTable r) :
    (fromCache shape rows C T).ratioBuilds≤r+1 ∧
    (fromCache shape rows C T).orderComparisons≤2*(r+1) ∧
    (fromCache shape rows C T).endpointTests≤2*(r+1) := by
  simpa only [T.good.length_eq,T.bad.length_eq,min_self,fromCache] using
    run_bounds shape r (Ratio.dyadic rows (circuitMap C ∅))
      (Ratio.dyadic rows (circuitMap C Finset.univ)) T.good.entries T.bad.entries 0
      (Ratio.dyadic rows (circuitMap C ∅))

theorem fromCache_comparisons (shape : Bool) (rows : List (List (PauliCoord n))) (C : Program r n)
    (T : CoefficientTable r) :
    (fromCache shape rows C T).orderComparisons=if shape then 2*r+1 else r := by
  unfold fromCache
  rw [run_comparisons_initial,T.good.length_eq,T.bad.length_eq,min_self]
  cases shape <;> simp
  omega

end QecReliability.RationalOutput.LinearRepair
