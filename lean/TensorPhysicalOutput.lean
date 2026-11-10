import TensorPhysicalAlgorithm
import TensorQueryBoundary

/-! Interpretation of the actual flat rational output vector. The tensor curve
is recovered solely from those coefficients and their runtime grid order. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.TensorMachine
open RationalOutput TensorBernstein SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate

theorem boundary_index_surjective (ds : List ℕ) : Function.Surjective (Boundary.index ds) := by
  intro j
  obtain ⟨k,hk⟩ := ordinalIndex_surjective ds j
  refine ⟨⟨k.val,by simpa only [Boundary.slots_pred_succ] using k.isLt⟩,?_⟩
  exact hk

def position (ds : List ℕ) (j : Grid ds) : Fin (slots ds-1+1) :=
  Classical.choose (boundary_index_surjective ds j)

theorem position_index (ds : List ℕ) (j : Grid ds) : Boundary.index ds (position ds j) = j :=
  Classical.choose_spec (boundary_index_surjective ds j)

def vectorCurve (ds : List ℕ) (v : RationalOutput.Vector (slots ds-1)) : Params ds → ℝ :=
  TensorBernstein.curve ds (fun j => (v.get (position ds j)).value)

namespace PhysicalAlgorithm
variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t)
  {n : ℕ} {ds : List ℕ}
  (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
  (solver : ∀ v, PrefixCNF.ExactSAT v 3) (B m : ℕ)
  (coins : CodeHash.BitTape (CodeHash.repeatBits
    (Factory.length hD hd A n ds) (Factory.width hD hd A n ds) m))

def outputVector : RationalOutput.Vector (slots ds-1) where
  entries := (output hD hd A rows C solver B m coins).toArray
  length_eq := by
    rw [List.size_toArray]
    exact (RationalTensorConfidence.output_length rows (TensorEncoding.circuitMap C)
      (decisions hD hd A rows C solver) B m _).trans
        (Boundary.slots_pred_succ ds).symm

theorem outputVector_list :
    (outputVector hD hd A rows C solver B m coins).entries.toList =
      output hD hd A rows C solver B m coins := by
  simp only [outputVector,List.toList_toArray]

theorem outputVector_get (j : Fin (slots ds-1+1)) :
    (outputVector hD hd A rows C solver B m coins).get j =
      RationalTensorRepair.coefficient ds rows (TensorEncoding.circuitMap C)
        (RationalTensorConfidence.estimateRatios (decisions hD hd A rows C solver) B m
          (CodeHash.repeatedSeedTapeEquiv _ _ m coins)) (Boundary.index ds j) := by
  simp only [outputVector,RationalOutput.Vector.get,List.getElem_toArray,output,
    RationalTensorConfidence.output,RationalTensorRepair.prepare_eq_map,List.getElem_map,
    Boundary.index,ordinalIndex,List.get_eq_getElem]

theorem vectorCurve_output :
    vectorCurve ds (outputVector hD hd A rows C solver B m coins) =
      outputCurve hD hd A rows C solver B m coins := by
  unfold vectorCurve outputCurve seedCurve RationalTensorConfidence.outputCurve
  congr 1
  funext j
  rw [outputVector_get,position_index]

end PhysicalAlgorithm
end QecReliability.TensorMachine
