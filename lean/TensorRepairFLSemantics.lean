import TensorRepairFLWrapper
import TensorGridEnumeration

/-! The full FL callback returns the executable bounded-ratio tensor output.
This bridge follows the actual runtime lexicographic grid and the physically
computed canonical corner anchors. -/
set_option autoImplicit false

namespace QecReliability.TensorMachine.RepairFL
open FL FL.Lib FL.Lib.LinearRepairFL RationalOutput TensorBernstein TensorLatent
open SharedCircuit SharedCircuit.LatentEncoding Trans.Query

/-- The finite dependent enumeration and executable runtime grid have identical
order, not merely the same members. -/
theorem enum_indexList (ds : List ℕ) :
    (RationalTensorRepair.enum ds).map (indexList ds) = grid ds := by
  exact TensorMachine.enum_map_indexList ds

theorem countDataR_encode (ds : List ℕ) (points : List (Grid ds))
    (gs bs : Grid ds → RawRatio) :
    countDataR (points.map (indexList ds)) (points.map gs) (points.map bs) =
      encodeEntries ds (points.map (fun j => (j,Ratio.counts (gs j).1 (bs j).1))) := by
  induction points with
  | nil => rfl
  | cons j points ih =>
    change (indexList ds j,countsR (gs j).1 (bs j).1) ::
      countDataR (points.map (indexList ds)) (points.map gs) (points.map bs) =
        (indexList ds j,toR (Ratio.counts (gs j).1 (bs j).1)) ::
          encodeEntries ds (points.map (fun k => (k,Ratio.counts (gs k).1 (bs k).1)))
    rw [ih,toR_counts]

theorem anchorDataR_encode {n : ℕ} (ds : List ℕ)
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (points : List (Grid ds)) :
    anchorDataR (ds,n,encRows rows,encProg C) (points.map (indexList ds)) =
      encodeEntries ds (RationalPosetRepair.anchorTable
        (points.filter (RationalTensorRepair.cornerTest ds))
        (RationalTensorRepair.dyadicAnchor ds rows
          (fun b => circuitMap C (flattenCauses ds b)))) := by
  induction points with
  | nil => rfl
  | cons j points ih =>
    simp only [List.map_cons,anchorDataR,cornerR_index]
    cases hj : RationalTensorRepair.cornerTest ds j with
    | false =>
      simpa only [List.filter_cons,hj,Bool.false_eq_true,ite_false] using ih
    | true =>
      rw [if_pos rfl,dyadicR_correct,ih]
      simp only [List.filter_cons,hj,ite_true,RationalPosetRepair.anchorTable,
        List.map_cons,encodeEntries,List.map_cons]
      congr 2
      rw [RationalTensorRepair.dyadicAnchor,RationalTensorRepair.canonicalCausesExec_eq]

def circuitObservations {n : ℕ} (ds : List ℕ) (C : SharedCircuit.Program ds.sum n) :
    CausesGrid ds → Finset (Fin n) := fun b => circuitMap C (flattenCauses ds b)

/-- The callback's complete rational output agrees with the checked tensor
repair, with anchors computed from the input code and circuit. The auxiliary
second component of every cached count entry is immaterial to this conversion. -/
theorem fullR_eq_prepare {n : ℕ} (ds : List ℕ)
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (q seed : ℕ) (coins : List Bool) (gs bs : Grid ds → RawRatio) :
    fullR (ds,grid ds,n,encRows rows,encProg C,q,seed,coins)
      ((RationalTensorRepair.enum ds).map gs) ((RationalTensorRepair.enum ds).map bs) =
      (RationalTensorRepair.prepare ds rows (circuitObservations ds C)
        (fun j => Ratio.counts (gs j).1 (bs j).1)).map toR := by
  unfold fullR
  change repairR
    (countDataR (grid ds) ((RationalTensorRepair.enum ds).map gs)
      ((RationalTensorRepair.enum ds).map bs))
    (anchorDataR (ds,n,encRows rows,encProg C) (grid ds)) = _
  rw [← enum_indexList ds,countDataR_encode,anchorDataR_encode,repairR_encode]
  simp only [RationalTensorRepair.prepare,RationalTensorRepair.anchors,circuitObservations,
    List.map_map,Function.comp_def]
  delta circuitObservations
  rfl

end QecReliability.TensorMachine.RepairFL
