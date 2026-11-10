import TensorQueryBoundary
import TensorRepairFLSemantics
import PhysicalBridge.RationalTensorConfidence

/-! The two concrete forward count tables feed the same rational tensor output
whose physical accuracy is proved by RationalTensorConfidence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace QecReliability.TensorMachine.Boundary
open SharedCircuit TensorCoefficientCounting RationalOutput
open OracleCost OracleCost.MultiTape OracleCost.WholeWrapperCandidate

theorem index_enumeration (ds : List ℕ) :
    (List.finRange (slots ds-1+1)).map (index ds) = RationalTensorRepair.enum ds := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_finRange,RationalTensorRepair.enum_length,
      slots_pred_succ]
    rfl
  · intro j hj hk
    simp only [List.getElem_map,List.getElem_finRange,index,ordinalIndex,List.get_eq_getElem,
      Fin.val_cast]

variable {Ω : Type*} [Fintype Ω] {n : ℕ} {ds : List ℕ}
  (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
  (H : HashStages Ω (Key n ds) (SharedCircuit.LatentEncoding.keySize n ds.sum))
  (K : SuppliedHashCircuits H (TensorCoefficientCounting.keyBits n ds))
  (m : ℕ) (ω : Fin (2*m+1) → Ω) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ}
  {resource : SATRequest → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps T resource)

def cached (B : ℕ) (side : Bool) (j : TensorBernstein.Grid ds) : Entry :=
  (TensorEncoding.queries ds rows C H K spec.service.solver (side,j)).cachedMedian B m ω

theorem table_eq (B : ℕ) (side : Bool) :
    CountingTrace.sideEntries (SharedCircuit.LatentEncoding.keySize n ds.sum)
      (slots ds-1) B m (external rows C H K m ω density spec) side
      (List.finRange (slots ds-1+1)) =
        (RationalTensorRepair.enum ds).map (cached rows C H K m ω density spec B side) := by
  unfold CountingTrace.sideEntries
  have he : CountingTrace.entry (SharedCircuit.LatentEncoding.keySize n ds.sum)
      (slots ds-1) B m (external rows C H K m ω density spec) side =
        fun j => cached rows C H K m ω density spec B side (index ds j) := by
    funext j
    exact entry_eq rows C H K m ω density spec B side j
  rw [he]
  simpa only [List.map_map,Function.comp_def] using
    congrArg (List.map (cached rows C H K m ω density spec B side)) (index_enumeration ds)

theorem repair_tables (B q seed : ℕ) (coins : List Bool) :
    RepairFL.fullR (ds,grid ds,n,Trans.Query.encRows rows,Trans.Query.encProg C,q,seed,coins)
      (CountingTrace.sideEntries (SharedCircuit.LatentEncoding.keySize n ds.sum)
        (slots ds-1) B m (external rows C H K m ω density spec) true
        (List.finRange (slots ds-1+1)))
      (CountingTrace.sideEntries (SharedCircuit.LatentEncoding.keySize n ds.sum)
        (slots ds-1) B m (external rows C H K m ω density spec) false
        (List.finRange (slots ds-1+1))) =
      (RationalTensorConfidence.output rows (TensorEncoding.circuitMap C)
        (TensorEncoding.queries ds rows C H K spec.service.solver) B m ω).map
          FL.Lib.LinearRepairFL.toR := by
  rw [table_eq,table_eq,RepairFL.fullR_eq_prepare]
  have hc : RepairFL.circuitObservations ds C = TensorEncoding.circuitMap C := rfl
  rw [hc]
  unfold RationalTensorConfidence.output
  apply congrArg (fun estimates =>
    (RationalTensorRepair.prepare ds rows (TensorEncoding.circuitMap C) estimates).map
      FL.Lib.LinearRepairFL.toR)
  funext j
  simp only [RationalTensorConfidence.estimateRatios,CachedAnswers.median_eq,cached]

end QecReliability.TensorMachine.Boundary
