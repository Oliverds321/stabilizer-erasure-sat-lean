import PhysicalBridge.LinearRepairOutput

/-! Physical confidence and deterministic resources for the same measured
single-pass output, with no new bad event or additional accuracy tolerance. -/
namespace QecReliability.RationalOutput.LinearRepair
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open QecPhysical.Stabilizer

def Resources (n r B m : ℕ) (O : Output r) : Prop :=
  RawCacheResources n r B m O.raw ∧ O.coefficients.entries.size=r+1 ∧
  O.coefficients.payload≤(r+1)*(2*(keySize n r+(4*B+1).size+1)) ∧
  O.report.pairVisits=r+1 ∧ O.report.ratioBuilds≤r+1 ∧
  O.report.orderComparisons≤2*(r+1) ∧ O.report.endpointTests≤2*(r+1) ∧
  O.report.maxAccumulatorDen≤2*trialValueBound (keySize n r) B ∧
  O.report.payload≤4*(2*(r+1)).size+(2*trialValueBound (keySize n r) B).size

theorem prepare_resources {Ω : Type*} [Fintype Ω] {n r : ℕ} (shape : Bool)
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (a b c d : ℕ) (ω : Fin (2*rationalRepetitionBudget (2*(r+1)) c d+1) → Ω) :
    Resources n r (rationalCellBudget a b) (rationalRepetitionBudget (2*(r+1)) c d)
      (prepare shape rows C H K solver a b c d ω) := by
  let B := rationalCellBudget a b
  let m := rationalRepetitionBudget (2*(r+1)) c d
  let T := prepareRational rows C H K solver a b c d ω
  have hv := prepared_vector_payload rows C H K solver B m ω
  have hT := prepare_count_bounds rows C H K solver B m ω
  have hb := fromCache_bounds shape rows C T
  refine ⟨prepare_raw_resources rows C H K solver B m ω,
    (prepare shape rows C H K solver a b c d ω).coefficients.length_eq,?_,
    fromCache_visits shape rows C T,hb.1,hb.2.1,hb.2.2,
    fromCache_accumulator_bound shape rows C T hT,fromCache_report_payload shape rows C T hT⟩
  rw [prepare_coefficients]
  cases shape
  · exact hv.1
  · exact hv.2

end QecReliability.RationalOutput.LinearRepair

namespace QecPhysical.Stabilizer.Lift
open QecReliability QecReliability.Binary QecReliability.RationalOutput
open QecReliability.SharedCircuit QecReliability.SharedCircuit.LatentEncoding
open QecReliability.SharedCircuit.ConcreteQuantum
variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (L : Lift (rowSpace rows)) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (a b c d : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (hab : a≤b)

include ha hb hc hd hab

theorem linear_endpoint_confidence :
    (∀ ω, let O := LinearRepair.prepare false rows C H K solver a b c d ω
      LinearRepair.Resources n r (rationalCellBudget a b) (rationalRepetitionBudget (2*(r+1)) c d) O ∧
      EndpointStructure (rowSpace rows) (circuitMap C) O.coefficients.curve) ∧
    1-(c:ℝ)/d ≤ (repeatedLaw H.law (rationalRepetitionBudget (2*(r+1)) c d)).prob
      (fun ω => L.PhysicalAccuracy (circuitMap C) ((a:ℝ)/b)
        (LinearRepair.prepare false rows C H K solver a b c d ω).coefficients.curve) := by
  have h := rational_endpoint_confidence rows L C H K solver a b c d ha hb hc hd hab
  refine ⟨fun ω => ⟨LinearRepair.prepare_resources false rows C H K solver a b c d ω,?_⟩,?_⟩
  · simpa only [LinearRepair.prepare_coefficients,Bool.false_eq_true,↓reduceIte,endpointVector_curve] using (h.1 ω).2
  · simpa only [LinearRepair.prepare_coefficients,Bool.false_eq_true,↓reduceIte,endpointVector_curve] using h.2

theorem linear_shape_confidence
    (hanti : Antitone (layerAverage (circuitMap C) (score (rowSpace rows)))) :
    (∀ ω, let O := LinearRepair.prepare true rows C H K solver a b c d ω
      LinearRepair.Resources n r (rationalCellBudget a b) (rationalRepetitionBudget (2*(r+1)) c d) O ∧
      ShapeStructure (rowSpace rows) (circuitMap C) O.coefficients.curve) ∧
    1-(c:ℝ)/d ≤ (repeatedLaw H.law (rationalRepetitionBudget (2*(r+1)) c d)).prob
      (fun ω => L.PhysicalAccuracy (circuitMap C) ((a:ℝ)/b)
        (LinearRepair.prepare true rows C H K solver a b c d ω).coefficients.curve) := by
  have h := rational_shape_confidence rows L C H K solver a b c d ha hb hc hd hab hanti
  refine ⟨fun ω => ⟨LinearRepair.prepare_resources true rows C H K solver a b c d ω,?_⟩,?_⟩
  · simpa only [LinearRepair.prepare_coefficients,↓reduceIte,shapeVector_curve] using (h.1 ω).2
  · simpa only [LinearRepair.prepare_coefficients,↓reduceIte,shapeVector_curve] using h.2

end QecPhysical.Stabilizer.Lift
