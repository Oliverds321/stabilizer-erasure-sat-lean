import PhysicalBridge.RationalRepair
import PhysicalBridge.RationalPhysicalEstimator

/-! The actual cached estimator followed by computed exact endpoints and a
materialized rational coefficient vector. These functions are executable
relative to supplied circuits, exact SAT and a seed vector. -/
namespace QecReliability.RationalOutput
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

structure Output (r : ℕ) where
  raw : CoefficientTable r
  coefficients : Vector r

def runEndpoint {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (a b c d : ℕ) (ω : Fin (2*rationalRepetitionBudget (2*(r+1)) c d+1) → Ω) : Output r :=
  let T := prepareRational rows C H K solver a b c d ω
  ⟨T,endpointVector rows C T⟩

def runShape {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (a b c d : ℕ) (ω : Fin (2*rationalRepetitionBudget (2*(r+1)) c d+1) → Ω) : Output r :=
  let T := prepareRational rows C H K solver a b c d ω
  ⟨T,shapeVector rows C T⟩

end QecReliability.RationalOutput

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

theorem executable_endpoint_confidence :
    (∀ ω, let O := runEndpoint rows C H K solver a b c d ω
      RawCacheResources n r (rationalCellBudget a b) (rationalRepetitionBudget (2*(r+1)) c d) O.raw ∧
      EndpointStructure (rowSpace rows) (circuitMap C) O.coefficients.curve ∧
      O.coefficients.entries.size=r+1) ∧
    1-(c:ℝ)/d ≤ (repeatedLaw H.law (rationalRepetitionBudget (2*(r+1)) c d)).prob
      (fun ω => L.PhysicalAccuracy (circuitMap C) ((a:ℝ)/b)
        (runEndpoint rows C H K solver a b c d ω).coefficients.curve) := by
  have h := rational_endpoint_confidence rows L C H K solver a b c d ha hb hc hd hab
  refine ⟨fun ω => ⟨(h.1 ω).1,?_,(runEndpoint rows C H K solver a b c d ω).coefficients.length_eq⟩,?_⟩
  · simpa only [runEndpoint,endpointVector_curve] using (h.1 ω).2
  · simpa only [runEndpoint,endpointVector_curve] using h.2

theorem executable_shape_confidence
    (hanti : Antitone (layerAverage (circuitMap C) (score (rowSpace rows)))) :
    (∀ ω, let O := runShape rows C H K solver a b c d ω
      RawCacheResources n r (rationalCellBudget a b) (rationalRepetitionBudget (2*(r+1)) c d) O.raw ∧
      ShapeStructure (rowSpace rows) (circuitMap C) O.coefficients.curve ∧
      O.coefficients.entries.size=r+1) ∧
    1-(c:ℝ)/d ≤ (repeatedLaw H.law (rationalRepetitionBudget (2*(r+1)) c d)).prob
      (fun ω => L.PhysicalAccuracy (circuitMap C) ((a:ℝ)/b)
        (runShape rows C H K solver a b c d ω).coefficients.curve) := by
  have h := rational_shape_confidence rows L C H K solver a b c d ha hb hc hd hab hanti
  refine ⟨fun ω => ⟨(h.1 ω).1,?_,(runShape rows C H K solver a b c d ω).coefficients.length_eq⟩,?_⟩
  · simpa only [runShape,shapeVector_curve] using (h.1 ω).2
  · simpa only [runShape,shapeVector_curve] using h.2

end QecPhysical.Stabilizer.Lift
