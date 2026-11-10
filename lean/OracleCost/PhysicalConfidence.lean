import OracleCost.QuantumService

/-! The measured service traversal and the existing physical confidence theorem
refer to one output. Structural properties and service-time bounds hold on every
seed. The only random event below is simultaneous physical approximation.
This is not yet a total wrapper runtime or space theorem. -/
namespace QecReliability.OracleCost.QuantumService
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open RationalOutput QecPhysical.Stabilizer

variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (L : Lift (rowSpace rows)) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (service : SATService)
    (a b c d : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (hab : a≤b)

include ha hb hc hd hab

/-- No confidence hypothesis is supplied: the finite probability bound is
inherited through exact equality of the prepared cache and repaired output. -/
theorem measured_shape_confidence
    (hanti : Antitone (layerAverage (circuitMap C) (score (rowSpace rows))))
    (bound : ℕ)
    (hbase : ∀ i, (service.run (baseRequest rows C i [])).time≤bound)
    (hcell : ∀ i s seed pre, pre.length≤keySize n r →
      (service.run (cellRequest rows C H K i s seed pre)).time≤bound) :
    (∀ ω,
      let B := rationalCellBudget a b
      let m := rationalRepetitionBudget (2*(r+1)) c d
      let O := output rows C H K service true a b c d ω
      (prepareMeasured rows C H K service B m ω).oracleTime≤
        2*(r+1)*(2*m+1)*trialCallBound (keySize n r) B*bound ∧
      LinearRepair.Resources n r B m O ∧
      ShapeStructure (rowSpace rows) (circuitMap C) O.coefficients.curve) ∧
    1-(c:ℝ)/d ≤ (repeatedLaw H.law (rationalRepetitionBudget (2*(r+1)) c d)).prob
      (fun ω => L.PhysicalAccuracy (circuitMap C) ((a:ℝ)/b)
        (output rows C H K service true a b c d ω).coefficients.curve) := by
  have h := Lift.linear_shape_confidence rows L C H K service.solver a b c d ha hb hc hd hab hanti
  refine ⟨fun ω => ⟨prepareMeasured_time rows C H K service _ _ bound ω hbase hcell,?_,?_⟩,?_⟩
  · rw [output_eq]
    exact (h.1 ω).1
  · rw [output_eq]
    exact (h.1 ω).2
  · simpa only [output_eq] using h.2

/-- Arbitrary latent circuits get endpoint replacement and range, without an
antitonicity assertion or an ordered-endpoint premise. -/
theorem measured_endpoint_confidence (bound : ℕ)
    (hbase : ∀ i, (service.run (baseRequest rows C i [])).time≤bound)
    (hcell : ∀ i s seed pre, pre.length≤keySize n r →
      (service.run (cellRequest rows C H K i s seed pre)).time≤bound) :
    (∀ ω,
      let B := rationalCellBudget a b
      let m := rationalRepetitionBudget (2*(r+1)) c d
      let O := output rows C H K service false a b c d ω
      (prepareMeasured rows C H K service B m ω).oracleTime≤
        2*(r+1)*(2*m+1)*trialCallBound (keySize n r) B*bound ∧
      LinearRepair.Resources n r B m O ∧
      EndpointStructure (rowSpace rows) (circuitMap C) O.coefficients.curve) ∧
    1-(c:ℝ)/d ≤ (repeatedLaw H.law (rationalRepetitionBudget (2*(r+1)) c d)).prob
      (fun ω => L.PhysicalAccuracy (circuitMap C) ((a:ℝ)/b)
        (output rows C H K service false a b c d ω).coefficients.curve) := by
  have h := Lift.linear_endpoint_confidence rows L C H K service.solver a b c d ha hb hc hd hab
  refine ⟨fun ω => ⟨prepareMeasured_time rows C H K service _ _ bound ω hbase hcell,?_,?_⟩,?_⟩
  · rw [output_eq]
    exact (h.1 ω).1
  · rw [output_eq]
    exact (h.1 ω).2
  · simpa only [output_eq] using h.2

end QecReliability.OracleCost.QuantumService
