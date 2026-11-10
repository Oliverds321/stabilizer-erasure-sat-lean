import PhysicalBridge.LinearRepairConfidence

/-! Exact evaluation, zero-latent endpoints and all-seed tails transport through
literal equality of the rational vectors, without a new probabilistic premise. -/
namespace QecReliability.RationalOutput.LinearRepair
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open QecPhysical.Stabilizer

theorem vector_evaluate {n r u d : ℕ} (shape : Bool)
    (rows : List (List (PauliCoord n))) (C : Program r n) (T : CoefficientTable r)
    (hud : u≤d) (hd : 0<d) :
    (((vector shape rows C T).evaluate u d).1:ℝ)/((vector shape rows C T).evaluate u d).2=
      (if shape then cachedShapeCurve (rowSpace rows) (circuitMap C) T
       else cachedEndpointCurve (rowSpace rows) (circuitMap C) T) ((u:ℝ)/d) := by
  rw [Vector.evaluate_correct _ hud hd,vector_eq]
  cases shape <;> simp only [Bool.false_eq_true,↓reduceIte,shapeVector_curve,endpointVector_curve]

theorem vector_zero_latents {n : ℕ} (shape : Bool) (rows : List (List (PauliCoord n)))
    (C : Program 0 n) (T : CoefficientTable 0) (p : ℝ) :
    (vector shape rows C T).curve p=score (rowSpace rows) (circuitMap C ∅) := by
  rw [vector_eq]
  cases shape <;> simp only [Bool.false_eq_true,↓reduceIte,shapeVector_zero_latents,endpointVector_zero_latents]

end QecReliability.RationalOutput.LinearRepair

namespace QecPhysical.Stabilizer.Lift
open QecReliability QecReliability.Binary QecReliability.RationalOutput
open QecReliability.SharedCircuit QecReliability.SharedCircuit.LatentEncoding
open QecReliability.SharedCircuit.ConcreteQuantum
variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (L : Lift (rowSpace rows)) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (a b c d : ℕ) (ω : Fin (2*rationalRepetitionBudget (2*(r+1)) c d+1) → Ω)

theorem linear_endpoint_tails :
    ∀ p (hp : p∈Set.Icc (0:ℝ) 1),
      TailExact (entanglementFidelity (L.erasureFlagDecoder.comp
        (L.iidLatentErasure (circuitMap C) p hp.1 hp.2)).map)
        ((LinearRepair.prepare false rows C H K solver a b c d ω).coefficients.curve p) := by
  simpa only [LinearRepair.prepare_coefficients,Bool.false_eq_true,↓reduceIte,endpointVector_curve,
    runEndpoint] using executable_endpoint_tails rows L C H K solver a b c d ω

theorem linear_shape_tails
    (hanti : Antitone (layerAverage (circuitMap C) (score (rowSpace rows)))) :
    ∀ p (hp : p∈Set.Icc (0:ℝ) 1),
      TailExact (entanglementFidelity (L.erasureFlagDecoder.comp
        (L.iidLatentErasure (circuitMap C) p hp.1 hp.2)).map)
        ((LinearRepair.prepare true rows C H K solver a b c d ω).coefficients.curve p) := by
  simpa only [LinearRepair.prepare_coefficients,↓reduceIte,shapeVector_curve,
    runShape] using executable_shape_tails rows L C H K solver a b c d ω hanti

end QecPhysical.Stabilizer.Lift
