import PhysicalBridge.RationalOutputStorage

/-! Zero latent bits and exact zero tails for the executable output. These are
every-seed statements; they do not assume the counting success event. -/
namespace QecReliability.RationalOutput
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open QecPhysical.Stabilizer

theorem endpointVector_zero_latents {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program 0 n) (T : CoefficientTable 0) (p : ℝ) :
    (endpointVector rows C T).curve p=score (rowSpace rows) (circuitMap C ∅) := by
  rw [endpointVector_curve,cachedEndpoint_zero_latents]

theorem shapeVector_zero_latents {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program 0 n) (T : CoefficientTable 0) (p : ℝ) :
    (shapeVector rows C T).curve p=score (rowSpace rows) (circuitMap C ∅) := by
  rw [shapeVector_curve,cachedShape_zero_latents]

end QecReliability.RationalOutput

namespace QecPhysical.Stabilizer.Lift
open QecReliability QecReliability.Binary QecReliability.RationalOutput
open QecReliability.SharedCircuit QecReliability.SharedCircuit.LatentEncoding
open QecReliability.SharedCircuit.ConcreteQuantum
variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (L : Lift (rowSpace rows)) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (a b c d : ℕ) (ω : Fin (2*rationalRepetitionBudget (2*(r+1)) c d+1) → Ω)

theorem executable_endpoint_tails :
    ∀ p (hp : p∈Set.Icc (0:ℝ) 1),
      TailExact (entanglementFidelity (L.erasureFlagDecoder.comp
        (L.iidLatentErasure (circuitMap C) p hp.1 hp.2)).map)
        ((runEndpoint rows C H K solver a b c d ω).coefficients.curve p) := by
  simpa only [runEndpoint,endpointVector_curve,prepareRational] using
    prepare_endpoint_physical_tails rows L C H K solver (rationalCellBudget a b)
      (rationalRepetitionBudget (2*(r+1)) c d) ω

theorem executable_shape_tails
    (hanti : Antitone (layerAverage (circuitMap C) (score (rowSpace rows)))) :
    ∀ p (hp : p∈Set.Icc (0:ℝ) 1),
      TailExact (entanglementFidelity (L.erasureFlagDecoder.comp
        (L.iidLatentErasure (circuitMap C) p hp.1 hp.2)).map)
        ((runShape rows C H K solver a b c d ω).coefficients.curve p) := by
  simpa only [runShape,shapeVector_curve,prepareRational] using
    prepare_shape_physical_tails rows L C H K solver hanti (rationalCellBudget a b)
      (rationalRepetitionBudget (2*(r+1)) c d) ω

end QecPhysical.Stabilizer.Lift
