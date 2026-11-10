import PhysicalBridge.PhysicalShapeConfidence
import PhysicalBridge.PostprocessTails

/-! Every-seed zero tails and zero latent-bit edge cases for the actual cache. -/
noncomputable section
namespace QecPhysical.Stabilizer
open QecReliability QecReliability.Binary
open QecReliability.SharedCircuit
open QecReliability.SharedCircuit.LatentEncoding
open QecReliability.SharedCircuit.ConcreteQuantum

theorem cachedEndpoint_zero_latents {n : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes 0 → Finset (Fin n)) (T : CoefficientTable 0) (p : ℝ) :
    cachedEndpointCurve S C T p=score S (C ∅) := by
  simp [cachedEndpointCurve,bernsteinCurve,average,bernsteinWeight,endpointInput]

theorem cachedShape_zero_latents {n : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes 0 → Finset (Fin n)) (T : CoefficientTable 0) (p : ℝ) :
    cachedShapeCurve S C T p=score S (C ∅) := by
  simp [cachedShapeCurve,bernsteinCurve,average,bernsteinWeight,endpointInput,repaired,runningMin]

namespace Lift
variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (L : Lift (rowSpace rows)) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)

include L in
theorem prepare_ratio_tailExact (B m : ℕ) (ω : Fin (2*m+1) → Ω) (j : Fin (r+1)) :
    TailExact (layerAverage (circuitMap C) (score (rowSpace rows)) j)
      ((prepare rows C H K solver B m ω).ratio j) := by
  let T := prepare rows C H K solver B m ω
  let A := goodCoefficient (rowSpace rows) (circuitMap C) j
  let D := badCoefficient (rowSpace rows) (circuitMap C) j
  have ha : T.value (true,j)=0 ↔ (A:ℝ)=0 := by
    rw [prepare_value_zero_iff]
    simp only [coefficientModels_card,↓reduceIte,Nat.cast_eq_zero,A]
  have hd : T.value (false,j)=0 ↔ (D:ℝ)=0 := by
    rw [prepare_value_zero_iff]
    simp only [coefficientModels_card,Bool.false_eq_true,↓reduceIte,Nat.cast_eq_zero,D]
  have hsum : 0<(A:ℝ)+D := coefficient_total_pos (rowSpace rows) (circuitMap C) j
  have hts := prepare_total_pos rows C H K solver B m ω j
  rw [←L.layer_ratio (circuitMap C) j]
  change TailExact ((A:ℝ)/((A:ℝ)+D)) (T.ratio j)
  constructor
  · intro hz
    have hA := (div_eq_zero_iff.mp hz).resolve_right hsum.ne'
    simp only [CoefficientTable.ratio,ha.mpr hA,zero_div]
  · intro ho
    have hA := (div_eq_iff hsum.ne').mp ho
    have hD : (D:ℝ)=0 := by linarith
    have hv := hd.mpr hD
    have hp : 0<T.value (true,j) := by change 0<T.value (true,j)+T.value (false,j) at hts; linarith
    simp only [CoefficientTable.ratio,hv,add_zero,div_self hp.ne']

theorem prepare_endpoint_physical_tails (B m : ℕ) (ω : Fin (2*m+1) → Ω) :
    ∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
      TailExact (entanglementFidelity (L.erasureFlagDecoder.comp
        (L.iidLatentErasure (circuitMap C) p hp.1 hp.2)).map)
        (cachedEndpointCurve (rowSpace rows) (circuitMap C) (prepare rows C H K solver B m ω) p) := by
  intro p hp
  rw [L.physical_fidelity_eq_latentCurve _ p hp.1 hp.2,latentCurve_eq_bernstein,cachedEndpointCurve_eq]
  exact bernsteinCurve_tailExact _ _
    (layerAverage_range _ _ (fun E => ⟨(score_range (rowSpace rows) E).1.le,(score_range (rowSpace rows) E).2⟩))
    (endpointCoefficients_tailExact _ _ (prepare_ratio_tailExact rows L C H K solver B m ω)) hp.1 hp.2

theorem prepare_shape_physical_tails
    (hanti : Antitone (layerAverage (circuitMap C) (score (rowSpace rows))))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) :
    ∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
      TailExact (entanglementFidelity (L.erasureFlagDecoder.comp
        (L.iidLatentErasure (circuitMap C) p hp.1 hp.2)).map)
        (cachedShapeCurve (rowSpace rows) (circuitMap C) (prepare rows C H K solver B m ω) p) := by
  intro p hp
  rw [L.physical_fidelity_eq_latentCurve _ p hp.1 hp.2,latentCurve_eq_bernstein,cachedShapeCurve_eq]
  have hr := layerAverage_range (circuitMap C) (score (rowSpace rows))
    (fun E => ⟨(score_range (rowSpace rows) E).1.le,(score_range (rowSpace rows) E).2⟩)
  exact bernsteinCurve_tailExact _ _ hr
    (shapeCoefficients_tailExact _ _ hr (prepare rows C H K solver B m ω).ratio_range
      hanti (prepare_ratio_tailExact rows L C H K solver B m ω)) hp.1 hp.2

end Lift
end QecPhysical.Stabilizer
