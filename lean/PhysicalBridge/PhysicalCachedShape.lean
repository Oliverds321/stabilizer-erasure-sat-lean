import PhysicalBridge.PostprocessShape
import PhysicalBridge.CachedCoefficients

/-! Postprocessing reads one prepared table and two exact physical endpoints.
All-CPTP optimality and every-run structure are separate from confidence. -/
noncomputable section
namespace QecPhysical.Stabilizer
open QecReliability QecReliability.Binary
open QecReliability.SharedCircuit
open QecReliability.SharedCircuit.LatentEncoding
open QecReliability.SharedCircuit.ConcreteQuantum

def cachedEndpointCurve {n r : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes r → Finset (Fin n)) (T : CoefficientTable r) : ℝ → ℝ :=
  bernsteinCurve r (fun j => endpointInput (score S (C ∅)) (score S (C Finset.univ)) T.ratio j.val)

def cachedShapeCurve {n r : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes r → Finset (Fin n)) (T : CoefficientTable r) : ℝ → ℝ :=
  bernsteinCurve r (fun j => repaired (score S (C Finset.univ))
    (endpointInput (score S (C ∅)) (score S (C Finset.univ)) T.ratio) j.val)

theorem cachedEndpointCurve_eq {n r : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes r → Finset (Fin n)) (T : CoefficientTable r) :
    cachedEndpointCurve S C T = bernsteinCurve r (endpointCoefficients (layerAverage C (score S)) T.ratio) := by
  funext p
  unfold cachedEndpointCurve
  congr 1
  funext j
  change endpointInput _ _ _ j.val = shapeInput _ _ j.val
  rw [shapeInput_eq_endpointInput,layerAverage_fin_zero,layerAverage_fin_last]

theorem cachedShapeCurve_eq {n r : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes r → Finset (Fin n)) (T : CoefficientTable r) :
    cachedShapeCurve S C T = bernsteinCurve r (shapeCoefficients (layerAverage C (score S)) T.ratio) := by
  funext p
  unfold cachedShapeCurve
  congr 1
  funext j
  change repaired _ _ j.val = repaired (layerAverage C (score S) (Fin.last r)) (shapeInput _ _) j.val
  rw [shapeInput_eq_endpointInput,layerAverage_fin_zero,layerAverage_fin_last]

theorem cachedEndpoint_structural {n r : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes r → Finset (Fin n)) (T : CoefficientTable r) :
    cachedEndpointCurve S C T 0 = score S (C ∅) ∧
    cachedEndpointCurve S C T 1 = score S (C Finset.univ) ∧
    ∀ p ∈ Set.Icc (0:ℝ) 1, 0≤cachedEndpointCurve S C T p ∧ cachedEndpointCurve S C T p≤1 := by
  rw [cachedEndpointCurve_eq]
  simpa only [layerAverage_fin_zero,layerAverage_fin_last] using endpointCurve_structural
    (layerAverage C (score S)) T.ratio
    (layerAverage_range C (score S) (fun E => ⟨(score_range S E).1.le,(score_range S E).2⟩))
    T.ratio_range

theorem cachedShape_structural {n r : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes r → Finset (Fin n)) (T : CoefficientTable r)
    (horder : score S (C Finset.univ)≤score S (C ∅)) :
    AntitoneOn (cachedShapeCurve S C T) (Set.Icc 0 1) ∧
    cachedShapeCurve S C T 0 = score S (C ∅) ∧
    cachedShapeCurve S C T 1 = score S (C Finset.univ) ∧
    ∀ p ∈ Set.Icc (0:ℝ) 1,
      score S (C Finset.univ)≤cachedShapeCurve S C T p ∧
      cachedShapeCurve S C T p≤score S (C ∅) ∧
      0≤cachedShapeCurve S C T p ∧ cachedShapeCurve S C T p≤1 := by
  rw [cachedShapeCurve_eq]
  have h := shapeCurve_structural (layerAverage C (score S)) T.ratio
    (by simpa only [layerAverage_fin_zero,layerAverage_fin_last] using horder)
    (by simpa only [layerAverage_fin_last] using (score_range S (C Finset.univ)).1.le)
    (by simpa only [layerAverage_fin_zero] using (score_range S (C ∅)).2)
  simpa only [layerAverage_fin_zero,layerAverage_fin_last] using h

namespace Lift
variable {n r : ℕ} {S : Submodule Bit (Pauli n)} (L : Lift S)

theorem cachedEndpoint_physical_endpoints (C : Causes r → Finset (Fin n)) (T : CoefficientTable r) :
    cachedEndpointCurve S C T 0 = entanglementFidelity (L.erasureFlagDecoder.comp
      (L.iidLatentErasure C 0 (by norm_num) (by norm_num))).map ∧
    cachedEndpointCurve S C T 1 = entanglementFidelity (L.erasureFlagDecoder.comp
      (L.iidLatentErasure C 1 (by norm_num) (by norm_num))).map :=
  ⟨(cachedEndpoint_structural S C T).1.trans (L.iidLatentErasure_endpoints C).1.symm,
    (cachedEndpoint_structural S C T).2.1.trans (L.iidLatentErasure_endpoints C).2.symm⟩

theorem cachedShape_physical_endpoints (C : Causes r → Finset (Fin n)) (T : CoefficientTable r)
    (horder : score S (C Finset.univ)≤score S (C ∅)) :
    cachedShapeCurve S C T 0 = entanglementFidelity (L.erasureFlagDecoder.comp
      (L.iidLatentErasure C 0 (by norm_num) (by norm_num))).map ∧
    cachedShapeCurve S C T 1 = entanglementFidelity (L.erasureFlagDecoder.comp
      (L.iidLatentErasure C 1 (by norm_num) (by norm_num))).map :=
  ⟨(cachedShape_structural S C T horder).2.1.trans (L.iidLatentErasure_endpoints C).1.symm,
    (cachedShape_structural S C T horder).2.2.1.trans (L.iidLatentErasure_endpoints C).2.symm⟩

def PhysicalAccuracy (C : Causes r → Finset (Fin n)) (ε : ℝ) (R : ℝ → ℝ) : Prop :=
  ∀ p (hp : p ∈ Set.Icc (0:ℝ) 1), RelPair ε
    (entanglementFidelity (L.erasureFlagDecoder.comp (L.iidLatentErasure C p hp.1 hp.2)).map) (R p)

/-- Deterministic physical attainment and unrestricted upper bound, outside all random events. -/
theorem cached_target_optimality (C : Causes r → Finset (Fin n)) :
    ∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
      entanglementFidelity (L.erasureFlagDecoder.comp (L.iidLatentErasure C p hp.1 hp.2)).map =
        latentCurve C (score S) p ∧
      ∀ Q : Channel (ErasureFlagOutput n) L.LogicalIndex,
        entanglementFidelity (Q.comp (L.iidLatentErasure C p hp.1 hp.2)).map ≤
          entanglementFidelity (L.erasureFlagDecoder.comp (L.iidLatentErasure C p hp.1 hp.2)).map := by
  intro p hp
  refine ⟨L.physical_fidelity_eq_latentCurve C p hp.1 hp.2,?_⟩
  rw [(L.iidLatentErasure_optimum C p hp.1 hp.2).1]
  exact (L.iidLatentErasure_optimum C p hp.1 hp.2).2

include L in
theorem layer_ratio (C : Causes r → Finset (Fin n)) (j : Fin (r+1)) :
    (goodCoefficient S C j:ℝ) / ((goodCoefficient S C j:ℝ)+badCoefficient S C j) =
      layerAverage C (score S) j := by
  rw [←Nat.cast_add,coefficient_partition,Nat.cast_mul]
  exact good_coefficient_normalized S L.isotropic C j

include L in
theorem coefficient_event_relPair (C : Causes r → Finset (Fin n)) (T : CoefficientTable r)
    {ε : ℝ} (hε : 0≤ε) (hε1 : ε≤1)
    (h : ∀ i, |T.value i-((coefficientModels S C i).card:ℝ)|≤(ε/3)*(coefficientModels S C i).card) :
    ∀ j, RelPair ε (layerAverage C (score S) j) (T.ratio j) := by
  intro j
  rw [←L.layer_ratio C j]
  exact (normalize_counts hε hε1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) (coefficient_total_pos S C j)
    (by simpa only [coefficientModels_card,Bool.true_eq,↓reduceIte] using h (true,j))
    (by simpa only [coefficientModels_card,Bool.false_eq_true,↓reduceIte] using h (false,j))).2.2.2

theorem endpoint_event_accuracy (C : Causes r → Finset (Fin n)) (T : CoefficientTable r)
    {ε : ℝ} (hε : 0≤ε) (hε1 : ε≤1)
    (h : ∀ i, |T.value i-((coefficientModels S C i).card:ℝ)|≤(ε/3)*(coefficientModels S C i).card) :
    L.PhysicalAccuracy C ε (cachedEndpointCurve S C T) := by
  intro p hp
  rw [L.physical_fidelity_eq_latentCurve C p hp.1 hp.2,latentCurve_eq_bernstein,cachedEndpointCurve_eq]
  exact endpointCurve_relPair _ _ hε
    (layerAverage_range C (score S) (fun E => ⟨(score_range S E).1.le,(score_range S E).2⟩))
    (L.coefficient_event_relPair C T hε hε1 h) p hp

theorem shape_event_accuracy (C : Causes r → Finset (Fin n)) (T : CoefficientTable r)
    (hanti : Antitone (layerAverage C (score S)))
    {ε : ℝ} (hε : 0≤ε) (hε1 : ε≤1)
    (h : ∀ i, |T.value i-((coefficientModels S C i).card:ℝ)|≤(ε/3)*(coefficientModels S C i).card) :
    L.PhysicalAccuracy C ε (cachedShapeCurve S C T) := by
  intro p hp
  rw [L.physical_fidelity_eq_latentCurve C p hp.1 hp.2,latentCurve_eq_bernstein,cachedShapeCurve_eq]
  apply bernsteinCurve_relPair hp.1 hp.2
  exact shapeCoefficients_relPair _ _ hε hε1
    (layerAverage_range C (score S) (fun E => ⟨(score_range S E).1.le,(score_range S E).2⟩))
    hanti (L.coefficient_event_relPair C T hε hε1 h)

end Lift
end QecPhysical.Stabilizer
