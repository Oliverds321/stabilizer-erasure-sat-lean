import PhysicalBridge.PhysicalCachedShape

/-! A once-prepared cache, deterministic structure/resources, and a separate
probabilistic accuracy event. Physical optimality is deterministic. -/
noncomputable section
namespace QecPhysical.Stabilizer
open QecReliability QecReliability.Binary
open QecReliability.SharedCircuit
open QecReliability.SharedCircuit.LatentEncoding
open QecReliability.SharedCircuit.ConcreteQuantum

def EndpointStructure {n r : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes r → Finset (Fin n)) (R : ℝ → ℝ) : Prop :=
  R 0=score S (C ∅) ∧ R 1=score S (C Finset.univ) ∧
    ∀ p ∈ Set.Icc (0:ℝ) 1, 0≤R p ∧ R p≤1

def ShapeStructure {n r : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes r → Finset (Fin n)) (R : ℝ → ℝ) : Prop :=
  AntitoneOn R (Set.Icc 0 1) ∧ R 0=score S (C ∅) ∧ R 1=score S (C Finset.univ) ∧
    ∀ p ∈ Set.Icc (0:ℝ) 1, score S (C Finset.univ)≤R p ∧ R p≤score S (C ∅) ∧ 0≤R p ∧ R p≤1

/-- Bounds only the original table; a materialized repaired vector is not included. -/
def RawCacheResources (n r B m : ℕ) (T : CoefficientTable r) : Prop :=
  T.calls≤2*(r+1)*(2*m+1)*trialCallBound (keySize n r) B ∧
  T.good.entries.length+T.bad.entries.length=2*(r+1) ∧
  T.payloadBits≤2*(r+1)*(keySize n r+(4*B+1).size+((2*m+1)*trialCallBound (keySize n r) B).size)

variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)

theorem prepare_raw_resources (B m : ℕ) (ω : Fin (2*m+1) → Ω) :
    RawCacheResources n r B m (prepare rows C H K solver B m ω) :=
  ⟨prepare_calls rows C H K solver B m ω,prepare_entry_count rows C H K solver B m ω,
    prepare_payload rows C H K solver B m ω⟩

namespace Lift
variable (L : Lift (rowSpace rows))

/-- Arbitrary latent circuit: exact endpoints/range on every seed; only accuracy is random. -/
theorem cached_physical_endpoint_confidence (B m : ℕ) (hB : 0<B)
    {ε δ : ℝ} (hε : 0<ε) (hε1 : ε≤1) (hcell : 16≤(ε/3)^2*(B:ℝ))
    (hrepeat : (2*(r+1):ℝ)*(1/2:ℝ)^(m+2)≤δ) :
    (∀ ω, let T := prepare rows C H K solver B m ω
      RawCacheResources n r B m T ∧ EndpointStructure (rowSpace rows) (circuitMap C)
        (cachedEndpointCurve (rowSpace rows) (circuitMap C) T)) ∧
    1-δ ≤ (repeatedLaw H.law m).prob (fun ω => L.PhysicalAccuracy (circuitMap C) ε
      (cachedEndpointCurve (rowSpace rows) (circuitMap C) (prepare rows C H K solver B m ω))) := by
  refine ⟨fun ω => ⟨prepare_raw_resources rows C H K solver B m ω,
    cachedEndpoint_structural _ _ _⟩,?_⟩
  apply (prepare_coefficients_confidence rows C H K solver B m hB hε hε1 hcell hrepeat).trans
  apply FiniteProbability.prob_mono
  intro ω hω
  exact L.endpoint_event_accuracy _ _ hε.le hε1 hω

/-- True coefficient antitonicity suffices; semantic monotonicity of C is not required. -/
theorem cached_physical_shape_confidence_of_layers_antitone
    (hanti : Antitone (layerAverage (circuitMap C) (score (rowSpace rows))))
    (B m : ℕ) (hB : 0<B) {ε δ : ℝ} (hε : 0<ε) (hε1 : ε≤1)
    (hcell : 16≤(ε/3)^2*(B:ℝ)) (hrepeat : (2*(r+1):ℝ)*(1/2:ℝ)^(m+2)≤δ) :
    (∀ ω, let T := prepare rows C H K solver B m ω
      RawCacheResources n r B m T ∧ ShapeStructure (rowSpace rows) (circuitMap C)
        (cachedShapeCurve (rowSpace rows) (circuitMap C) T)) ∧
    1-δ ≤ (repeatedLaw H.law m).prob (fun ω => L.PhysicalAccuracy (circuitMap C) ε
      (cachedShapeCurve (rowSpace rows) (circuitMap C) (prepare rows C H K solver B m ω))) := by
  have ho : score (rowSpace rows) (circuitMap C Finset.univ)≤score (rowSpace rows) (circuitMap C ∅) := by
    simpa only [layerAverage_fin_zero,layerAverage_fin_last] using hanti (show (0:Fin (r+1))≤Fin.last r from Nat.zero_le r)
  refine ⟨fun ω => ⟨prepare_raw_resources rows C H K solver B m ω,
    cachedShape_structural _ _ _ ho⟩,?_⟩
  apply (prepare_coefficients_confidence rows C H K solver B m hB hε hε1 hcell hrepeat).trans
  apply FiniteProbability.prob_mono
  intro ω hω
  exact L.shape_event_accuracy _ _ hanti hε.le hε1 hω

end Lift

theorem prepare_shape_eq_repairedCurve (ε δ : ℝ) (hδ : 0<δ)
    (ω : Fin (2*repetitionBudget (Fintype.card (CoefficientIndex r)) δ hδ+1) → Ω) :
    cachedShapeCurve (rowSpace rows) (circuitMap C)
      (prepare rows C H K solver (cellBudget (ε/3))
        (repetitionBudget (Fintype.card (CoefficientIndex r)) δ hδ) ω) =
      repairedCurve rows C H K solver ε δ hδ ω := by
  rw [cachedShapeCurve_eq]
  unfold repairedCurve shapeCorrectedCurve
  apply congrArg (fun g => bernsteinCurve r (shapeCoefficients (layerAverage (circuitMap C) (score (rowSpace rows))) g))
  funext j
  simp only [CoefficientTable.ratio,CoefficientTable.value,Bool.false_eq_true,↓reduceIte]
  rw [(prepare_values rows C H K solver ε δ hδ ω j).1,
    (prepare_values rows C H K solver ε δ hδ ω j).2]

namespace Lift
variable (L : Lift (rowSpace rows))

/-- Direct reuse of M12's canonical shape-confidence theorem, rewritten through
the actual prepared cache. Shape and resource claims hold on every seed. -/
theorem cached_physical_shape_confidence
    (hC : ∀ a b, a⊆b → circuitMap C a⊆circuitMap C b)
    {ε δ : ℝ} (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ) :
    (∀ ω, let B := cellBudget (ε/3)
      let m := repetitionBudget (Fintype.card (CoefficientIndex r)) δ hδ
      let T := prepare rows C H K solver B m ω
      RawCacheResources n r B m T ∧ ShapeStructure (rowSpace rows) (circuitMap C)
        (cachedShapeCurve (rowSpace rows) (circuitMap C) T)) ∧
    1-δ ≤ (repeatedLaw H.law (repetitionBudget (Fintype.card (CoefficientIndex r)) δ hδ)).prob
      (fun ω => L.PhysicalAccuracy (circuitMap C) ε
        (cachedShapeCurve (rowSpace rows) (circuitMap C)
          (prepare rows C H K solver (cellBudget (ε/3))
            (repetitionBudget (Fintype.card (CoefficientIndex r)) δ hδ) ω))) := by
  refine ⟨fun ω => ⟨prepare_raw_resources rows C H K solver _ _ ω,
    cachedShape_structural _ _ _ (score_antitone _ L.isotropic (hC ∅ Finset.univ (Finset.empty_subset _)))⟩,?_⟩
  apply (shape_curve_confidence rows L.isotropic C hC H K solver hε hε1 hδ).trans
  apply FiniteProbability.prob_mono
  intro ω hω p hp
  rw [L.physical_fidelity_eq_latentCurve _ p hp.1 hp.2,
    prepare_shape_eq_repairedCurve rows C H K solver ε δ hδ ω]
  exact (hω.2.2.2 p hp).1

end Lift
end QecPhysical.Stabilizer
