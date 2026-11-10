import ResourceQuantumQueryBounds
import OracleCost.EnginePhysical

/-! Actual SAT service time aggregated over the existing measured preparation.
The polynomial resource argument includes dimension; the exponential/rate
argument remains the padded variable count, never the serialized payload. -/
set_option autoImplicit false
namespace QecReliability.OracleCost.QuantumService
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open WholeWrapperCandidate MultiTape

variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r))
    {k : ℕ} {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ] [Fintype Λ]
    {M : Machine k Γ Λ} {D : ℕ} {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ}
    (spec : ResourceEncodedSAT M D Pt Ps T requestExtent) (hT : Monotone T)

include hT

/-- Bounds on the actual base/cell service requests, including density padding. -/
theorem resource_engine_request_bounds (g : ℕ)
    (hg : ∀ s seed, (K.program s seed).gates ≤ g) :
    (∀ i pre, (spec.service.run (baseRequest rows C i pre)).time ≤
      Pt.eval (queryExtentCap rows C D g) * T (engineVariables rows C D g)) ∧
    (∀ i s seed pre, (spec.service.run (cellRequest rows C H K i s seed pre)).time ≤
      Pt.eval (queryExtentCap rows C D g) * T (engineVariables rows C D g)) := by
  constructor
  · intro i pre
    have hb := base_dimensions rows C g i pre
    exact (spec.dimension_request_bounds hT _ _ _ hb.1 hb.2).1
  · intro i s seed pre
    have hb := cell_dimensions rows C H K g i s seed pre (hg s seed)
    exact (spec.dimension_request_bounds hT _ _ _ hb.1 hb.2).1

/-- Exact old request aggregation, now for the additional resource interface. -/
theorem prepare_resource_engine_time (B m g : ℕ)
    (hg : ∀ s seed, (K.program s seed).gates ≤ g) (ω : Fin (2*m+1) → Ω) :
    (prepareMeasured rows C H K spec.service B m ω).oracleTime ≤
      2*(r+1)*(2*m+1)*trialCallBound (keySize n r) B *
        Pt.eval (queryExtentCap rows C D g) * T (engineVariables rows C D g) := by
  have hs := resource_engine_request_bounds rows C H K spec hT g hg
  have ht := prepareMeasured_time rows C H K spec.service B m _ ω
    (fun i => hs.1 i []) (fun i s seed pre _ => hs.2 i s seed pre)
  simpa only [Nat.mul_assoc] using ht

end QecReliability.OracleCost.QuantumService
