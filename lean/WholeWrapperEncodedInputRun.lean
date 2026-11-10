import WholeWrapperInputRun

/-! The external SAT assumption backs the exact service time used by the
actual macro run. This charges only SAT-machine executions; local macro and
frontend/endpoint costs are intentionally not mislabelled physical total time. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open MultiTape

/-- The source service time, and hence the actual macro trace's identical
oracleTime, has one multiplicative SAT-time factor. Query representation growth
changes only the fixed polynomial overhead, never an exponent of T. -/
theorem prepare_encoded_time_input
    {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r))
    {k : ℕ} {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ] [Fintype Λ]
    {M : Machine k Γ Λ} {D : ℕ} {Ptime Pspace : PolynomialEnvelope} {T : ℕ → ℕ}
    (spec : EncodedSAT M D Ptime Pspace T) (hT : Monotone T)
    (a b c d B m h : ℕ) (ω : Fin (2*m+1) → Ω)
    (hg : ∀ scale seed, (K.program scale seed).gates≤h*keySize n r) :
    (QuantumService.prepareMeasured rows C H K spec.service B m ω).oracleTime≤
      totalCallCap (keySize n r) r B m *
        Ptime.eval (InputEncoding.queryPolynomial h D (InputEncoding.paperLength rows C a b c d)) *
          T (InputEncoding.queryVariableCoeff h D*(InputEncoding.paperLength rows C a b c d+1)) := by
  have old := QuantumService.prepare_engine_time rows C H K spec hT B m
    (h*keySize n r) hg ω
  have hp := Ptime.monotone (InputEncoding.engineInputBound_input_polynomial rows C a b c d h D)
  have ht := hT (InputEncoding.engine_variables_input_bound rows C a b c d h D)
  have bounded := old.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hp) ht)
  simpa only [totalCallCap,trialCallCap,prefixCallCap,trialCallBound] using bounded

end QecReliability.OracleCost.WholeWrapperCandidate
