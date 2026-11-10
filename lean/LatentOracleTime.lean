import LatentFactoryResourceBounds
import ResourceQuantumTime

/-! Actual positive-latent factory specialization of measured SAT time.
No wrapper, interpreter or reset time is included in this oracle-only bound. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine.Factory
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.StoredCodeHashConfidence

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t)
  {kE : ℕ} {ΓE ΛE : Type*} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : MultiTape.Machine kE ΓE ΛE} {density : ℕ}
  {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps T requestExtent) (hT : Monotone T)

include hT

/-- The actual full-coin generic walk, not the dispatched zero-length factory.
The rate argument is exactly the structural padded variable bound. -/
theorem prepare_resource_time {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program r n) (hr : 0<r) (B m : ℕ)
    (coins : Fin (CodeHash.repeatBits (length hD hd A n r)
      (width hD hd A n r) m) → Bool) :
    (QuantumService.prepareMeasured rows C (actualCodeHash (system hD hd A n r))
      (circuits hD hd A n r) spec.service B m
      (decodeCoins (length hD hd A n r) (width hD hd A n r) m coins)).oracleTime ≤
      2*(r+1)*(2*m+1)*trialCallBound (keySize n r) B *
        Pt.eval (queryExtentCap rows C density (gateConstant hD hd A * keySize n r)) *
        T (QuantumService.engineVariables rows C density (gateConstant hD hd A * keySize n r)) :=
  QuantumService.prepare_resource_engine_time rows C
    (actualCodeHash (system hD hd A n r)) (circuits hD hd A n r) spec hT
    B m (gateConstant hD hd A * keySize n r) (gates_of_latent_positive hD hd A hr)
    (decodeCoins (length hD hd A n r) (width hD hd A n r) m coins)

end QecReliability.LatentMachine.Factory
end
