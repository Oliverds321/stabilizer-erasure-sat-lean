import LatentFactorySeeds
import ResourceQuantumQueryBounds

/-! Positive-key-size bounds for the actual generic walk factory (not the
zero-dispatched factory). No C*q assertion is made at q=0. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine.Factory
open Binary SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.StoredCodeHashConfidence

/-- Abstract the dyadic data before specializing the large fixed certificate.
This keeps the gate-budget conversion at the small generic representation. -/
private theorem forward_gates_positive (X : DyadicXorData) (hb : 8 ≤ X.base)
    (G : MGGInput) {n r : ℕ} (hq : 0 < keySize n r)
    (scale : Fin (keySize n r+1))
    (seed : CodeHash.Seed (X.walkCode hb G (keySize n r)).L
      ((X.walkCode hb G (keySize n r)).steps+1)) :
    (((X.walkCircuits hb G (keySize n r)).forward (keyBits n r)).compiled.implementation.supplied.program scale seed).gates ≤ X.Cfixed * keySize n r := by
  exact (((X.walkCircuits hb G (keySize n r)).forward (keyBits n r)).hash_gates scale seed).trans
    (X.gates_positive hb G (keySize n r) hq)

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t)

/-- Same fixed constant as the positive dispatched factory, but proved directly
for the actual `Factory.circuits`, with its unchanged seed type and keyBits. -/
theorem gates_positive {n r : ℕ} (hq : 0 < keySize n r)
    (scale : Fin (keySize n r+1))
    (seed : CodeHash.Seed (length hD hd A n r) (width hD hd A n r)) :
    ((circuits hD hd A n r).program scale seed).gates ≤
      gateConstant hD hd A * keySize n r :=
  forward_gates_positive (data hD hd A) (base_ge_eight hD hd A) actualMGG hq scale seed

/-- The actual SAT-bearing latent branch has r>0, hence positive key size. -/
theorem gates_of_latent_positive {n r : ℕ} (hr : 0 < r)
    (scale : Fin (keySize n r+1))
    (seed : CodeHash.Seed (length hD hd A n r) (width hD hd A n r)) :
    ((circuits hD hd A n r).program scale seed).gates ≤
      gateConstant hD hd A * keySize n r :=
  gates_positive hD hd A (by unfold keySize; omega) scale seed

/-- Discharge the query-cap gate premise for the exact factory and decoded coins. -/
theorem concreteQuery_resource_qok {kE : ℕ} {ΓE ΛE : Type}
    [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE] (E : MultiTape.Machine kE ΓE ΛE)
    {n r : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n) (hr : 0 < r)
    (m : ℕ) (coins : Fin (CodeHash.repeatBits (length hD hd A n r)
      (width hD hd A n r) m) → Bool) (a b c d density : ℕ)
    (key : RequestKey) (valid : ValidKey (keySize n r) r m key) :
    (RegMachine.resourceSatOracle E density requestExtent
      (InputEncoding.queryExtentPolynomial (gateConstant hD hd A) density
        (InputEncoding.paperLength rows C a b c d))).qok
      (Final.concreteQuery rows C (actualCodeHash (system hD hd A n r))
        (circuits hD hd A n r) m
        (decodeCoins (length hD hd A n r) (width hD hd A n r) m coins) density key) :=
  WholeWrapperCandidate.concreteQuery_resource_qok rows C
    (actualCodeHash (system hD hd A n r)) (circuits hD hd A n r) E m
    (decodeCoins (length hD hd A n r) (width hD hd A n r) m coins)
    a b c d (gateConstant hD hd A) density (gates_of_latent_positive hD hd A hr) key valid

end QecReliability.LatentMachine.Factory
end
