import LatentFactorySeeds
import LatentControllerInstalled
import Install.Components

/-! The installed latent callbacks agree with concrete quantum queries and
exact endpoints for the actual fixed factory and literal decoded coins.
No assumed hash/query denotation or ExtAgrees premise remains. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine.Runtime
open FL Trans.Wire Trans.Control
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.StoredCodeHashConfidence

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)

def program : FL.Program :=
  ControllerInstalled.program (data hD hd A).base (data hD hd A).den density
    (Trans.HashCallees.encConsts D A) (Install.thePg hD hd A) (Trans.Hash.gNbr actualMGG)

def controller : Trans.Control.Ix TX :=
  ControllerInstalled.indices (data hD hd A).base (data hD hd A).den density
    (Trans.HashCallees.encConsts D A) (Install.thePg hD hd A) (Trans.Hash.gNbr actualMGG)

/-- Fixed-certificate validity discharges the last original hash-callee premise. -/
theorem step_valid : ∀ x, (EndpointControllerFL.stepF (controller hD hd A density)).ValidAt
    (program hD hd A density) x :=
  ControllerInstalled.step_valid _ _ _ _ _ _ (Install.theHash_ok hD hd A density)

def contextData {n r : ℕ} (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (m : ℕ) (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n r)
      (Factory.width hD hd A n r) m) → Bool) : TX.den :=
  ContextFL.externalData (data hD hd A).base (data hD hd A).den rows C (List.ofFn coins)

theorem compile_agrees {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program r n) (m : ℕ)
    (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n r)
      (Factory.width hD hd A n r) m) → Bool) (key : RequestKey)
    (valid : ValidKey (keySize n r) r m key) :
    (controller hD hd A density).compile.den
      (contextData hD hd A rows C m coins,encKey key) =
      Final.concreteQuery rows C (actualCodeHash (Factory.system hD hd A n r))
        (Factory.circuits hD hd A n r) m
        (decodeCoins (Factory.length hD hd A n r) (Factory.width hD hd A n r) m coins)
        density key := by
  change (WrappersFL.compileF Install.wL WrappersInstalled.indices Install.queryFn
    (Install.theHash hD hd A) (data hD hd A).base (data hD hd A).den density).den _ = _
  have hh : ∀ x, (Install.theHash hD hd A).den x =
      Trans.Hash.hashPlain x.1 x.2.1 x.2.2.1 (Install.thePg hD hd A)
        (Trans.Hash.gNbr actualMGG) x.2.2.2.1 x.2.2.2.2 := fun _ => rfl
  cases key with
  | base side j rep =>
    rw [← Trans.Query.queryFn_base rows C _ _ _ _ density side j rep valid]
    unfold contextData ContextFL.externalData
    rw [WrappersFL.compileF_den_base]
    rfl
  | cell side j rep scale pre =>
    rw [← Trans.Query.queryFn_cell rows C _ _ _ _ density side j rep scale pre valid]
    unfold contextData ContextFL.externalData
    rw [WrappersFL.compileF_den_cell,hh,Factory.seed_length,
      Factory.decode_slice,Factory.hash_program hD hd A n r ⟨scale,valid.2.2.1⟩ _
        (Factory.slice_length _ _ m coins rep valid.2.1)]
    simp only [Install.queryFn,Trans.Query.queryFnF_den,Trans.Query.cellArg]
    rw [show Install.thePg hD hd A =
      (fun ell => Trans.Query.encProg ((data hD hd A).program ell)) from rfl]

theorem endpoint_agrees {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program r n) (m : ℕ)
    (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n r)
      (Factory.width hD hd A n r) m) → Bool) (side : Bool) :
    (controller hD hd A density).endpoint.den
      (contextData hD hd A rows C m coins,side) =
      Trans.Control.toR (Final.concreteEndpoint rows C side).value := by
  exact WrappersFL.endpointWF_den Install.wL WrappersInstalled.indices Install.yR
    rows C _ _ side

section External
variable {kE : ℕ} {ΓE ΛE : Type*} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : MultiTape.Machine kE ΓE ΛE} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}
  (spec : EncodedSAT E density PtE PsE T)

def external {n r : ℕ} (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (m : ℕ) (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n r)
      (Factory.width hD hd A n r) m) → Bool) : External :=
  Final.concreteExternal rows C (actualCodeHash (Factory.system hD hd A n r))
    (Factory.circuits hD hd A n r) m
    (decodeCoins (Factory.length hD hd A n r) (Factory.width hD hd A n r) m coins) density spec

/-- Actual callbacks, not a new semantic agreement assumption. -/
theorem extAgrees {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program r n) (m : ℕ)
    (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n r)
      (Factory.width hD hd A n r) m) → Bool) (s : Config)
    (valid : ValidKey (keySize n r) r m s.request) :
    ExtAgrees (controller hD hd A density) (contextData hD hd A rows C m coins)
      (external hD hd A density spec rows C m coins) s where
  query := compile_agrees hD hd A density rows C m coins s.request valid
  endpoint side := endpoint_agrees hD hd A density rows C m coins side

end External
end QecReliability.LatentMachine.Runtime
