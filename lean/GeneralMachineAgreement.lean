import GeneralMachineConcrete
import TensorMachineAgreement
import TensorRuntimeQueries
import Install.Components

/-! Fixed-factory agreement for the actual installed tensor controller.
Both query bytes and the inherited endpoint callback are discharged by code. -/

set_option autoImplicit false
noncomputable section
namespace QecReliability.TensorMachineG.Runtime
open QecReliability.TensorMachine QecReliability.TensorMachine.Runtime
open FL FL.Tm Trans.Wire Trans.Control
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.MultiTape

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)

abbrev source := Concrete.source (data hD hd A).base (data hD hd A).den density
  (Trans.HashCallees.encConsts D A) (Install.thePg hD hd A) (Trans.Hash.gNbr actualMGG)
abbrev program := Concrete.program (data hD hd A).base (data hD hd A).den density
  (Trans.HashCallees.encConsts D A) (Install.thePg hD hd A) (Trans.Hash.gNbr actualMGG)
abbrev indices := Concrete.indices (data hD hd A).base (data hD hd A).den density
  (Trans.HashCallees.encConsts D A) (Install.thePg hD hd A) (Trans.Hash.gNbr actualMGG)
abbrev controller := Program.controller (source hD hd A density) Concrete.query
  (data hD hd A).base (data hD hd A).den density
  (Trans.HashCallees.encConsts D A) (Install.thePg hD hd A) (Trans.Hash.gNbr actualMGG)

theorem valid : Program.Valid (source hD hd A density) Concrete.query Concrete.repair
    (data hD hd A).base (data hD hd A).den density
    (Trans.HashCallees.encConsts D A) (Install.thePg hD hd A) (Trans.Hash.gNbr actualMGG) :=
  Concrete.valid _ _ _ _ _ _ (Install.theHash_ok hD hd A density)

theorem endpoint_agrees {n : ℕ} (ds : List ℕ) (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program ds.sum n) (coins : List Bool) (side : Bool) :
    (controller hD hd A density).endpoint.den (contextData hD hd A ds rows C coins,side) =
      toR (Final.concreteEndpoint rows C side).value := by
  change (Program.endpointF _).den (contextData hD hd A ds rows C coins,side) = _
  simp only [Program.endpointF,bodySig_den,Program.endpointBody,tm_simp,contextData,
    ContextFL.externalData]
  exact LatentMachine.WrappersFL.endpointWF_den Install.wL
    LatentMachine.WrappersInstalled.indices Install.yR rows C _ coins side

variable {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ}
  {resource : SATRequest → ℕ} (spec : ResourceEncodedSAT E density Pt Ps T resource)

theorem extAgrees {n : ℕ} {ds : List ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program ds.sum n) (m : ℕ)
    (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds) m) → Bool) (s : Config)
    (validKey : ValidKey (keySize n ds.sum) (slots ds-1) m s.request) :
    ExtAgrees (controller hD hd A density) (contextData hD hd A ds rows C (List.ofFn coins))
      (external hD hd A density spec rows C m coins) s where
  query := RuntimeQueries.compile_agrees hD hd A density QueryInstalled.indices
    (source hD hd A density).length rows C m coins s.request validKey
  endpoint side := endpoint_agrees hD hd A density ds rows C (List.ofFn coins) side

end QecReliability.TensorMachineG.Runtime
end
