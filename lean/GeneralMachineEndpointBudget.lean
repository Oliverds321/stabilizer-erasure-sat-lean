import GeneralMachineAgreement
import TensorMachineEndpointBudget
import TensorArgumentMagnitude
import LatentEndpointInputBudget

/-! Bounds for the inherited endpoint callback in the common counting-step
analysis. Its exponentially valued denominator is charged by bit storage. -/
set_option autoImplicit false
noncomputable section

namespace QecReliability.TensorMachineG.Runtime
open QecReliability.TensorMachine QecReliability.TensorMachine.Runtime
open FL Trans.Control Trans.Query.Bound Trans.BoundsQH Trans.BoundsRest
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)

theorem endpoint_budget : ∃ P : PolynomialEnvelope, ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds) (rationalRepetitionBudget (2*slots ds) c d)) → Bool)
      (side : Bool),
    let X := contextData hD hd A ds rows C (List.ofFn coins)
    let L := Boundary.resourceSize rows C a b c d
    (controller hD hd A density).endpoint.cost (X,side) ≤ P.eval L ∧
    (controller hD hd A density).endpoint.depth (X,side) ≤ P.eval L ∧
    (controller hD hd A density).endpoint.msize (X,side) ≤ P.eval L := by
  obtain ⟨Pa,ha⟩ := QueryResources.argument_bound hD hd A
  obtain ⟨k,c,h⟩ := Program.endpoint_resources ((source hD hd A density).length+1)
  have hg : Assembly.PolyBounded (fun L => G k c (Pa.eval L)) := G_comp_pb k c (by poly_bounded)
  obtain ⟨P,hP⟩ := hg.envelope
  refine ⟨P,?_⟩
  intro n ds rows C a b c' d hapos hc coins side
  let L := Boundary.resourceSize rows C a b c' d
  let X := contextData hD hd A ds rows C (List.ofFn coins)
  have hx := ha rows C a b c' d hapos hc coins (.base false 0 0) (by constructor <;> omega)
  have hx' : mag (.prod ContextFL.TX .bool) (X,side) ≤ Pa.eval L := by
    change mag ContextFL.TX X+8+1 ≤ Pa.eval L at hx
    change mag ContextFL.TX X+1+1 ≤ Pa.eval L
    omega
  obtain ⟨ht,hdp,hm⟩ := h (X,side)
  have hgrow := (G_mono (k := k) (c := c) le_rfl le_rfl hx').trans (hP L)
  exact ⟨ht.trans hgrow,hdp.trans hgrow,hm.trans hgrow⟩

end QecReliability.TensorMachineG.Runtime
