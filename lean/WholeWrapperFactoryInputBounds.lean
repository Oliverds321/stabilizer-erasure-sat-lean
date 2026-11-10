import WholeWrapperInputBounds
import FixedWitnessAllLengthFactoryCandidate

/-! Specialize the representation
measure theorem to the actual all-length fixed-witness factory. This removes
the generic gate-linear premise using the factory's defined unchanged program.
The finite local certificate is factory data, not a wrapper resource contract. -/
namespace QecReliability.SharedCircuit.FixedLocalEmitter.AllLength
open Binary SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open CodeHash UniformAdapter ExpanderWalk FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate

variable {D t : ℕ} (hD : D=16^384) (hd : D=256*t)
    (A : CertifiedParity (512*t) (64*t) t)

/-- Program-valued reindexing changes neither gates nor seed representation. -/
theorem circuitsFor_gates_input {X : Type} {q : ℕ} (e : X ≃ BitModels q)
    (scale : Fin (q+1)) (seed : Seed hD hd A q) :
    ((circuitsFor hD hd A e).program scale seed).gates≤gateConstant hD hd A*q :=
  gates_linear hD hd A q scale seed

/-- No assumed h, gate bound, scalar input-length premise, QueryBound, or
endpoint-width premise: every reachable macro field is bounded for the actual
fixed-factory H/K pair. Parser, seed generation/storage, and physical primitive
workspace remain distinct machine-refinement obligations. -/
theorem reachable_wholewrapper_input_representation {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n) (service : SATService)
    (a b c d : ℕ) (ha : 0<a) (hc : 0<c)
    (ω : Fin (2*rationalRepetitionBudget (2*(r+1)) c d+1) → Seed hD hd A (keySize n r))
    (density : ℕ) (shape : Bool) (ext : External)
    (hboundary : BoundaryCorrect rows C
      (stagesFor hD hd A (keyBits n r)) (circuitsFor hD hd A (keyBits n r)) service
      (rationalRepetitionBudget (2*(r+1)) c d) ω density ext)
    {s : Config} (hreach : Reachable (keySize n r) r (rationalCellBudget a b)
      (rationalRepetitionBudget (2*(r+1)) c d) shape ext s) :
    (representedBits s).length≤
      InputEncoding.retainedPolynomial (gateConstant hD hd A) density
        (InputEncoding.paperLength rows C a b c d) :=
  InputEncoding.reachable_input_representation rows C
    (stagesFor hD hd A (keyBits n r)) (circuitsFor hD hd A (keyBits n r)) service
    a b c d ha hc ω (gateConstant hD hd A) density shape ext hboundary
    (fun scale seed => circuitsFor_gates_input hD hd A (keyBits n r) scale seed) hreach

end QecReliability.SharedCircuit.FixedLocalEmitter.AllLength
