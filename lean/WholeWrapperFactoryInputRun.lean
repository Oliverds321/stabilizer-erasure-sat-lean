import WholeWrapperFactoryInputBounds
import WholeWrapperEncodedInputRun

/-! Joint accepted-model composition. The actual all-length fixed-witness
family discharges the gate-linear premise, and the actual encoded SAT machine
bounds the exact SAT service time. This is still a macro run, not the complete
finite-tape lowering of controller, factory, sampler and boundaries. -/
namespace QecReliability.SharedCircuit.FixedLocalEmitter.AllLength
open Binary SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open CodeHash UniformAdapter ExpanderWalk FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.MultiTape

variable {D t : ℕ} (hD : D=16^384) (hd : D=256*t)
    (A : CertifiedParity (512*t) (64*t) t)

/-- No gate-family/resource contract is assumed: the defined family supplies
its proved structural linearity. One fixed A serves every input length. The
only algorithmic hypothesis is the stated external exact SAT machine; typed
boundary fidelity still awaits actual primitive lowering. -/
theorem fixed_factory_encoded_input_run {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    {k : ℕ} {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ] [Fintype Λ]
    {M : Machine k Γ Λ} {density : ℕ}
    {Ptime Pspace : PolynomialEnvelope} {T : ℕ → ℕ}
    (spec : EncodedSAT M density Ptime Pspace T) (hT : Monotone T)
    (a b c d : ℕ) (ha : 0<a) (hc : 0<c)
    (ω : Fin (2*rationalRepetitionBudget (2*(r+1)) c d+1) → Seed hD hd A (keySize n r))
    (shape : Bool) (ext : External)
    (hboundary : BoundaryCorrect rows C
      (stagesFor hD hd A (keyBits n r)) (circuitsFor hD hd A (keyBits n r)) spec.service
      (rationalRepetitionBudget (2*(r+1)) c d) ω density ext) :
    let H := stagesFor hD hd A (keyBits n r)
    let K := circuitsFor hD hd A (keyBits n r)
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*(r+1)) c d
    let L := InputEncoding.paperLength rows C a b c d
    let cache := prepare rows C H K spec.service.solver B m ω
    ∃ final totals events,
      Trace (keySize n r) r B m shape ext (initial (keySize n r) r m) totals events final ∧
      HasOutput final cache.good.entries cache.bad.entries
        (RationalOutput.LinearRepair.fromCache shape rows C cache) ∧
      drive (keySize n r) r B m shape ext
        (macroDispatchBound (keySize n r) r B m+1) (initial (keySize n r) r m)=some final ∧
      totals.calls=cache.calls ∧
      totals.oracleTime=(QuantumService.prepareMeasured rows C H K spec.service B m ω).oracleTime ∧
      totals.oracleTime≤totalCallCap (keySize n r) r B m *
        Ptime.eval (InputEncoding.queryPolynomial (gateConstant hD hd A) density L) *
          T (InputEncoding.queryVariableCoeff (gateConstant hD hd A) density*(L+1)) ∧
      totals.endpointTime=(ext.endpoint false).time+(ext.endpoint true).time ∧
      totals.calls≤totalCallCap (keySize n r) r B m ∧
      totals.dispatches≤macroDispatchBound (keySize n r) r B m ∧
      (∀ s, Reachable (keySize n r) r B m shape ext s →
        (representedBits s).length≤InputEncoding.retainedPolynomial (gateConstant hD hd A) density L) ∧
      (representedBits final).length≤InputEncoding.retainedPolynomial (gateConstant hD hd A) density L := by
  let H := stagesFor hD hd A (keyBits n r)
  let K := circuitsFor hD hd A (keyBits n r)
  have hg : ∀ scale seed, (K.program scale seed).gates≤gateConstant hD hd A*keySize n r :=
    fun scale seed => circuitsFor_gates_input hD hd A (keyBits n r) scale seed
  obtain ⟨final,totals,events,htrace,hout,hdrive,hcalls,htime,hendpoint,hcap,hdispatch,hall,hfinal,hinput⟩ :=
    initial_output_with_input_representation rows C H K spec.service a b c d ha hc ω
      (gateConstant hD hd A) density shape ext hboundary hg
  refine ⟨final,totals,events,htrace,hout,hdrive,hcalls,htime,?_,hendpoint,hcap,hdispatch,hall,hfinal⟩
  rw [htime]
  exact prepare_encoded_time_input rows C H K spec hT a b c d _ _ (gateConstant hD hd A) ω hg

end QecReliability.SharedCircuit.FixedLocalEmitter.AllLength
