import LatentUniformRunRefinement

/-! Actual fixed-machine latent reliability theorem: no assumed parser, evaluator,
controller, resource, seed-realization or run-refinement contract. Arbitrary C
uses endpoint-only repair. One coin event gives simultaneous all-p, both-tail
relative accuracy for the ordinary E-flagged erasure decoder. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine.Runtime
open scoped Classical
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open RationalOutput QecPhysical QecPhysical.Stabilizer
open OracleCost OracleCost.MultiTape OracleCost.WholeWrapperCandidate OracleCost.StoredCodeHashConfidence

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density PtE PsE T requestExtent) (hT : Monotone T)
include spec hT

/-- One finite-tape machine, chosen before all runtime rows, circuits, dimensions,
precisions and coins. Structural extent explicitly includes independent n+r.
Time keeps the concrete broad dispatch and padded-variable SAT-work bounds. -/
theorem endpoint_machine_guarantee : ∃ Pspace Ptime : PolynomialEnvelope, ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → a≤b → 0<c → 0<d →
    ∀ lift : Lift (rowSpace rows),
    let m := rationalRepetitionBudget (2*(r+1)) c d
    let B := rationalCellBudget a b
    let L := InputEncoding.paperLength rows C a b c d
    let N := CodeHash.repeatBits (Factory.length hD hd A n r) (Factory.width hD hd A n r) m
    let M := Assembly.theMachine E (program hD hd A density) assemblyIndices
    let timeBound := Ptime.eval L*(macroDispatchBound (keySize n r) r B m+1)+
      (3*kE+6)*oracleWorkBound rows C (gateConstant hD hd A) density B m PtE T
    (∀ w : Fin N → Bool,
      ∃ (run : Completed M (input rows C a b c d (List.ofFn w))) (v : Vector r),
        Final.Outputs M run (Assembly.outTape kE) v ∧
        run.time ≤ timeBound ∧ run.cells ≤ Pspace.eval L ∧
        EndpointStructure (rowSpace rows) (circuitMap C) v.curve ∧
        ∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
          TailExact (entanglementFidelity (lift.erasureFlagDecoder.comp
            (lift.iidLatentErasure (circuitMap C) p hp.1 hp.2)).map) (v.curve p)) ∧
    (1-(c:ℝ)/d)*(2:ℝ)^N ≤
      ((Finset.univ.filter (fun w : Fin N → Bool =>
        ∀ (run : Completed M (input rows C a b c d (List.ofFn w))) (v : Vector r),
          Final.Outputs M run (Assembly.outTape kE) v →
          lift.PhysicalAccuracy (circuitMap C) ((a:ℝ)/b) v.curve)).card : ℝ) := by
  obtain ⟨Ps,Pt,hR⟩ := uniform_run_refinement hD hd A density spec hT
  refine ⟨Ps,Pt,?_⟩
  intro n r rows C a b c d ha hab hc hdpos lift
  exact endpoint_machine_bridge rows C
    (actualCodeHash (Factory.system hD hd A n r)) (Factory.circuits hD hd A n r)
    spec.service.solver a b c d
    (Assembly.theMachine E (program hD hd A density) assemblyIndices) (Assembly.outTape kE)
    lift ha hab hc hdpos _ _ _ _
    (actualCodeHash_realizesCoins (Factory.system hD hd A n r) c d)
    (hR rows C a b c d ha hc)

end QecReliability.LatentMachine.Runtime
