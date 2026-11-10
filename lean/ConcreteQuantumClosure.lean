import ExternalSATConcreteSolver
import LatentPolynomialMachineGuarantee

/-! The latent reliability machine instantiated with the verified SAT solver
and its canonical binary-query frontend. The engine, rate constant and resource
envelopes are selected before all runtime inputs. The fixed parity certificate
and physical lift hypotheses are retained from the generic quantum theorem. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine.Runtime

open scoped Classical
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open RationalOutput QecPhysical QecPhysical.Stabilizer
open OracleCost OracleCost.MultiTape OracleCost.WholeWrapperCandidate OracleCost.StoredCodeHashConfidence
open ExternalSATBridge

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t)

/-- One concrete finite-tape reliability machine with the SAT hypothesis
discharged. Its SAT rate is evaluated at the structural variable bound; its
polynomial space bound depends on structural input and encoded precision. -/
theorem concrete_polynomial_endpoint_machine_guarantee :
    ∃ (engine : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine)
      (rateConstant : ℝ) (Pspace Ptime : PolynomialEnvelope),
    0 < rateConstant ∧ ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → a≤b → 0<c → 0<d →
    ∀ lift : Lift (rowSpace rows),
    let m := rationalRepetitionBudget (2*(r+1)) c d
    let B := rationalCellBudget a b
    let L := InputEncoding.paperLength rows C a b c d
    let N := CodeHash.repeatBits (Factory.length hD hd A n r) (Factory.width hD hd A n r) m
    let E := PrimitiveTransport.machine (PrimitiveLink.queryMachine engine)
    let M := Assembly.theMachine E (program hD hd A 1) assemblyIndices
    let timeBound := Ptime.eval L*(b/a+1)^2*
      (RateMajorant.runtimeEnvelope rateConstant
        (InputEncoding.queryVariableCoeff (gateConstant hD hd A) 1*
          (satExtent rows C+1))+1)
    PhysicalTargetOptimality rows C lift ∧
    (∀ w : Fin N → Bool,
      ∃ (run : Completed M (input rows C a b c d (List.ofFn w))) (v : Vector r),
        Final.Outputs M run (Assembly.outTape (PrimitiveLink.queryMachine engine).tapeCount) v ∧
        run.time ≤ timeBound ∧ run.cells ≤ Pspace.eval L ∧
        EndpointStructure (rowSpace rows) (circuitMap C) v.curve ∧
        ∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
          TailExact (entanglementFidelity (lift.erasureFlagDecoder.comp
            (lift.iidLatentErasure (circuitMap C) p hp.1 hp.2)).map) (v.curve p)) ∧
    (1-(c:ℝ)/d)*(2:ℝ)^N ≤
      ((Finset.univ.filter (fun w : Fin N → Bool =>
        ∀ (run : Completed M (input rows C a b c d (List.ofFn w))) (v : Vector r),
          Final.Outputs M run (Assembly.outTape (PrimitiveLink.queryMachine engine).tapeCount) v →
          lift.PhysicalAccuracy (circuitMap C) ((a:ℝ)/b) v.curve)).card : ℝ) := by
  obtain ⟨engine, PtE, PsE, rateConstant, hrate, spec, hT⟩ :=
    ConcreteSolver.exists_resource_machine
  obtain ⟨Pspace, Ptime, hclosed⟩ :=
    polynomial_endpoint_machine_guarantee hD hd A 1 spec hT
  exact ⟨engine, rateConstant, Pspace, Ptime, hrate, hclosed⟩

end QecReliability.LatentMachine.Runtime
