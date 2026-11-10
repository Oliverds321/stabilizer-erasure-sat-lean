import LatentEndpointMachineGuarantee
import LatentTimePolynomial
import LatentEngineExtent

/-! Closed structural/precision resource form of the actual latent machine
reliability theorem. The SAT rate is evaluated at a fixed constant times
n+r+row-incidences+encoded circuit extent, never at quadratic payload length. -/
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
Time is quadratic in the rational inverse accuracy parameter; space depends
only on structural input and encoded precision, not numerical inverse accuracy. -/
theorem polynomial_endpoint_machine_guarantee : ∃ Pspace Ptime : PolynomialEnvelope, ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → a≤b → 0<c → 0<d →
    ∀ lift : Lift (rowSpace rows),
    let m := rationalRepetitionBudget (2*(r+1)) c d
    let B := rationalCellBudget a b
    let L := InputEncoding.paperLength rows C a b c d
    let N := CodeHash.repeatBits (Factory.length hD hd A n r) (Factory.width hD hd A n r) m
    let M := Assembly.theMachine E (program hD hd A density) assemblyIndices
    let timeBound := Ptime.eval L*(b/a+1)^2*
      (T (InputEncoding.queryVariableCoeff (gateConstant hD hd A) density*
        (satExtent rows C+1))+1)
    PhysicalTargetOptimality rows C lift ∧
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
  obtain ⟨Ps,Pt,hbase⟩ := endpoint_machine_guarantee hD hd A density spec hT
  obtain ⟨Q,hQ⟩ := time_bound_polynomial Pt PtE (gateConstant hD hd A) density (3*kE+6) T
  refine ⟨Ps,Q,?_⟩
  intro n r rows C a b c d ha hab hc hdpos lift
  obtain ⟨hruns,hprob⟩ := hbase rows C a b c d ha hab hc hdpos lift
  refine ⟨physicalTargetOptimality rows C lift,?_,hprob⟩
  intro coins
  obtain ⟨run,v,hout,htime,hspace,hend,htails⟩ := hruns coins
  refine ⟨run,v,hout,?_,hspace,hend,htails⟩
  have hraw := hQ rows C a b c d ha hc
  have hrate := hT (engine_variables_satExtent rows C (gateConstant hD hd A) density)
  have hrate' := Nat.mul_le_mul_left
    (Q.eval (InputEncoding.paperLength rows C a b c d)*(b/a+1)^2)
    (Nat.add_le_add_right hrate 1)
  exact htime.trans (hraw.trans hrate')

end QecReliability.LatentMachine.Runtime
