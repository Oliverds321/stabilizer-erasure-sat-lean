import ConcreteQuantumClosure
import PhysicalBridge.GeneralStabilizer
import QecReliability.PackedSemanticBridgeCandidate

/-! A symbolic fixed-certificate specialization of the concrete reliability
machine. No certificate search or checker is executed by this module. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine.Runtime.FixedQuantum

open scoped Classical
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open RationalOutput QecPhysical QecPhysical.Stabilizer
open OracleCost OracleCost.MultiTape OracleCost.WholeWrapperCandidate OracleCost.StoredCodeHashConfidence
open ExternalSATBridge

def fixedDegree : ℕ := 16 ^ 384
def fixedScale : ℕ := 2 ^ 1528

theorem fixedDegree_eq : fixedDegree = 16 ^ 384 := rfl

theorem fixedDegree_scale : fixedDegree = 256 * fixedScale := by
  unfold fixedDegree fixedScale
  exact FiniteLocalCountingCandidate.fixed_degree_reparametrization

theorem fixedScale_pos : 0 < fixedScale :=
  pow_pos (by decide : 0 < (2 : ℕ)) 1528

/-- The explicit selector proves inhabitation; classical choice keeps this
closed astronomical certificate out of executable module initialization. -/
noncomputable def fixedCertificate :
    CertifiedParity (512 * fixedScale) (64 * fixedScale) fixedScale :=
  Classical.choice
    (show Nonempty (CertifiedParity (512 * fixedScale) (64 * fixedScale) fixedScale) from
      ⟨PackedSemanticBridgeCandidate.localCertified fixedScale fixedScale_pos⟩)

/-- No SAT or code-certificate hypothesis remains. The physical lift and
runtime accuracy/confidence assumptions retain their original quantifiers. -/
theorem fixed_polynomial_endpoint_machine_guarantee :
    ∃ (engine : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine)
      (rateConstant : ℝ) (Pspace Ptime : PolynomialEnvelope),
    0 < rateConstant ∧ ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → a≤b → 0<c → 0<d →
    ∀ lift : Lift (rowSpace rows),
    let m := rationalRepetitionBudget (2*(r+1)) c d
    let L := InputEncoding.paperLength rows C a b c d
    let N := CodeHash.repeatBits
      (Factory.length fixedDegree_eq fixedDegree_scale fixedCertificate n r)
      (Factory.width fixedDegree_eq fixedDegree_scale fixedCertificate n r) m
    let E := PrimitiveTransport.machine (PrimitiveLink.queryMachine engine)
    let M := Assembly.theMachine E
      (program fixedDegree_eq fixedDegree_scale fixedCertificate 1) assemblyIndices
    let timeBound := Ptime.eval L*(b/a+1)^2*
      (RateMajorant.runtimeEnvelope rateConstant
        (InputEncoding.queryVariableCoeff
          (gateConstant fixedDegree_eq fixedDegree_scale fixedCertificate) 1*
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
          lift.PhysicalAccuracy (circuitMap C) ((a:ℝ)/b) v.curve)).card : ℝ) :=
  concrete_polynomial_endpoint_machine_guarantee
    fixedDegree_eq fixedDegree_scale fixedCertificate

/-- For isotropic stabilizer rows, the physical lift is constructed from the
row space. The engine and polynomial envelopes are fixed before all inputs. -/
theorem isotropic_polynomial_endpoint_machine_guarantee :
    ∃ (engine : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine)
      (rateConstant : ℝ) (Pspace Ptime : PolynomialEnvelope),
    0 < rateConstant ∧ ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → a≤b → 0<c → 0<d →
    ∀ hS : rowSpace rows ≤ QecReliability.normalizer (symplectic n) (rowSpace rows),
    let lift := QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS
    let m := rationalRepetitionBudget (2*(r+1)) c d
    let L := InputEncoding.paperLength rows C a b c d
    let N := CodeHash.repeatBits
      (Factory.length fixedDegree_eq fixedDegree_scale fixedCertificate n r)
      (Factory.width fixedDegree_eq fixedDegree_scale fixedCertificate n r) m
    let E := PrimitiveTransport.machine (PrimitiveLink.queryMachine engine)
    let M := Assembly.theMachine E
      (program fixedDegree_eq fixedDegree_scale fixedCertificate 1) assemblyIndices
    let timeBound := Ptime.eval L*(b/a+1)^2*
      (RateMajorant.runtimeEnvelope rateConstant
        (InputEncoding.queryVariableCoeff
          (gateConstant fixedDegree_eq fixedDegree_scale fixedCertificate) 1*
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
  obtain ⟨engine, rateConstant, Pspace, Ptime, hrate, hclosed⟩ :=
    fixed_polynomial_endpoint_machine_guarantee
  refine ⟨engine, rateConstant, Pspace, Ptime, hrate, ?_⟩
  intro n r rows C a b c d ha hab hc hd hS
  exact hclosed rows C a b c d ha hab hc hd
    (QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS)

end QecReliability.LatentMachine.Runtime.FixedQuantum
