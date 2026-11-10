import TensorMachineGuarantee
import FixedQuantumClosure

/-! Concrete SAT and fixed-certificate specialization of the multiclass
machine. Isotropic stabilizer rows supply the physical lift. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
namespace QecReliability.TensorMachine.Runtime.FixedQuantum
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.MultiTape RationalOutput Final QecPhysical QecPhysical.Stabilizer
open ExternalSATBridge
open QecReliability.LatentMachine.Runtime.FixedQuantum

local notation "HD" => fixedDegree_eq
local notation "HS" => fixedDegree_scale
local notation "CERT" => fixedCertificate

/-- The engine, fixed reliability program and resource envelopes precede all
runtime inputs. The hypotheses concern the input code, observation map and
requested accuracy/confidence; none assumes a SAT solver or compiler bound. -/
theorem isotropic_tensor_machine_guarantee :
    ∃ (engine : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine)
      (rateConstant : ℝ) (Ptime Pspace : PolynomialEnvelope),
    0<rateConstant ∧ ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → a≤b → 0<c → 0<d →
    ∀ hS : rowSpace rows ≤ QecReliability.normalizer (symplectic n) (rowSpace rows),
    Monotone (TensorEncoding.circuitMap C) →
    let lift := QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS
    let L := Boundary.resourceSize rows C a b c d
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*slots ds) c d
    let N := CodeHash.repeatBits (Factory.length HD HS CERT n ds) (Factory.width HD HS CERT n ds) m
    let E := PrimitiveTransport.machine (PrimitiveLink.queryMachine engine)
    let M := Assembly.theMachine E (program HD HS CERT 1) (indices HD HS CERT 1)
    let outputTape := Assembly.outTape (PrimitiveLink.queryMachine engine).tapeCount
    (∀ coins : Fin N → Bool,
      ∃ (run : Completed M (input ds rows C a b c d (List.ofFn coins))) (v : Vector (slots ds-1)),
        Outputs M run outputTape v ∧
        run.time ≤ Ptime.eval L*(B+1)*(RateMajorant.runtimeEnvelope rateConstant
          (Boundary.variableCoefficient 1 (data HD HS CERT).Cfixed*
            (Boundary.satStructuralSize rows C+1))+1) ∧
        run.cells ≤ Pspace.eval L ∧
        lift.TensorPhysicalStructure (TensorEncoding.circuitMap C) (vectorCurve ds v)) ∧
    1-(c:ℝ)/d ≤ (uniformLaw (CodeHash.BitTape N)).prob
      (fun coins => ∀ (run : Completed M (input ds rows C a b c d (List.ofFn coins)))
        (v : Vector (slots ds-1)), Outputs M run outputTape v →
          lift.TensorPhysicalAccuracy (TensorEncoding.circuitMap C) ((a:ℝ)/b) (vectorCurve ds v)) := by
  obtain ⟨engine,PtE,PsE,rateConstant,hrate,spec,hT⟩ := ConcreteSolver.exists_resource_machine
  obtain ⟨Ptime,Pspace,hclosed⟩ := tensor_machine_guarantee HD HS CERT 1 spec hT
  refine ⟨engine,rateConstant,Ptime,Pspace,hrate,?_⟩
  intro n ds rows C a b c d ha hab hc hd hS hC
  obtain ⟨hruns,hshape,hprob⟩ := hclosed (n:=n) (ds:=ds) rows C a b c d ha hab hc hd
    (QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS) hC
  refine ⟨?_,hprob⟩
  intro coins
  obtain ⟨run,hout,htime,hspace⟩ := hruns coins
  exact ⟨run,_,hout,htime,hspace,hshape coins run _ hout⟩

end QecReliability.TensorMachine.Runtime.FixedQuantum
