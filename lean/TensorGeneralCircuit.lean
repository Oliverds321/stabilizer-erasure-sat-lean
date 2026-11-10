import GeneralMachineGuarantee
import TensorFixedQuantumStrong

/-! Closed multiclass machine theorem for GENERAL (not necessarily monotone)
latent circuits. The fixed machine is the tensor machine with the full shape
repair replaced by corner replacement (`GeneralRepairFL.generalF`): the corner
coefficients (each class all-zero or all-one) are the exact dyadic physical
scores and every other coefficient is the normalized cached count estimate.
No monotonicity hypothesis appears. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
namespace QecReliability.TensorMachineG.Runtime.FixedQuantum
open QecReliability.TensorMachine QecReliability.TensorMachine.Runtime
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.MultiTape RationalOutput Final QecPhysical QecPhysical.Stabilizer
open ExternalSATBridge TensorBernstein TensorLatent
open QecReliability.LatentMachine.Runtime.FixedQuantum
open QecReliability.TensorMachine.Runtime.FixedQuantum

local notation "HD" => fixedDegree_eq
local notation "HS" => fixedDegree_scale
local notation "CERT" => explicitCertificate

theorem isotropic_tensor_machine_guarantee_general :
    ∃ (engine : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine)
      (rateConstant : ℝ) (Ptime Pspace : PolynomialEnvelope),
    0<rateConstant ∧ ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → a≤b → 0<c → 0<d →
    ∀ hS : rowSpace rows ≤ QecReliability.normalizer (symplectic n) (rowSpace rows),
    let lift := QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS
    let f := multivariateCoefficients (rowSpace rows) (TensorEncoding.circuitMap C)
    let L := Boundary.resourceSize rows C a b c d
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*slots ds) c d
    let N := CodeHash.repeatBits (Factory.length HD HS CERT n ds) (Factory.width HD HS CERT n ds) m
    let E := PrimitiveTransport.machine (PrimitiveLink.queryMachine engine)
    let M := Assembly.theMachine E (QecReliability.TensorMachineG.Runtime.program HD HS CERT 1)
      (QecReliability.TensorMachineG.Runtime.indices HD HS CERT 1)
    let outputTape := Assembly.outTape (PrimitiveLink.queryMachine engine).tapeCount
    -- (a) the target is the Bernstein curve of `f`, and it is optimal over all recoveries
    (∀ p (hp : cube ds p),
      entanglementFidelity (lift.erasureFlagDecoder.comp
          (lift.multivariateLatentErasure (TensorEncoding.circuitMap C) p hp)).map =
        curve ds f p ∧
      ∀ Q : Channel (ErasureFlagOutput n) lift.LogicalIndex,
        entanglementFidelity (Q.comp
            (lift.multivariateLatentErasure (TensorEncoding.circuitMap C) p hp)).map ≤
          entanglementFidelity (lift.erasureFlagDecoder.comp
            (lift.multivariateLatentErasure (TensorEncoding.circuitMap C) p hp)).map) ∧
    -- (b) every coin string: completed run, output, resources, table and curve structure
    (∀ coins : Fin N → Bool,
      ∃ (run : Completed M (input ds rows C a b c d (List.ofFn coins))) (v : Vector (slots ds-1)),
        Outputs M run outputTape v ∧
        run.time ≤ Ptime.eval L*(B+1)*(RateMajorant.runtimeEnvelope rateConstant
          (Boundary.variableCoefficient 1 (data HD HS CERT).Cfixed*
            (Boundary.satStructuralSize rows C+1))+1) ∧
        run.cells ≤ Pspace.eval L ∧
        -- every output coefficient lies in the unit interval
        (∀ j, 0 ≤ vectorTable ds v j ∧ vectorTable ds v j ≤ 1) ∧
        -- every corner coefficient is the exact physical score
        (∀ b : Corner ds, vectorTable ds v (cornerIndex ds b) = f (cornerIndex ds b) ∧
          vectorTable ds v (cornerIndex ds b) =
            erasureScore (rowSpace rows) (TensorEncoding.circuitMap C (cornerCauses ds b))) ∧
        -- zero-infidelity coefficients are identified exactly
        (∀ j, vectorTable ds v j = 1 ↔ f j = 1) ∧
        -- the output curve lies in [0,1] on the cube and is exact at every corner
        TensorGeneral.GeneralStructure rows (TensorEncoding.circuitMap C) lift (vectorCurve ds v)) ∧
    -- (c) one coin event gives two-tail accuracy on the whole parameter cube
    1-(c:ℝ)/d ≤ (uniformLaw (CodeHash.BitTape N)).prob
      (fun coins => ∀ (run : Completed M (input ds rows C a b c d (List.ofFn coins)))
        (v : Vector (slots ds-1)), Outputs M run outputTape v →
          lift.TensorPhysicalAccuracy (TensorEncoding.circuitMap C) ((a:ℝ)/b) (vectorCurve ds v)) := by
  obtain ⟨engine,PtE,PsE,rateConstant,hrate,spec,hT⟩ := ConcreteSolver.exists_resource_machine
  obtain ⟨Ptime,Pspace,hclosed⟩ :=
    QecReliability.TensorMachineG.Runtime.tensor_machine_guarantee_general HD HS CERT 1 spec hT
  refine ⟨engine,rateConstant,Ptime,Pspace,hrate,?_⟩
  intro n ds rows C a b c d ha hab hc hd hS
  obtain ⟨hruns,_,hprob⟩ := hclosed (n:=n) (ds:=ds) rows C a b c d ha hab hc hd
    (QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS)
  refine ⟨?_,?_,hprob⟩
  · intro p hp
    have h := (QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS).multivariateLatentErasure_optimum
      (TensorEncoding.circuitMap C) p hp
    refine ⟨h.1, fun Q => ?_⟩
    rw [h.1]
    exact h.2 Q
  · intro coins
    obtain ⟨run,hout,htime,hspace⟩ := hruns coins
    obtain ⟨hstruct,_⟩ := GeneralAlgorithm.vector_guarantee HD HS CERT rows C spec.service.solver
      (QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS) a b c d ha hab hc hd
    obtain ⟨h1,h2,h3,h4⟩ := hstruct coins
    exact ⟨run,_,hout,htime,hspace,h1,h2,h3,h4⟩

/-- The machine of `isotropic_tensor_machine_guarantee_general` is the generic
tensor controller assembled over the general installation, with the general
callback (corner replacement) in the repair position. -/
theorem general_program_eq :
    QecReliability.TensorMachineG.Runtime.program HD HS CERT 1 =
      Program.program (GeneralInstalled.program (data HD HS CERT).base (data HD HS CERT).den 1
          (Trans.HashCallees.encConsts fixedDegree CERT) (Install.thePg HD HS CERT) (Trans.Hash.gNbr actualMGG))
        QueryInstalled.query GeneralInstalled.callback (data HD HS CERT).base (data HD HS CERT).den 1
        (Trans.HashCallees.encConsts fixedDegree CERT) (Install.thePg HD HS CERT) (Trans.Hash.gNbr actualMGG) :=
  rfl

theorem general_program_length :
    (QecReliability.TensorMachineG.Runtime.program HD HS CERT 1).length = 387 :=
  QecReliability.TensorMachineG.Concrete.program_length _ _ _ _ _ _

end QecReliability.TensorMachineG.Runtime.FixedQuantum

#print axioms QecReliability.TensorMachineG.Runtime.FixedQuantum.isotropic_tensor_machine_guarantee_general
