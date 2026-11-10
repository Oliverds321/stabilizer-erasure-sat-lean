import GeneralMachineAgreement
import GeneralReachableBounds
import TensorMachineFinishResources

/-! Uniform input envelopes for the actual final controller iteration and the
complete encoded repaired state subsequently observed and serialized. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
namespace QecReliability.TensorMachineG.Runtime
open QecReliability.TensorMachine QecReliability.TensorMachine.Runtime
open FL Trans.Control
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.MultiTape RationalOutput

private theorem finish_polynomial (Ps Pr : PolynomialEnvelope) :
    Assembly.PolyBounded (fun L => ControllerFL.finalStepBudget (Ps.eval L) (Pr.eval L)+
      Ps.eval L+Pr.eval L+100) := by
  unfold ControllerFL.finalStepBudget
  poly_bounded

/-- All arithmetic is proved with symbolic bounds before specializing to the
fixed certificate, whose constants need never be evaluated. -/
private theorem finish_package (x : Ix ContextFL.TX)
    (repair : FnSig ControllerFL.RepairArg (.list TR))
    (fi di si q r B m : ℕ) (X : ContextFL.TX.den) (s : Config) (S R U : ℕ)
    (hpc : s.pc=.endpointZero)
    (hs : (Ty.enc (TArg ContextFL.TX) (encCtx q r B m X,encCfg s)).size≤S)
    (hr : CallBounds repair (X,s.goodTable,s.badTable) R R R)
    (ho : (Ty.enc (.list TR) (repair.den (X,s.goodTable,s.badTable))).size≤R)
    (hU : ControllerFL.finalStepBudget S R+S+R+100≤U) :
    CallBounds (ControllerFL.stepF x repair fi di si) (encCtx q r B m X,encCfg s) U U U ∧
    ∀ values : List Ratio, repair.den (X,s.goodTable,s.badTable)=values.map toR →
      (Ty.enc (TArg ContextFL.TX)
        (encCtx q r B m X,encCfg {s with pc := .done,output := values})).size≤U := by
  have hp : (encCfg s).1.1=14 := by change pcCode s.pc=14; rw [hpc]; rfl
  obtain ⟨ht,hd,hm⟩ := ControllerFL.finish_resources x repair fi di si
    (encCtx q r B m X,encCfg s) S R hp hs hr.time hr.depth hr.space ho
  constructor
  · refine ⟨by omega,?_,by omega,by omega⟩
    change ((TArg ContextFL.TX).enc (encCtx q r B m X,encCfg s)).size ≤ U
    exact hs.trans (by omega)
  · intro values he
    have hf := ControllerFL.finish_result_size repair fi (encCtx q r B m X,encCfg s)
    rw [ControllerFL.finish_den repair fi q r B m X s values he] at hf
    simp only [Prod.snd] at hf
    have hi := @Trans.Bounds.shape2 (TCtx ContextFL.TX) TCfg (encCtx q r B m X) (encCfg s)
    change ((TArg ContextFL.TX).enc (encCtx q r B m X,encCfg s)).size =
      ((TCtx ContextFL.TX).enc (encCtx q r B m X)).size+(TCfg.enc (encCfg s)).size+1 at hi
    have ho' : (Ty.enc (.list TR)
        (repair.den (ControllerFL.repairInput (encCtx q r B m X,encCfg s)))).size≤R := ho
    rw [Trans.Bounds.shape2]
    omega

variable {D t : ℕ} (hD : D=16^384) (hd : D=256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps T requestExtent)

/-- One envelope is fixed before all runtime inputs. Its second conclusion
charges the full final state for the stop test and output serialization. -/
theorem finish_step_budget : ∃ P : PolynomialEnvelope, ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds) (rationalRepetitionBudget (2*slots ds) c d)) → Bool)
      (s : Config),
    let m := rationalRepetitionBudget (2*slots ds) c d
    let B := rationalCellBudget a b
    let X := contextData hD hd A ds rows C (List.ofFn coins)
    let L := Boundary.resourceSize rows C a b c d
    Reachable (keySize n ds.sum) (slots ds-1) B m false
      (external hD hd A density spec rows C m coins) s → s.pc=.endpointZero →
    CallBounds (Program.tensorStep (source hD hd A density) Concrete.query Concrete.repair
      (data hD hd A).base (data hD hd A).den density (Trans.HashCallees.encConsts D A)
      (Install.thePg hD hd A) (Trans.Hash.gNbr actualMGG))
      (encCtx (keySize n ds.sum) (slots ds-1) B m X,encCfg s)
      (P.eval L) (P.eval L) (P.eval L) ∧
    ∀ values : List Ratio, Concrete.repair.den (X,s.goodTable,s.badTable)=values.map toR →
      (Ty.enc (TArg ContextFL.TX)
        (encCtx (keySize n ds.sum) (slots ds-1) B m X,
          encCfg {s with pc := .done,output := values})).size≤P.eval L := by
  obtain ⟨Pstate,hstate⟩ := argument_envelope hD hd A density spec
  obtain ⟨Prepair,hrepair⟩ := GeneralResources.callback_envelope hD hd A density spec
  obtain ⟨P,hP⟩ := (finish_polynomial Pstate Prepair).envelope
  refine ⟨P,?_⟩
  intro n ds rows C a b c d ha hc coins s
  dsimp only
  intro hs hpc
  let L := Boundary.resourceSize rows C a b c d
  let m := rationalRepetitionBudget (2*slots ds) c d
  let B := rationalCellBudget a b
  let X := contextData hD hd A ds rows C (List.ofFn coins)
  let src := source hD hd A density
  have hi := hstate (n:=n) (ds:=ds) rows C a b c d ha hc coins s hs
  obtain ⟨hr,ho⟩ := hrepair (n:=n) (ds:=ds) rows C a b c d ha hc coins s hs
  exact finish_package (controller hD hd A density) Concrete.repair
    (src.length+6) (src.length+7) (src.length+8) (keySize n ds.sum) (slots ds-1) B m X s
    (Pstate.eval L) (Prepair.eval L) (P.eval L) hpc hi hr ho (hP L)

end QecReliability.TensorMachineG.Runtime
