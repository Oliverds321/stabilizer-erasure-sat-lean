import TensorMachineArgumentEnvelope
import TensorMachineEndpointBudget
import TensorQueryInputBudget
import TensorMachineStepResources

/-! The actual inherited counting transitions within one uniform polynomial.
All query/endpoint costs and both state sizes are discharged from input bounds. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.TensorMachine.Runtime
open FL Trans.Control Trans.BoundsStep Trans.Query.Bound
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.MultiTape

private theorem counting_poly (Ps Pq Pe : PolynomialEnvelope) :
    Assembly.PolyBounded (fun L => ControllerFL.localStepBudget (Ps.eval L)
      (Pq.eval L+2*Pe.eval L)+Ps.eval L) := by
  unfold ControllerFL.localStepBudget
  poly_bounded

private theorem sum_callees {TX : Ty} (x : Ix TX) (q r B m : ℕ) (X : TX.den)
    (s : Config) (Q E : ℕ)
    (hq : x.compile.cost (X,encKey s.request) ≤ Q ∧
      x.compile.depth (X,encKey s.request) ≤ Q ∧ x.compile.msize (X,encKey s.request) ≤ Q)
    (he : ∀ side, x.endpoint.cost (X,side) ≤ E ∧
      x.endpoint.depth (X,side) ≤ E ∧ x.endpoint.msize (X,side) ≤ E) :
    CC x (encCtx q r B m X,encCfg s) ≤ Q+2*E ∧
    CD x (encCtx q r B m X,encCfg s) ≤ Q+2*E ∧
    CM x (encCtx q r B m X,encCfg s) ≤ Q+2*E := by
  obtain ⟨e0,d0,m0⟩ := he false
  obtain ⟨e1,d1,m1⟩ := he true
  rcases hq with ⟨qc,qd,qm⟩
  change x.compile.cost (X,encKey s.request)+x.endpoint.cost (X,false)+x.endpoint.cost (X,true) ≤ _ ∧
    x.compile.depth (X,encKey s.request)+x.endpoint.depth (X,false)+x.endpoint.depth (X,true) ≤ _ ∧
    x.compile.msize (X,encKey s.request)+x.endpoint.msize (X,false)+x.endpoint.msize (X,true) ≤ _
  omega

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps T requestExtent)

set_option maxHeartbeats 2000000 in
theorem counting_step_budget : ∃ P : PolynomialEnvelope, ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds) (rationalRepetitionBudget (2*slots ds) c d)) → Bool)
      (s : Config) (e : Edge),
    let m := rationalRepetitionBudget (2*slots ds) c d
    let B := rationalCellBudget a b
    let X := contextData hD hd A ds rows C (List.ofFn coins)
    let ext := external hD hd A density spec rows C m coins
    let L := Boundary.resourceSize rows C a b c d
    Reachable (keySize n ds.sum) (slots ds-1) B m false ext s →
    s.pc ≠ .invoke → s.pc ≠ .endpointZero →
    WholeWrapperCandidate.step (keySize n ds.sum) (slots ds-1) B m false ext s = some e →
    CallBounds (Program.tensorStep (source hD hd A density) Concrete.query Concrete.repair
      (data hD hd A).base (data hD hd A).den density (Trans.HashCallees.encConsts D A)
      (Install.thePg hD hd A) (Trans.Hash.gNbr actualMGG))
      (encCtx (keySize n ds.sum) (slots ds-1) B m X,encCfg s)
      (P.eval L) (P.eval L) (P.eval L) := by
  obtain ⟨Pstate,hstate⟩ := argument_envelope hD hd A density spec
  obtain ⟨Pquery,hquery⟩ := QueryResources.compiler_budget hD hd A density QueryInstalled.indices
    (source hD hd A density).length
  obtain ⟨Pend,hend⟩ := endpoint_budget hD hd A density
  obtain ⟨P,hP⟩ := (counting_poly Pstate Pquery Pend).envelope
  refine ⟨P,?_⟩
  intro n ds rows C a b c d ha hc coins s e
  dsimp only
  intro hs hn hb hedge
  let L := Boundary.resourceSize rows C a b c d
  let m := rationalRepetitionBudget (2*slots ds) c d
  let B := rationalCellBudget a b
  let X := contextData hD hd A ds rows C (List.ofFn coins)
  let cx := controller hD hd A density
  let src := source hD hd A density
  let arg := (encCtx (keySize n ds.sum) (slots ds-1) B m X,encCfg s)
  have hi := hstate (n:=n) (ds:=ds) rows C a b c d ha hc coins s hs
  have hnxt := hstate (n:=n) (ds:=ds) rows C a b c d ha hc coins e.next
    (Assembly.reachable_next hs hedge)
  have hv := (reachable_request_invariant hs).request
  obtain ⟨qc,qd,qm,_,_⟩ := hquery (n:=n) (ds:=ds) rows C a b c d ha hc coins s.request hv
  have hh := sum_callees cx (keySize n ds.sum) (slots ds-1) B m X s
    (Pquery.eval L) (Pend.eval L) ⟨qc,qd,qm⟩
    (hend (n:=n) (ds:=ds) rows C a b c d ha hc coins)
  have hpc : arg.2.1.1 ≠ 14 := by
    change pcCode s.pc ≠ 14
    cases h : s.pc <;> simp_all [pcCode]
  have hden := Program.counting_step_den src Concrete.query Concrete.repair
    (data hD hd A).base (data hD hd A).den density (Trans.HashCallees.encConsts D A)
    (Install.thePg hD hd A) (Trans.Hash.gNbr actualMGG)
    (keySize n ds.sum) (slots ds-1) B m X
    (external hD hd A density spec rows C m coins) s hn hb
    (extAgrees hD hd A density spec (n:=n) (ds:=ds) rows C m coins s hv) e hedge
  have hold := (ControllerFL.nonfinish_den cx Concrete.repair (src.length+6)
    (src.length+7) (src.length+8) arg hpc).symm.trans hden
  have hout : ((TArg ContextFL.TX).enc
      ((LatentMachine.EndpointControllerFL.stepF cx).den arg)).size ≤ Pstate.eval L := by
    rw [hold]
    exact hnxt
  have hd : s.pc ≠ .done := Assembly.pc_ne_done_of_step hedge
  have hf : s.pc ≠ .fault := by intro hf; simp only [WholeWrapperCandidate.step,hf] at hedge; contradiction
  obtain ⟨ht,hdep,hm⟩ := ControllerFL.counting_resources cx Concrete.repair
    (src.length+6) (src.length+7) (src.length+8)
    (encCtx (keySize n ds.sum) (slots ds-1) B m X) s (Pstate.eval L)
    (Pquery.eval L+2*Pend.eval L) hn hd hf hb hi hout hh.1 hh.2.1 hh.2.2
  have hbnd := hP L
  have hdom : ControllerFL.localStepBudget (Pstate.eval L)
      (Pquery.eval L+2*Pend.eval L) ≤ P.eval L := by omega
  have hadom : Pstate.eval L ≤ P.eval L := by omega
  exact ⟨hm.trans hdom,hi.trans hadom,ht.trans hdom,hdep.trans hdom⟩

end QecReliability.TensorMachine.Runtime
