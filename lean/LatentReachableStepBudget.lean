import LatentReachableStateSize
import LatentEndpointStepBounds
import LatentEndpointInputBudget
import Assembly.Loop

/-! Measured actual callback/step budgets and literal FL step execution at every
reachable non-oracle edge. Numerical B is absent from the workspace envelope.
Oracle edges remain separate, with their real machine time and cells. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine.Runtime
open FL Trans.Wire Trans.Control Trans.Query.Bound Trans.BoundsQH
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)

/-- Actual signature resources, rather than merely macro counters or an
existential short evaluation of a possibly larger signature. -/
theorem callback_budget : ∃ P : PolynomialEnvelope, ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n r)
      (Factory.width hD hd A n r) (rationalRepetitionBudget (2*(r+1)) c d)) → Bool),
    let m := rationalRepetitionBudget (2*(r+1)) c d
    let L := InputEncoding.paperLength rows C a b c d
    let X := contextData hD hd A rows C m coins
    (∀ key : RequestKey, ValidKey (keySize n r) r m key →
      (controller hD hd A density).compile.cost (X,encKey key) ≤ P.eval L ∧
      (controller hD hd A density).compile.depth (X,encKey key) ≤ P.eval L ∧
      (controller hD hd A density).compile.msize (X,encKey key) ≤ P.eval L) ∧
    (∀ side : Bool,
      (controller hD hd A density).endpoint.cost (X,side) ≤ P.eval L ∧
      (controller hD hd A density).endpoint.depth (X,side) ≤ P.eval L ∧
      (controller hD hd A density).endpoint.msize (X,side) ≤ P.eval L) := by
  obtain ⟨Pm,hm⟩ := argument_bound hD hd A
  obtain ⟨Kc,Cc,hcomp⟩ := compile_bound hD hd A density
  obtain ⟨Ke,Ce,hend⟩ := EndpointBounds.endpoint_bound Install.wL WrappersInstalled.indices Install.yR
  have hpm : Assembly.PolyBounded Pm.eval := by unfold PolynomialEnvelope.eval; poly_bounded
  have hg1 := Trans.BoundsRest.G_comp_pb Kc Cc hpm
  have hg2 := Trans.BoundsRest.G_comp_pb Ke Ce hpm
  have hsum : Assembly.PolyBounded (fun L => G Kc Cc (Pm.eval L)+G Ke Ce (Pm.eval L)) := by
    poly_bounded
  obtain ⟨P,hP⟩ := hsum.envelope
  refine ⟨P,?_⟩
  intro n r rows C a b c d ha hc coins
  let L := InputEncoding.paperLength rows C a b c d
  let m := rationalRepetitionBudget (2*(r+1)) c d
  let X := contextData hD hd A rows C m coins
  have hdom := hP L
  have hcdom : G Kc Cc (Pm.eval L) ≤ P.eval L := by omega
  have hedom : G Ke Ce (Pm.eval L) ≤ P.eval L := by omega
  constructor
  · intro key hk
    obtain ⟨h1,h2,h3,_,_⟩ := hcomp (Pm.eval L) (X,encKey key)
      (hm rows C a b c d ha hc coins key hk)
    exact ⟨h1.trans hcdom, h2.trans hcdom, h3.trans hcdom⟩
  · intro side
    have hbase := hm rows C a b c d ha hc coins (.base false 0 0) (by constructor <;> omega)
    have harg : mag (.prod TX .bool) (X,side) ≤ Pm.eval L := by
      change mag TX X+8+1 ≤ Pm.eval L at hbase
      change mag TX X+1+1 ≤ Pm.eval L
      omega
    obtain ⟨h1,h2,h3⟩ := hend (X,side)
    have hg := G_mono (k:=Ke) (c:=Ce) le_rfl le_rfl harg
    have t1 := h1.trans hg
    have t2 := h2.trans hg
    have t3 := h3.trans hg
    change (controller hD hd A density).endpoint.cost (X,side) ≤ _ at t1
    change (controller hD hd A density).endpoint.depth (X,side) ≤ _ at t2
    change (controller hD hd A density).endpoint.msize (X,side) ≤ _ at t3
    exact ⟨t1.trans hedom, t2.trans hedom, t3.trans hedom⟩

variable {kE : ℕ} {ΓE ΛE : Type*} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : MultiTape.Machine kE ΓE ΛE} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}
  {resource : SATRequest → ℕ} (spec : ResourceEncodedSAT E density PtE PsE T resource)

/-- Every reachable non-invocation edge runs the concrete false-mode FL step,
with fixed structural-input bounds on value cells, time and call depth. -/
theorem resource_step_computes : ∃ P : PolynomialEnvelope, ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → 0<c → 0<r →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n r)
      (Factory.width hD hd A n r) (rationalRepetitionBudget (2*(r+1)) c d)) → Bool)
      (s : Config) (e : Edge),
    let m := rationalRepetitionBudget (2*(r+1)) c d
    let B := rationalCellBudget a b
    let L := InputEncoding.paperLength rows C a b c d
    let X := contextData hD hd A rows C m coins
    let ext := resourceExternal hD hd A density spec rows C m coins
    Reachable (keySize n r) r B m false ext s → s.pc ≠ .invoke →
    WholeWrapperCandidate.step (keySize n r) r B m false ext s = some e →
    Computes (program hD hd A density) (EndpointControllerFL.stepF (controller hD hd A density)).idx
      ((TArg TX).enc (encCtx (keySize n r) r B m X,encCfg s))
      ((TArg TX).enc (encCtx (keySize n r) r B m X,encCfg e.next))
      (P.eval L) (P.eval L) (P.eval L) := by
  obtain ⟨Ps,hs⟩ := resource_state_size_bound hD hd A density spec
  obtain ⟨Pc,hc⟩ := callback_budget hD hd A density
  have hps : Assembly.PolyBounded Ps.eval := by unfold PolynomialEnvelope.eval; poly_bounded
  have hpc : Assembly.PolyBounded Pc.eval := by unfold PolynomialEnvelope.eval; poly_bounded
  have hsum : Assembly.PolyBounded
      (fun L => 6000000*(Ps.eval L+1)^2+30000*(Ps.eval L+1)+3*Pc.eval L) := by poly_bounded
  obtain ⟨P,hP⟩ := hsum.envelope
  refine ⟨P,?_⟩
  intro n r rows C a b c d ha hcpos hr coins s e
  dsimp only
  intro hreach hn hedge
  let m := rationalRepetitionBudget (2*(r+1)) c d
  let B := rationalCellBudget a b
  let L := InputEncoding.paperLength rows C a b c d
  let X := contextData hD hd A rows C m coins
  let ctx := encCtx (keySize n r) r B m X
  let arg : (TArg TX).den := (ctx,encCfg s)
  have harg := hs rows C a b c d ha hcpos hr coins s hreach
  have hnext := hs rows C a b c d ha hcpos hr coins e.next (Assembly.reachable_next hreach hedge)
  have hden := resource_reachable_step hD hd A density spec rows C B m coins hreach hn e hedge
  have hdone : s.pc ≠ .done := Assembly.pc_ne_done_of_step hedge
  have hf : s.pc ≠ .fault := by intro hf; simp only [WholeWrapperCandidate.step,hf] at hedge; contradiction
  obtain ⟨st,sd,sm⟩ := EndpointControllerBounds.step_bounds (controller hD hd A density) ctx s hn hdone hf
  obtain ⟨hcompile,hend⟩ := hc rows C a b c d ha hcpos coins
  obtain ⟨c1,c2,c3⟩ := hcompile s.request (reachable_request_invariant hreach).request
  obtain ⟨e1,e2,e3⟩ := hend false
  obtain ⟨f1,f2,f3⟩ := hend true
  have cc : Trans.BoundsStep.CC (controller hD hd A density) arg ≤ 3*Pc.eval L := by
    change (controller hD hd A density).compile.cost (X,encKey s.request)+
      (controller hD hd A density).endpoint.cost (X,false)+
      (controller hD hd A density).endpoint.cost (X,true) ≤ _
    dsimp only [X,L,m] at *
    omega
  have cd : Trans.BoundsStep.CD (controller hD hd A density) arg ≤ 3*Pc.eval L := by
    change (controller hD hd A density).compile.depth (X,encKey s.request)+
      (controller hD hd A density).endpoint.depth (X,false)+
      (controller hD hd A density).endpoint.depth (X,true) ≤ _
    dsimp only [X,L,m] at *
    omega
  have cm : Trans.BoundsStep.CM (controller hD hd A density) arg ≤ 3*Pc.eval L := by
    change (controller hD hd A density).compile.msize (X,encKey s.request)+
      (controller hD hd A density).endpoint.msize (X,false)+
      (controller hD hd A density).endpoint.msize (X,true) ≤ _
    dsimp only [X,L,m] at *
    omega
  change (EndpointControllerFL.stepF (controller hD hd A density)).cost arg ≤
    5000000*(((TArg TX).enc arg).size+1)^2+Trans.BoundsStep.CC (controller hD hd A density) arg at st
  change (EndpointControllerFL.stepF (controller hD hd A density)).depth arg ≤
    2000*(((TArg TX).enc arg).size+1)+Trans.BoundsStep.CD (controller hD hd A density) arg at sd
  change (EndpointControllerFL.stepF (controller hD hd A density)).msize arg ≤
    2*((TArg TX).enc ((EndpointControllerFL.stepF (controller hD hd A density)).den arg)).size+
      20000*(((TArg TX).enc arg).size+1)+Trans.BoundsStep.CM (controller hD hd A density) arg at sm
  change (EndpointControllerFL.stepF (controller hD hd A density)).den arg = (ctx,encCfg e.next) at hden
  change ((TArg TX).enc arg).size ≤ Ps.eval L at harg
  have hsq : (((TArg TX).enc arg).size+1)^2 ≤ (Ps.eval L+1)^2 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right harg 1) 2
  have hlin : Ps.eval L+1 ≤ (Ps.eval L+1)^2 := Nat.le_self_pow (by norm_num) _
  rw [hden] at sm
  have hdom := hP L
  have ht : (EndpointControllerFL.stepF (controller hD hd A density)).cost arg ≤ P.eval L := by omega
  have hdp : (EndpointControllerFL.stepF (controller hD hd A density)).depth arg ≤ P.eval L := by omega
  have hm : (EndpointControllerFL.stepF (controller hD hd A density)).msize arg ≤ P.eval L := by
    change ((TArg TX).enc (ctx,encCfg e.next)).size ≤ Ps.eval L at hnext
    omega
  have hin : ((TArg TX).enc arg).size ≤ P.eval L := by omega
  obtain ⟨hi,time,depth,htime,hdepth,heval⟩ :=
    (step_valid hD hd A density arg).computes hm hin
  rw [hden] at heval
  exact ⟨hi,time,depth,htime.trans ht,hdepth.trans hdp,heval⟩

end QecReliability.LatentMachine.Runtime
