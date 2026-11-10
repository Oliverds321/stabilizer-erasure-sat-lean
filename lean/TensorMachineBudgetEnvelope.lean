import TensorMachineCountingStepBudget
import TensorMachineFinishStepBudget
import TensorMachineInitializerEnvelope
import TensorMachineRuntimeLoop
import Assembly.Instance

/-! One fixed polynomial budget for every actual tensor-machine callback.
The register capacity is selected generically before concrete factory data is
substituted, so its proof never normalizes a large fixed certificate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace QecReliability.TensorMachine
open FL OracleCost

theorem CallBounds.weaken {a b : Ty} {F : FnSig a b} {x : a.den}
    {M T D M' T' D' : ℕ} (h : CallBounds F x M T D)
    (hm : M≤M') (ht : T≤T') (hd : D≤D') : CallBounds F x M' T' D' :=
  ⟨h.space.trans hm,h.argument.trans hm,h.time.trans ht,h.depth.trans hd⟩

private theorem six_envelopes (A B C D E F : PolynomialEnvelope) :
    ∃ P : PolynomialEnvelope, ∀ L, A.eval L≤P.eval L ∧ B.eval L≤P.eval L ∧
      C.eval L≤P.eval L ∧ D.eval L≤P.eval L ∧ E.eval L≤P.eval L ∧ F.eval L≤P.eval L := by
  have hpoly : Assembly.PolyBounded (fun L => A.eval L+B.eval L+C.eval L+D.eval L+E.eval L+F.eval L) := by
    poly_bounded
  obtain ⟨P,hP⟩ := hpoly.envelope
  exact ⟨P,fun L => by have := hP L; omega⟩

/-- Generic interpreter capacity, retaining program size as a fixed constant. -/
theorem capacity_envelope (code : FL.Program) (ix : Assembly.Indices) (P : PolynomialEnvelope) :
    ∃ S : PolynomialEnvelope, ∀ L,
      Assembly.stBound code ix (P.eval L) (P.eval L)+(FL.Program.enc code).size+2≤S.eval L ∧
      2*P.eval L+4≤S.eval L := by
  let Bd : Assembly.Budget := ⟨P,P,P⟩
  obtain ⟨S,hS⟩ := (Assembly.regBound_poly code ix Bd).envelope
  refine ⟨S,fun L => ?_⟩
  exact ⟨(Assembly.regBound_hS code ix Bd L).trans (hS L),
    (Assembly.regBound_hm code ix Bd L).trans (hS L)⟩

end QecReliability.TensorMachine

noncomputable section
namespace QecReliability.TensorMachine.Runtime
open FL Trans.Control Trans.Wire Assembly RationalOutput
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.MultiTape

variable {D t : ℕ} (hD : D=16^384) (hd : D=256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {Pt Ps : PolynomialEnvelope} {timeE : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps timeE requestExtent)
  {n : ℕ} {ds : List ℕ} (rows : List (List (PauliCoord n)))
  (C : SharedCircuit.Program ds.sum n) (a b c d m : ℕ)


variable (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
  (Factory.width hD hd A n ds) (m)) → Bool)


/-- All numerical premises of the actual completion theorem, with one shared
callee budget and one register-capacity envelope. -/
structure InstanceBudget (P S : PolynomialEnvelope) : Prop where
  loop : LoopBounds hD hd A density spec (n:=n) (ds:=ds) rows C (rationalCellBudget a b) (m) coins
    (P.eval (Boundary.resourceSize rows C a b c d)) (P.eval (Boundary.resourceSize rows C a b c d)) (P.eval (Boundary.resourceSize rows C a b c d))
  initial : CallBounds (Program.initializer (source hD hd A density) (data hD hd A).base (data hD hd A).den)
    (input ds rows C a b c d (List.ofFn coins)) (P.eval (Boundary.resourceSize rows C a b c d)) (P.eval (Boundary.resourceSize rows C a b c d)) (P.eval (Boundary.resourceSize rows C a b c d))
  finished : ∀ s, (Reachable (keySize n ds.sum) (slots ds-1) (rationalCellBudget a b) (m) false (external hD hd A density spec (n:=n) (ds:=ds) rows C (m) coins)) s → s.pc=.endpointZero → ∀ values : List Ratio,
    Concrete.repair.den ((contextData hD hd A ds rows C (List.ofFn coins)),s.goodTable,s.badTable)=values.map toR →
    CallBounds (isDoneF (controller hD hd A density)) ((fun s : Config => (encCtx (keySize n ds.sum) (slots ds-1) (rationalCellBudget a b) (m) (contextData hD hd A ds rows C (List.ofFn coins)),encCfg s)) {s with pc:=.done,output:=values})
      (P.eval (Boundary.resourceSize rows C a b c d)) (P.eval (Boundary.resourceSize rows C a b c d)) (P.eval (Boundary.resourceSize rows C a b c d)) ∧
    CallBounds (Trans.Bounds.outputF Install.oX ContextFL.TX) ((fun s : Config => (encCtx (keySize n ds.sum) (slots ds-1) (rationalCellBudget a b) (m) (contextData hD hd A ds rows C (List.ofFn coins)),encCfg s)) {s with pc:=.done,output:=values})
      (P.eval (Boundary.resourceSize rows C a b c d)) (P.eval (Boundary.resourceSize rows C a b c d)) (P.eval (Boundary.resourceSize rows C a b c d))
  capacity : stBound (program hD hd A density) (indices hD hd A density) (P.eval (Boundary.resourceSize rows C a b c d)) (P.eval (Boundary.resourceSize rows C a b c d))+(FL.Program.enc (program hD hd A density)).size+2≤S.eval (Boundary.resourceSize rows C a b c d)
  values_fit : 2*P.eval (Boundary.resourceSize rows C a b c d)+4≤S.eval (Boundary.resourceSize rows C a b c d)

set_option maxHeartbeats 2000000 in
theorem budget_envelope : ∃ P S : PolynomialEnvelope, ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (m : ℕ), m = rationalRepetitionBudget (2*slots ds) c d →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds) m) → Bool),
    InstanceBudget hD hd A density spec (n:=n) (ds:=ds) rows C a b c d m coins P S := by
  obtain ⟨Parg,harg⟩ := argument_envelope hD hd A density spec
  obtain ⟨Pcount,hcount⟩ := counting_step_budget hD hd A density spec
  obtain ⟨Pfinish,hfinish⟩ := finish_step_budget hD hd A density spec
  obtain ⟨Pinit,hinit⟩ := initializer_call_bounds hD hd A
  obtain ⟨Paux,haux⟩ := Auxiliary.envelopes Parg
  obtain ⟨Pfinal,hfinal⟩ := Auxiliary.envelopes Pfinish
  obtain ⟨P,hP⟩ := six_envelopes Parg Pcount Pfinish Pinit Paux Pfinal
  obtain ⟨S,hS⟩ := capacity_envelope (program hD hd A density) (indices hD hd A density) P
  refine ⟨P,S,?_⟩
  intro n ds rows C a b c d ha hc m hrep coins
  subst m
  let L := Boundary.resourceSize rows C a b c d
  let m := rationalRepetitionBudget (2*slots ds) c d
  let B := rationalCellBudget a b
  let X := contextData hD hd A ds rows C (List.ofFn coins)
  let cx := controller hD hd A density
  let ctx := encCtx (keySize n ds.sum) (slots ds-1) B m X
  obtain ⟨da,dc,df,di,dx,dy⟩ := hP L
  have hobs : ∀ s, Reachable (keySize n ds.sum) (slots ds-1) B m false
      (external hD hd A density spec (n:=n) (ds:=ds) rows C m coins) s →
      CallBounds (isInvokeF cx) (ctx,encCfg s) (Paux.eval L) (Paux.eval L) (Paux.eval L) ∧
      CallBounds (isDoneF cx) (ctx,encCfg s) (Paux.eval L) (Paux.eval L) (Paux.eval L) ∧
      CallBounds (queryOfF cx) (ctx,encCfg s) (Paux.eval L) (Paux.eval L) (Paux.eval L) ∧
      (∀ answer, CallBounds (Trans.Bounds.resumeTopF Install.oX cx) (answer,(ctx,encCfg s))
        (Paux.eval L) (Paux.eval L) (Paux.eval L)) ∧
      CallBounds (Trans.Bounds.outputF Install.oX ContextFL.TX) (ctx,encCfg s)
        (Paux.eval L) (Paux.eval L) (Paux.eval L) := by
    intro s hs
    exact haux cx Install.oX ctx s L (harg (n:=n) (ds:=ds) rows C a b c d ha hc coins s hs)
  refine ⟨?_,?_,?_,(hS L).1,(hS L).2⟩
  · refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · intro s hs
      exact (harg (n:=n) (ds:=ds) rows C a b c d ha hc coins s hs).trans da
    · intro s hs
      exact (hobs s hs).1.weaken dx dx dx
    · intro s hs
      exact (hobs s hs).2.1.weaken dx dx dx
    · intro s hs
      exact (hobs s hs).2.2.1.weaken dx dx dx
    · intro s e hs hn hb hedge
      exact (hcount (n:=n) (ds:=ds) rows C a b c d ha hc coins s e hs hn hb hedge).weaken dc dc dc
    · intro s hs hb
      exact (hfinish (n:=n) (ds:=ds) rows C a b c d ha hc coins s hs hb).1.weaken df df df
    · intro s hs answer
      exact ((hobs s hs).2.2.2.1 answer).weaken dx dx dx
  · exact (hinit (source hD hd A density) (n:=n) (ds:=ds) rows C a b c d ha hc coins).weaken di di di
  · intro s hs hb values he
    have hz := (hfinish (n:=n) (ds:=ds) rows C a b c d ha hc coins s hs hb).2 values he
    have hf := hfinal cx Install.oX ctx {s with pc:=.done,output:=values} L hz
    exact ⟨hf.2.1.weaken dy dy dy,hf.2.2.2.2.weaken dy dy dy⟩

end QecReliability.TensorMachine.Runtime
end
