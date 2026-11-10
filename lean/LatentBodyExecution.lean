import LatentReachableStepBudget
import LatentResourceRunFacts
import LatentAuxiliaryExecution
import Assembly.Instance

/-! Concrete register-interpreter execution of every reachable latent controller
edge. The fixed program is unchanged. SAT cleanup cells are charged separately
from the actual edge's oracle time; all other register bounds are structural. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine.Runtime
open FL Trans.Wire Trans.Control RegMachine
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate

/-- Widen measured execution without changing its actual evaluation witness. -/
theorem computes_widen {P : FL.Program} {f : ℕ} {x y : Val} {m t d m' t' d' : ℕ}
    (h : Computes P f x y m t d) (hm : m ≤ m') (ht : t ≤ t') (hd : d ≤ d') :
    Computes P f x y m' t' d' := by
  obtain ⟨hx,time,depth,htime,hdepth,he⟩ := h
  exact ⟨hx.trans hm,time,depth,htime.trans ht,hdepth.trans hd,Eval.mono hm he⟩

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : MultiTape.Machine kE ΓE ΛE} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density PtE PsE T requestExtent)

/-- Actual body runs, including oracle invocation, with one input-independent
polynomial budget. This is a register run, not yet the finite-tape lowering. -/
theorem resource_body_execution : ∃ Bd : Assembly.Budget, ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → 0<c → 0<r →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n r)
      (Factory.width hD hd A n r) (rationalRepetitionBudget (2*(r+1)) c d)) → Bool),
    let m := rationalRepetitionBudget (2*(r+1)) c d
    let B := rationalCellBudget a b
    let L := InputEncoding.paperLength rows C a b c d
    let ext := resourceExternal hD hd A density spec rows C m coins
    let vals := fun s : Config => (TArg TX).enc
      (encCtx (keySize n r) r B m (contextData hD hd A rows C m coins),encCfg s)
    let P := program hD hd A density
    let cap := InputEncoding.queryExtentPolynomial (gateConstant hD hd A) density L
    let O := resourceSatOracle E density requestExtent cap
    (∀ s, Reachable (keySize n r) r B m false ext s →
      Fits (Assembly.regBound P assemblyIndices Bd L)
        (Assembly.headRegs (vals s) (decide (s.pc = .done)))) ∧
    (∀ s e, Reachable (keySize n r) r B m false ext s →
      WholeWrapperCandidate.step (keySize n r) r B m false ext s = some e →
      Assembly.ORuns O (Assembly.regBound P assemblyIndices Bd L) (Assembly.body P assemblyIndices)
        (Assembly.headRegs (vals s) false)
        (Assembly.headRegs (vals e.next) (decide (e.next.pc = .done)))
        ((Assembly.iterBound P assemblyIndices Bd L+PsE.eval cap)+e.oracleTime)) := by
  obtain ⟨Ps,hs⟩ := resource_state_size_bound hD hd A density spec
  obtain ⟨Pe,he⟩ := resource_step_computes hD hd A density spec
  have hps : Assembly.PolyBounded Ps.eval := by unfold PolynomialEnvelope.eval; poly_bounded
  have hpe : Assembly.PolyBounded Pe.eval := by unfold PolynomialEnvelope.eval; poly_bounded
  have hp : Assembly.PolyBounded (fun L => Pe.eval L+Ps.eval L+
      auxiliaryValue (Ps.eval L)+auxiliaryCost (Ps.eval L)+auxiliaryDepth (Ps.eval L)) := by
    unfold auxiliaryValue auxiliaryCost auxiliaryDepth
    poly_bounded
  obtain ⟨Q,hQ⟩ := hp.envelope
  let Bd : Assembly.Budget := ⟨Q,Q,Q⟩
  refine ⟨Bd,?_⟩
  intro n r rows C a b c d ha hc hr coins
  dsimp only
  let m := rationalRepetitionBudget (2*(r+1)) c d
  let B := rationalCellBudget a b
  let L := InputEncoding.paperLength rows C a b c d
  let X := contextData hD hd A rows C m coins
  let ext := resourceExternal hD hd A density spec rows C m coins
  let vals := fun s : Config => (TArg TX).enc (encCtx (keySize n r) r B m X,encCfg s)
  let PP := program hD hd A density
  let cap := InputEncoding.queryExtentPolynomial (gateConstant hD hd A) density L
  let O := resourceSatOracle E density requestExtent cap
  let Good := Reachable (keySize n r) r B m false ext
  have hdom := hQ L
  have hv : auxiliaryValue (Ps.eval L) ≤ Q.eval L := by omega
  have ht : auxiliaryCost (Ps.eval L) ≤ Q.eval L := by omega
  have hdpth : auxiliaryDepth (Ps.eval L) ≤ Q.eval L := by omega
  have heB : Pe.eval L ≤ Q.eval L := by omega
  have hsB : Ps.eval L ≤ Q.eval L := by omega
  have hsize : ∀ s, Good s → (vals s).size ≤ Ps.eval L := by
    intro s hreach
    exact hs rows C a b c d ha hc hr coins s hreach
  have hdone : ∀ s, Good s → Computes PP assemblyIndices.isDone (vals s)
      (Enc.bool (decide (s.pc = .done))) (Q.eval L) (Q.eval L) (Q.eval L) := by
    intro s hreach
    exact computes_widen
      (auxiliary_isDone_computes hD hd A density (keySize n r) r B m X s (Ps.eval L)
        (resource_reachable_ne_fault hD hd A density spec rows C B m coins hreach)
        (hsize s hreach)) hv ht hdpth
  have hS := Assembly.regBound_hS PP assemblyIndices Bd L
  have hm := Assembly.regBound_hm PP assemblyIndices Bd L
  constructor
  · intro s hreach
    exact Assembly.fits_start hm (hdone s hreach).1
  · intro s e hreach hedge
    have hnext : Good e.next := Assembly.reachable_next hreach hedge
    have hdone' := hdone e.next hnext
    have hinv := computes_widen
      (auxiliary_isInvoke_computes hD hd A density (keySize n r) r B m X s
        (Ps.eval L) (hsize s hreach)) hv ht hdpth
    by_cases hpc : s.pc = .invoke
    · rw [show decide (s.pc = .invoke) = true by simp [hpc]] at hinv
      have hquery := computes_widen
        (auxiliary_query_computes hD hd A density (keySize n r) r B m X s
          (Ps.eval L) (hsize s hreach)) hv ht hdpth
      have hresume := computes_widen
        (auxiliary_resume_computes hD hd A density (keySize n r) r B m X s
          (Ps.eval L) ext e hpc hedge (hsize s hreach) (hsize e.next hnext)) hv ht hdpth
      obtain ⟨hok,hanswer,hcost⟩ := resource_invoke_correct hD hd A density spec
        rows C hr B m a b c d coins hreach hpc
      change O.qok s.query at hok
      change O.oracle s.query = (ext.sat s.query).value at hanswer
      change O.ocost s.query ≤ (ext.sat s.query).time+PsE.eval cap at hcost
      rw [← hanswer] at hresume
      have hedgeTime := Assembly.invoke_edge_time hpc hedge
      change e.oracleTime = (ext.sat s.query).time at hedgeTime
      have hrun := Assembly.body_invoke_run (O := O) hS hm hinv hquery hok hresume hdone'
      apply hrun.mono
      change Assembly.bodyCost PP assemblyIndices (Assembly.regBound PP assemblyIndices Bd L)
        (Q.eval L) (Q.eval L) (Q.eval L)+O.ocost s.query ≤
        (Assembly.iterBound PP assemblyIndices Bd L+PsE.eval cap)+e.oracleTime
      change Assembly.iterBound PP assemblyIndices Bd L+O.ocost s.query ≤ _
      omega
    · rw [show decide (s.pc = .invoke) = false by simp [hpc]] at hinv
      have hstep := computes_widen
        (he rows C a b c d ha hc hr coins s e hreach hpc hedge) heB heB heB
      have hrun := Assembly.body_step_run (O := O) hS hm hinv hstep hdone'
      apply hrun.mono
      change Assembly.iterBound PP assemblyIndices Bd L ≤
        (Assembly.iterBound PP assemblyIndices Bd L+PsE.eval cap)+e.oracleTime
      omega

end QecReliability.LatentMachine.Runtime
