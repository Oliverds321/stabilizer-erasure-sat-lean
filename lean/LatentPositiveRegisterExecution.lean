import LatentBodyExecution
import LatentRegisterSpace
import LatentInitializerComputes

/-! Actual whole register execution on the SAT-bearing latent branch. All
preamble, loop and output runs are discharged for the one installed program.
The oracle is still abstract here; finite-tape realization is the next layer. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine.Runtime
open FL Trans.Wire Trans.Control RegMachine
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.StoredCodeHashConfidence

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : MultiTape.Machine kE ΓE ΛE} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density PtE PsE T requestExtent)

/-- Two structural-input polynomials bound registers and non-SAT work per
macro dispatch. Actual SAT time is retained exactly; cleanup cells are in Pt. -/
theorem positive_register_execution : ∃ Pspace Ptime : PolynomialEnvelope, ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → 0<c → 0<r →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n r)
      (Factory.width hD hd A n r) (rationalRepetitionBudget (2*(r+1)) c d)) → Bool),
    let m := rationalRepetitionBudget (2*(r+1)) c d
    let B := rationalCellBudget a b
    let L := InputEncoding.paperLength rows C a b c d
    let seeds := decodeCoins (Factory.length hD hd A n r) (Factory.width hD hd A n r) m coins
    let cache := SharedCircuit.ConcreteQuantum.prepare rows C (actualCodeHash (Factory.system hD hd A n r))
      (Factory.circuits hD hd A n r) spec.service.solver B m seeds
    let ext := resourceExternal hD hd A density spec rows C m coins
    let cap := InputEncoding.queryExtentPolynomial (gateConstant hD hd A) density L
    ∃ final totals events, ∃ out : Regs 20,
      Trace (keySize n r) r B m false ext (initial (keySize n r) r m) totals events final ∧
      HasOutput final cache.good.entries cache.bad.entries
        (RationalOutput.LinearRepair.fromCache false rows C cache) ∧
      totals.calls = cache.calls ∧
      totals.oracleTime = (QuantumService.prepareMeasured rows C
        (actualCodeHash (Factory.system hD hd A n r)) (Factory.circuits hD hd A n r)
        spec.service B m seeds).oracleTime ∧
      totals.calls ≤ totalCallCap (keySize n r) r B m ∧
      totals.dispatches ≤ macroDispatchBound (keySize n r) r B m ∧
      Assembly.ORuns (resourceSatOracle E density requestExtent cap) (Pspace.eval L)
        (Assembly.mainProg (program hD hd A density) assemblyIndices).body
        (inputRegs (R := 19) (input rows C a b c d (List.ofFn coins))) out
        (Ptime.eval L*(totals.dispatches+1)+totals.oracleTime) ∧
      out Assembly.rOUT = Assembly.ratioWord final.output := by
  obtain ⟨Bb,hbody⟩ := resource_body_execution hD hd A density spec
  obtain ⟨Pi,hi⟩ := initializer_computes hD hd A density
  obtain ⟨Ps,hs⟩ := resource_state_size_bound hD hd A density spec
  let PP := program hD hd A density
  have hpi : Assembly.PolyBounded Pi.eval := by unfold PolynomialEnvelope.eval; poly_bounded
  have hps : Assembly.PolyBounded Ps.eval := by unfold PolynomialEnvelope.eval; poly_bounded
  have haux : Assembly.PolyBounded (fun L => Pi.eval L+Ps.eval L+
      auxiliaryValue (Ps.eval L)+auxiliaryCost (Ps.eval L)+auxiliaryDepth (Ps.eval L)) := by
    unfold auxiliaryValue auxiliaryCost auxiliaryDepth
    poly_bounded
  obtain ⟨Q,hQ⟩ := haux.envelope
  let Ba : Assembly.Budget := ⟨Q,Q,Q⟩
  have hsb := Assembly.regBound_poly PP assemblyIndices Bb
  have hsa := Assembly.regBound_poly PP assemblyIndices Ba
  have hss : Assembly.PolyBounded (fun L => Assembly.regBound PP assemblyIndices Bb L+
      Assembly.regBound PP assemblyIndices Ba L) := by poly_bounded
  obtain ⟨S,hSbound⟩ := hss.envelope
  have hsPoly : Assembly.PolyBounded S.eval := by unfold PolynomialEnvelope.eval; poly_bounded
  have hqPoly : Assembly.PolyBounded Q.eval := by unfold PolynomialEnvelope.eval; poly_bounded
  have hit := Assembly.iterBound_poly PP assemblyIndices Bb
  have hcPoly : Assembly.PolyBounded (fun L => PsE.eval
      (InputEncoding.queryExtentPolynomial (gateConstant hD hd A) density L)) := by
    unfold PolynomialEnvelope.eval InputEncoding.queryExtentPolynomial InputEncoding.queryPolynomial
    poly_bounded
  have hpPoly : Assembly.PolyBounded (fun L =>
      Assembly.preCost PP assemblyIndices (S.eval L) (Q.eval L) (Q.eval L) (Q.eval L)+
      Assembly.iterBound PP assemblyIndices Bb L+
      PsE.eval (InputEncoding.queryExtentPolynomial (gateConstant hD hd A) density L)+1+
      Assembly.postCost PP assemblyIndices (S.eval L) (Q.eval L) (Q.eval L) (Q.eval L)) := by
    unfold Assembly.preCost Assembly.postCost Assembly.flCost Assembly.stBound
      FL.stateBound FL.frameBound
    poly_bounded
  obtain ⟨Pt,hPt⟩ := hpPoly.envelope
  refine ⟨S,Pt,?_⟩
  intro n r rows C a b c d ha hc hr coins
  dsimp only
  let m := rationalRepetitionBudget (2*(r+1)) c d
  let B := rationalCellBudget a b
  let L := InputEncoding.paperLength rows C a b c d
  let X := contextData hD hd A rows C m coins
  let ext := resourceExternal hD hd A density spec rows C m coins
  let vals := fun s : Config => (TArg TX).enc (encCtx (keySize n r) r B m X,encCfg s)
  let Good := Reachable (keySize n r) r B m false ext
  let cap := InputEncoding.queryExtentPolynomial (gateConstant hD hd A) density L
  let O := resourceSatOracle E density requestExtent cap
  have hsum := hQ L
  have hPi : Pi.eval L ≤ Q.eval L := by omega
  have hv : auxiliaryValue (Ps.eval L) ≤ Q.eval L := by omega
  have ht : auxiliaryCost (Ps.eval L) ≤ Q.eval L := by omega
  have hdpth : auxiliaryDepth (Ps.eval L) ≤ Q.eval L := by omega
  have hspace := hSbound L
  have hSb : Assembly.regBound PP assemblyIndices Bb L ≤ S.eval L := by omega
  have hSa : Assembly.regBound PP assemblyIndices Ba L ≤ S.eval L := by omega
  have hS := (Assembly.regBound_hS PP assemblyIndices Ba L).trans hSa
  have hm := (Assembly.regBound_hm PP assemblyIndices Ba L).trans hSa
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
  have hinit := computes_widen (hi rows C a b c d ha hc coins) hPi hPi hPi
  simp only [initializedValue,initialConfiguration,if_neg (Nat.ne_of_gt hr)] at hinit
  change Computes PP assemblyIndices.init (Assembly.bitsVal (input rows C a b c d (List.ofFn coins)))
    (vals (initial (keySize n r) r m)) (Q.eval L) (Q.eval L) (Q.eval L) at hinit
  have hpre := Assembly.preamble_run (O := O) hS hm hinit
    (hdone _ Assembly.reachable_initial)
  obtain ⟨hf,hb⟩ := hbody rows C a b c d ha hc hr coins
  have hbody' : ∀ s e, Good s → WholeWrapperCandidate.step (keySize n r) r B m false ext s = some e →
      Assembly.ORuns O (S.eval L) (Assembly.body PP assemblyIndices)
        (Assembly.headRegs (vals s) false)
        (Assembly.headRegs (vals e.next) (decide (e.next.pc = .done)))
        ((Assembly.iterBound PP assemblyIndices Bb L+PsE.eval cap)+e.oracleTime) := by
    intro s e hreach hedge
    exact oruns_space_mono (hb s e hreach hedge) hSb
  obtain ⟨final,totals,events,htrace,hout,_,hcalls,htime,hcap,hdispatch⟩ :=
    resource_macro_output hD hd A density spec rows C B m coins
  have hloop := Assembly.loop_trace (P := PP) (I := assemblyIndices) vals Good
    (fun s e hs he => Assembly.reachable_next hs he)
    (fun s hs => Assembly.fits_start hm (hdone s hs).1)
    hbody' htrace Assembly.reachable_initial hout.1
  have houtRun := computes_widen
    (auxiliary_output_computes hD hd A density (keySize n r) r B m X final (Ps.eval L)
      (hsize final ⟨_,_,htrace⟩)) hv ht hdpth
  have hpost := Assembly.postamble_run (O := O) hS houtRun hloop.fits_end
  refine ⟨final,totals,events,
    Assembly.regsOf (vals final).bits [] (Assembly.dnBits true) [] (Assembly.ratioWord final.output),
    htrace,hout,hcalls,htime,hcap,hdispatch,?_,rfl⟩
  apply (hpre.seq (hloop.seq hpost)).mono
  have htimeBound := hPt L
  change Assembly.preCost PP assemblyIndices (S.eval L) (Q.eval L) (Q.eval L) (Q.eval L)+
      ((totals.dispatches+1)*(Assembly.iterBound PP assemblyIndices Bb L+PsE.eval cap+1)+
        totals.oracleTime+Assembly.postCost PP assemblyIndices (S.eval L) (Q.eval L) (Q.eval L) (Q.eval L)) ≤
      Pt.eval L*(totals.dispatches+1)+totals.oracleTime
  change Assembly.preCost PP assemblyIndices (S.eval L) (Q.eval L) (Q.eval L) (Q.eval L)+
      Assembly.iterBound PP assemblyIndices Bb L+PsE.eval cap+1+
      Assembly.postCost PP assemblyIndices (S.eval L) (Q.eval L) (Q.eval L) (Q.eval L) ≤ Pt.eval L at htimeBound
  have hmul := Nat.mul_le_mul_left (totals.dispatches+1) htimeBound
  nlinarith only [hmul,
    Nat.zero_le (totals.dispatches*Assembly.preCost PP assemblyIndices (S.eval L) (Q.eval L) (Q.eval L) (Q.eval L)),
    Nat.zero_le (totals.dispatches*Assembly.postCost PP assemblyIndices (S.eval L) (Q.eval L) (Q.eval L) (Q.eval L))]

end QecReliability.LatentMachine.Runtime
