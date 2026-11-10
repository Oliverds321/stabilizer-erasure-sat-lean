import LatentPositiveRegisterExecution
import ResourceAssemblyAdapter

/-! Finite-tape lowering of the actual positive-latent register execution.
Completed.cells counts every visited tape cell, including input, coins, interpreter
and SAT/reset tapes. The same machine is fixed before all runtime data. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine.Runtime
open FL Trans.Wire Trans.Control RegMachine
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.StoredCodeHashConfidence

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : MultiTape.Machine kE ΓE ΛE} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density PtE PsE T requestExtent)

/-- Exact endpoint-mode output with all-tape space and time. The measured SAT
time term remains literal here; its engine-variable bound is a separate result. -/
theorem positive_machine_execution : ∃ Pspace Ptime : PolynomialEnvelope, ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → 0<c → 0<r →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n r)
      (Factory.width hD hd A n r) (rationalRepetitionBudget (2*(r+1)) c d)) → Bool),
    let m := rationalRepetitionBudget (2*(r+1)) c d
    let B := rationalCellBudget a b
    let L := InputEncoding.paperLength rows C a b c d
    let H := actualCodeHash (Factory.system hD hd A n r)
    let K := Factory.circuits hD hd A n r
    let seeds := decodeCoins (Factory.length hD hd A n r) (Factory.width hD hd A n r) m coins
    let M := Assembly.theMachine E (program hD hd A density) assemblyIndices
    ∃ run : MultiTape.Completed M (input rows C a b c d (List.ofFn coins)),
      Final.Outputs M run (Assembly.outTape kE)
        (semanticOutput rows C H K spec.service.solver a b c d seeds) ∧
      run.time ≤ Ptime.eval L*(macroDispatchBound (keySize n r) r B m+1)+
        (3*kE+6)*(QuantumService.prepareMeasured rows C H K spec.service B m seeds).oracleTime ∧
      run.cells ≤ Pspace.eval L := by
  obtain ⟨S,P,hP⟩ := positive_register_execution hD hd A density spec
  have hS : Assembly.PolyBounded S.eval := by unfold PolynomialEnvelope.eval; poly_bounded
  have hPpoly : Assembly.PolyBounded P.eval := by unfold PolynomialEnvelope.eval; poly_bounded
  have hcap : Assembly.PolyBounded (fun L => PsE.eval
      (InputEncoding.queryExtentPolynomial (gateConstant hD hd A) density L)) := by
    unfold PolynomialEnvelope.eval InputEncoding.queryExtentPolynomial InputEncoding.queryPolynomial
    poly_bounded
  have hspace : Assembly.PolyBounded (fun L => (19+kE+1+1)*
      (2*(S.eval L+PsE.eval (InputEncoding.queryExtentPolynomial (gateConstant hD hd A) density L))+3)) := by
    poly_bounded
  have htime : Assembly.PolyBounded (fun L => (3*kE+6)*(P.eval L+1)) := by poly_bounded
  obtain ⟨Ss,hSs⟩ := hspace.envelope
  obtain ⟨Pt,hPt⟩ := htime.envelope
  refine ⟨Ss,Pt,?_⟩
  intro n r rows C a b c d ha hc hr coins
  dsimp only
  let m := rationalRepetitionBudget (2*(r+1)) c d
  let B := rationalCellBudget a b
  let L := InputEncoding.paperLength rows C a b c d
  let H := actualCodeHash (Factory.system hD hd A n r)
  let K := Factory.circuits hD hd A n r
  let seeds := decodeCoins (Factory.length hD hd A n r) (Factory.width hD hd A n r) m coins
  let v := semanticOutput rows C H K spec.service.solver a b c d seeds
  let cap := InputEncoding.queryExtentPolynomial (gateConstant hD hd A) density L
  let O := resourceSatOracle E density requestExtent cap
  obtain ⟨final,totals,events,houtRegs,htrace,hout,_,hot,_,hdispatch,hrun,hword⟩ :=
    hP rows C a b c d ha hc hr coins
  have hvalues : final.output = v.entries.toList := by
    simpa only [v,semanticOutput,RationalOutput.LinearRepair.prepare,prepareRational,
      Array.toArray_toList] using hout.2.2.2.1
  have hword' : houtRegs Assembly.rOUT = Final.outputWord v := by
    rw [hword,hvalues,Assembly.outputWord_eq_ratioWord]
  obtain ⟨run,hrout,hrt,hrs⟩ := Assembly.complete_of_oruns_resource O
    (resourceSatOracle_realizes spec cap) hrun hword'
  refine ⟨run,hrout,?_,?_⟩
  · have hp := hPt L
    have hdisp := Nat.mul_le_mul_left (P.eval L) (Nat.add_le_add_right hdispatch 1)
    have hpoly := Nat.mul_le_mul_right (macroDispatchBound (keySize n r) r B m+1) hp
    change run.time ≤ (3*kE+6)*(P.eval L*(totals.dispatches+1)+totals.oracleTime+1) at hrt
    have hrunBound := hrt.trans (Nat.mul_le_mul_left (3*kE+6)
      (Nat.add_le_add_right (Nat.add_le_add_right hdisp totals.oracleTime) 1))
    have hslack : P.eval L*(macroDispatchBound (keySize n r) r B m+1)+totals.oracleTime+1 ≤
        (P.eval L+1)*(macroDispatchBound (keySize n r) r B m+1)+totals.oracleTime := by
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    have hbound := hrunBound.trans (Nat.mul_le_mul_left (3*kE+6) hslack)
    have heq : (3*kE+6)*((P.eval L+1)*(macroDispatchBound (keySize n r) r B m+1)+totals.oracleTime) =
        ((3*kE+6)*(P.eval L+1))*(macroDispatchBound (keySize n r) r B m+1)+
          (3*kE+6)*totals.oracleTime := by ring
    rw [heq] at hbound
    have hfinal := hbound.trans (Nat.add_le_add_right hpoly ((3*kE+6)*totals.oracleTime))
    rw [hot] at hfinal
    exact hfinal
  · have hmax : max (S.eval L) (PsE.eval cap) ≤ S.eval L+PsE.eval cap := max_le (by omega) (by omega)
    have hb := Nat.mul_le_mul_left (19+kE+1+1)
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hmax) 3)
    exact hrs.trans (hb.trans (hSs L))

end QecReliability.LatentMachine.Runtime
