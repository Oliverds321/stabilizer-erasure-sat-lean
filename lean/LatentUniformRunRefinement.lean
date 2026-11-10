import LatentPositiveMachineExecution
import LatentZeroMachineExecution
import LatentOracleTime

/-! Discharges the original latent run-refinement obligation for one actual
fixed finite-tape machine, both latent-zero and positive branches. Bounds are
uniform over all coins; SAT rate uses actual padded variable count. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine.Runtime
open FL Trans.Wire Trans.Control RegMachine
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.StoredCodeHashConfidence

/-- Uniform actual-engine work cap. It does not include interpreter work. -/
def oracleWorkBound {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program r n) (G density B m : ℕ)
    (Pt : PolynomialEnvelope) (T : ℕ → ℕ) : ℕ :=
  2*(r+1)*(2*m+1)*trialCallBound (keySize n r) B *
    Pt.eval (queryExtentCap rows C density (G*keySize n r)) *
    T (QuantumService.engineVariables rows C density (G*keySize n r))

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : MultiTape.Machine kE ΓE ΛE} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density PtE PsE T requestExtent) (hT : Monotone T)
include hT

/-- No implementation, run, seed, success-event or tape-resource premise remains.
Only the engine resource specification and fixed hash certificate are parameters.
Uniqueness quantifies over every completed run and every decoded output. -/
theorem uniform_run_refinement : ∃ Pspace Ptime : PolynomialEnvelope, ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → 0<c →
    let m := rationalRepetitionBudget (2*(r+1)) c d
    let B := rationalCellBudget a b
    let L := InputEncoding.paperLength rows C a b c d
    let H := actualCodeHash (Factory.system hD hd A n r)
    let K := Factory.circuits hD hd A n r
    let N := CodeHash.repeatBits (Factory.length hD hd A n r) (Factory.width hD hd A n r) m
    let M := Assembly.theMachine E (program hD hd A density) assemblyIndices
    RunRefinement rows C H K spec.service.solver a b c d M (Assembly.outTape kE) N
      (Ptime.eval L*(macroDispatchBound (keySize n r) r B m+1)+
        (3*kE+6)*oracleWorkBound rows C (gateConstant hD hd A) density B m PtE T)
      (Pspace.eval L) (decodeCoins (Factory.length hD hd A n r) (Factory.width hD hd A n r) m) := by
  obtain ⟨Sp,Tp,hp⟩ := positive_machine_execution hD hd A density spec
  obtain ⟨Sz,Tz,hz⟩ := zero_machine_execution hD hd A density spec
  have hsp : Assembly.PolyBounded Sp.eval := by unfold PolynomialEnvelope.eval; poly_bounded
  have hsz : Assembly.PolyBounded Sz.eval := by unfold PolynomialEnvelope.eval; poly_bounded
  have htp : Assembly.PolyBounded Tp.eval := by unfold PolynomialEnvelope.eval; poly_bounded
  have htz : Assembly.PolyBounded Tz.eval := by unfold PolynomialEnvelope.eval; poly_bounded
  have hs : Assembly.PolyBounded (fun L => Sp.eval L+Sz.eval L) := by poly_bounded
  have ht : Assembly.PolyBounded (fun L => Tp.eval L+Tz.eval L) := by poly_bounded
  obtain ⟨S,hS⟩ := hs.envelope
  obtain ⟨P,hP⟩ := ht.envelope
  refine ⟨S,P,?_⟩
  intro n r rows C a b c d ha hc
  dsimp only
  let m := rationalRepetitionBudget (2*(r+1)) c d
  let B := rationalCellBudget a b
  let L := InputEncoding.paperLength rows C a b c d
  let H := actualCodeHash (Factory.system hD hd A n r)
  let K := Factory.circuits hD hd A n r
  let N := CodeHash.repeatBits (Factory.length hD hd A n r) (Factory.width hD hd A n r) m
  let M := Assembly.theMachine E (program hD hd A density) assemblyIndices
  let decode := decodeCoins (Factory.length hD hd A n r) (Factory.width hD hd A n r) m
  let tb := P.eval L*(macroDispatchBound (keySize n r) r B m+1)+
    (3*kE+6)*oracleWorkBound rows C (gateConstant hD hd A) density B m PtE T
  have hSsum := hS L
  have hTsum := hP L
  have hSp : Sp.eval L ≤ S.eval L := by omega
  have hSz : Sz.eval L ≤ S.eval L := by omega
  have hTp : Tp.eval L ≤ P.eval L := by omega
  have hTz : Tz.eval L ≤ P.eval L := by omega
  have hcomplete : ∀ coins : Fin N → Bool,
      ∃ run : MultiTape.Completed M (input rows C a b c d (List.ofFn coins)),
        Final.Outputs M run (Assembly.outTape kE)
          (semanticOutput rows C H K spec.service.solver a b c d (decode coins)) ∧
        run.time ≤ tb ∧ run.cells ≤ S.eval L := by
    intro coins
    by_cases hr : r=0
    · subst r
      obtain ⟨run,hout,hrt,hrs⟩ := hz rows C a b c d ha hc coins
      refine ⟨run,hout,?_,hrs.trans hSz⟩
      have ht0 := hrt.trans hTz
      have hmul := Nat.mul_le_mul_left (P.eval L)
        (show 1 ≤ macroDispatchBound (keySize n 0) 0 B m+1 by omega)
      simp only [Nat.mul_one] at hmul
      exact (ht0.trans hmul).trans (Nat.le_add_right _ _)
    · have hrpos : 0<r := Nat.pos_of_ne_zero hr
      obtain ⟨run,hout,hrt,hrs⟩ := hp rows C a b c d ha hc hrpos coins
      have ho := Factory.prepare_resource_time hD hd A spec hT rows C hrpos B m coins
      have hscaled := Nat.mul_le_mul_left (3*kE+6) ho
      have hpoly := Nat.mul_le_mul_right (macroDispatchBound (keySize n r) r B m+1) hTp
      refine ⟨run,hout,?_,hrs.trans hSp⟩
      exact hrt.trans (Nat.add_le_add hpoly hscaled)
  constructor
  · exact hcomplete
  · intro coins run v hv
    obtain ⟨run0,hout,_,_⟩ := hcomplete coins
    have hfin := (MultiTape.Completed.unique run run0).1
    have hv0 : Final.Outputs M run0 (Assembly.outTape kE) v := by
      unfold Final.Outputs at hv ⊢
      rw [← hfin]
      exact hv
    exact Final.Outputs.unique hv0 hout

end QecReliability.LatentMachine.Runtime
