import LatentZeroRegisterExecution
import ResourceAssemblyAdapter

/-! The exact zero-cause branch of the same fixed finite-tape machine. No SAT
call occurs; all input, coin, interpreter and endpoint-rank cells are charged. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine.Runtime
open FL Trans.Wire Trans.Control RegMachine
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.StoredCodeHashConfidence

private theorem endpoint_zero_values {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program 0 n) (tab : CoefficientTable 0) :
    (RationalOutput.endpointVector rows C tab).entries.toList =
      [RationalOutput.Ratio.dyadic rows (circuitMap C ∅)] := by
  have hf : (fun j : Fin (0+1) => RationalOutput.endpointEntry
      (RationalOutput.Ratio.dyadic rows (circuitMap C ∅))
      (RationalOutput.Ratio.dyadic rows (circuitMap C Finset.univ)) tab j.val) =
      (fun _ : Fin (0+1) => RationalOutput.Ratio.dyadic rows (circuitMap C ∅)) := by
    funext j
    have hj : j.val = 0 := by omega
    simp only [RationalOutput.endpointEntry,hj,↓reduceIte]
  change (Array.ofFn (fun j : Fin (0+1) => RationalOutput.endpointEntry
      (RationalOutput.Ratio.dyadic rows (circuitMap C ∅))
      (RationalOutput.Ratio.dyadic rows (circuitMap C Finset.univ)) tab j.val)).toList = _
  rw [hf]
  simp

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : MultiTape.Machine kE ΓE ΛE} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density PtE PsE T requestExtent)

/-- Exact semantic output for arbitrary physical dimension and no latent causes.
The service may be any valid engine; no query execution is required. -/
theorem zero_machine_execution : ∃ Pspace Ptime : PolynomialEnvelope, ∀ {n : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program 0 n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n 0)
      (Factory.width hD hd A n 0) (rationalRepetitionBudget (2*(0+1)) c d)) → Bool),
    let m := rationalRepetitionBudget (2*(0+1)) c d
    let L := InputEncoding.paperLength rows C a b c d
    let H := actualCodeHash (Factory.system hD hd A n 0)
    let K := Factory.circuits hD hd A n 0
    let seeds := decodeCoins (Factory.length hD hd A n 0) (Factory.width hD hd A n 0) m coins
    let M := Assembly.theMachine E (program hD hd A density) assemblyIndices
    ∃ run : MultiTape.Completed M (input rows C a b c d (List.ofFn coins)),
      Final.Outputs M run (Assembly.outTape kE)
        (semanticOutput rows C H K spec.service.solver a b c d seeds) ∧
      run.time ≤ Ptime.eval L ∧ run.cells ≤ Pspace.eval L := by
  obtain ⟨Q,hQ⟩ := zero_register_execution hD hd A density
  let PP := program hD hd A density
  let Bd : Assembly.Budget := ⟨Q,Q,Q⟩
  have hs := Assembly.regBound_poly PP assemblyIndices Bd
  have hp := Assembly.preBound_poly PP assemblyIndices Bd
  have ho := Assembly.postBound_poly PP assemblyIndices Bd
  have ht : Assembly.PolyBounded (fun L => (3*kE+6)*
      (Assembly.preBound PP assemblyIndices Bd L+1+Assembly.postBound PP assemblyIndices Bd L+1)) := by
    poly_bounded
  have hsp : Assembly.PolyBounded (fun L => (19+kE+1+1)*
      (2*(Assembly.regBound PP assemblyIndices Bd L+PsE.eval 0)+3)) := by poly_bounded
  obtain ⟨Pt,hPt⟩ := ht.envelope
  obtain ⟨Ps,hPs⟩ := hsp.envelope
  refine ⟨Ps,Pt,?_⟩
  intro n rows C a b c d ha hc coins
  dsimp only
  let L := InputEncoding.paperLength rows C a b c d
  let m := rationalRepetitionBudget (2*(0+1)) c d
  let H := actualCodeHash (Factory.system hD hd A n 0)
  let K := Factory.circuits hD hd A n 0
  let seeds := decodeCoins (Factory.length hD hd A n 0) (Factory.width hD hd A n 0) m coins
  let v := semanticOutput rows C H K spec.service.solver a b c d seeds
  let O := resourceSatOracle E density requestExtent 0
  obtain ⟨out,hrun,hword⟩ := hQ O rows C a b c d ha hc coins
  have hvalues : v.entries.toList = [RationalOutput.Ratio.dyadic rows (circuitMap C ∅)] := by
    dsimp only [v,semanticOutput]
    rw [RationalOutput.LinearRepair.prepare_coefficients]
    simp only [Bool.false_eq_true,if_false]
    exact endpoint_zero_values rows C _
  have hout : out Assembly.rOUT = Final.outputWord v := by
    rw [hword,Assembly.outputWord_eq_ratioWord,hvalues]
  obtain ⟨run,hrout,hrt,hrs⟩ := Assembly.complete_of_oruns_resource O
    (resourceSatOracle_realizes spec 0) hrun hout
  refine ⟨run,hrout,hrt.trans (hPt L),?_⟩
  have hmax : max (Assembly.regBound PP assemblyIndices Bd L) (PsE.eval 0) ≤
      Assembly.regBound PP assemblyIndices Bd L+PsE.eval 0 := max_le (by omega) (by omega)
  have hb := Nat.mul_le_mul_left (19+kE+1+1)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hmax) 3)
  exact hrs.trans (hb.trans (hPs L))

end QecReliability.LatentMachine.Runtime
