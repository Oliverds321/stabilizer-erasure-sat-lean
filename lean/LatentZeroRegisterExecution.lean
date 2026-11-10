import LatentZeroExecution
import Assembly.Instance

/-! The actual zero-latent branch of the installed register program. This is
oracle-independent: its terminal loop test executes no oracle instruction.
Physical dimension and the complete sampled coin tape remain unrestricted. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine.Runtime
open FL Trans.Wire Trans.Control RegMachine Interp
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)

/-- The same main program, with no loop-body iteration and no SAT call.
The structural space and pre/post bounds are polynomial by Assembly.Instance. -/
theorem zero_register_execution : ∃ Q : PolynomialEnvelope, ∀ (O : OracleSpec)
    {n : ℕ} (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program 0 n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n 0)
      (Factory.width hD hd A n 0) (rationalRepetitionBudget (2*(0+1)) c d)) → Bool),
    let L := InputEncoding.paperLength rows C a b c d
    let Bd : Assembly.Budget := ⟨Q,Q,Q⟩
    let PP := program hD hd A density
    ∃ out : Regs 20,
      Assembly.ORuns O (Assembly.regBound PP assemblyIndices Bd L)
        (Assembly.mainProg PP assemblyIndices).body
        (inputRegs (R := 19) (input rows C a b c d (List.ofFn coins))) out
        (Assembly.preBound PP assemblyIndices Bd L + 1 +
          Assembly.postBound PP assemblyIndices Bd L) ∧
      out Assembly.rOUT = Assembly.ratioWord
        [RationalOutput.Ratio.dyadic rows (circuitMap C ∅)] := by
  obtain ⟨Q,hQ⟩ := zero_execution hD hd A density
  refine ⟨Q,?_⟩
  intro O n rows C a b c d ha hc coins
  let L := InputEncoding.paperLength rows C a b c d
  let Bd : Assembly.Budget := ⟨Q,Q,Q⟩
  let PP := program hD hd A density
  let v := Ty.enc (TArg TX) (initializedValue hD hd A rows C a b c d (List.ofFn coins))
  obtain ⟨hinit,_,hdone,hout⟩ := hQ rows C a b c d ha hc coins
  have hS := Assembly.regBound_hS PP assemblyIndices Bd L
  have hm := Assembly.regBound_hm PP assemblyIndices Bd L
  have hpre := Assembly.preamble_run (O := O) hS hm hinit hdone
  have hf := hpre.fits_end
  have hloop : Assembly.ORuns O (Assembly.regBound PP assemblyIndices Bd L)
      (Assembly.mainLoop PP assemblyIndices)
      (Assembly.headRegs v true) (Assembly.headRegs v true) 1 := by
    refine ⟨1, _, Stmt.BigStep.loopF (σ := Assembly.σO O) hf trivial
      (Assembly.headIs_eval Assembly.rDN _ true (by simp)) (by decide) hf, ?_⟩
    simp [Assembly.σO, oracleSem, OInstr.cost, Instr.cost]
  have hpost := Assembly.postamble_run (O := O) hS hout hloop.fits_end
  exact ⟨_, (hpre.seq (hloop.seq hpost)).mono
    (by unfold Assembly.preBound Assembly.postBound
        dsimp only [PP, Bd, L, Assembly.Budget.value, Assembly.Budget.cost, Assembly.Budget.depth]
        omega), rfl⟩

end QecReliability.LatentMachine.Runtime
end
