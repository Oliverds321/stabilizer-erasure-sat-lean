import ExternalSATWidthPreparation

/-! Actual initialization of the canonical traversal's unary bound2v from the
retained binary variable header. The header is copied and shifted physically,
then the accepted finite binary-to-unary converter runs on that copied word. -/
namespace QecReliability.ExternalSATBridge.CandidateBound

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls
open HeaderToUnary (store counterStack counterStack_injective counter_embed)

abbrev copyProgram : Program 3 4 8 := StackRoutines.copyProgram 0 1 3 0 1

theorem copy_eval (bits : List Bool) :
    Eval (.call copyProgram) (7 * bits.length + 5)
      (store bits [] [] []) (store bits bits [] []) := by
  apply Eval.call
  have h := ListRegisterProgram.copy_run (0 : Fin 4) 1 3 (0 : Fin 3) 1
    (by decide) (by decide) (by decide) (by decide)
    (fun _ => false) (![bits, [], [], []] : Fin 4 → List Bool) rfl
  have hr : readRegs (fun _ : Fin 3 => false) 0 1 none = (fun _ => false) := by
    funext i; fin_cases i <;> simp [readRegs]
  have hs : StackRoutines.copyStacks (0 : Fin 4) 1
      (![bits, [], [], []] : Fin 4 → List Bool) = ![bits, bits, [], []] := by
    funext i; fin_cases i <;> simp [StackRoutines.copyStacks]
  simpa only [ListRegisterProgram.Run, store, StructuredProgram.State.withPC, hr, hs,
    show (![bits, [], [], []] : Fin 4 → List Bool) 0 = bits from rfl] using h

def shift : StructuredCalls.Cmd 3 4 := .base (.atom (.push 1 0))

theorem shift_eval (bits : List Bool) :
    Eval shift 1 (store bits bits [] []) (store bits (false :: bits) [] []) := by
  apply Eval.base
  have h := StructuredProgram.Eval.atom (.push (1 : Fin 4) (0 : Fin 3)) (store bits bits [] [])
  have hs : Function.update (![bits, bits, [], []] : Fin 4 → List Bool) 1 (false :: bits) =
      ![bits, false :: bits, [], []] := by
    funext i; fin_cases i <;> simp
  simpa only [store, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
    show (![bits, bits, [], []] : Fin 4 → List Bool) 1 = bits from rfl, hs] using h

noncomputable def command : StructuredCalls.Cmd 3 4 :=
  .seq (.call copyProgram) (.seq shift
    (.call (ProgramLinking.liftProgram CounterConversions.encodeNatProgram id counterStack)))
noncomputable abbrev program := compiled command 0 2

def timeBound (bits : List Bool) : ℕ :=
  7 * bits.length + 7 + 32 * (2 * CounterPrograms.value bits + 1) * (bits.length + 2)

theorem value_shift (bits : List Bool) :
    CounterPrograms.value (false :: bits) = 2 * CounterPrograms.value bits := by
  simp [CounterPrograms.value]

theorem source_bits (bits : List Bool) :
    BitProgram.RunsIn program (timeBound bits)
      ((store bits [] [] []).withPC (some program.entry))
      ((store bits [] (Encoding.encodeNat (2 * CounterPrograms.value bits)) []).withPC none) := by
  obtain ⟨n, hn, ht⟩ := CounterConversions.encodeNat_runs CounterConversions.zeroRegs (false :: bits)
  have he := eval_call_lifted CounterConversions.encodeNatProgram
    (id : Fin 3 → Fin 3) counterStack (store bits [] [] [])
    Function.injective_id counterStack_injective ht
  rw [counter_embed, counter_embed, value_shift] at he
  have hall := (copy_eval bits).seq ((shift_eval bits).seq he)
  refine ⟨(7 * bits.length + 5) + (1 + n) + 1, ?_, compiled_halt_trace hall 0 2⟩
  simp only [CounterConversions.runtimeBound, value_shift, List.length_cons] at hn
  have hlen : bits.length + 1 + 1 = bits.length + 2 := by omega
  rw [hlen] at hn
  dsimp only [timeBound]
  omega

/-- The real retained query word is sufficient, with no supplied unary bound. -/
theorem source_variable_header (v : ℕ) :
    BitProgram.RunsIn program
      (7 * v.size + 7 + 32 * (2 * v + 1) * (v.size + 2))
      ((store (QueryCodec.word v.size v) [] [] []).withPC (some program.entry))
      ((store (QueryCodec.word v.size v) [] (Encoding.encodeNat (2 * v)) []).withPC none) := by
  have hv := PrimitiveTransport.binary_word_value v.size v (Nat.lt_size_self v)
  simpa only [timeBound, hv, QueryCodec.word_length] using source_bits (QueryCodec.word v.size v)

end QecReliability.ExternalSATBridge.CandidateBound
