import ExternalSATHeaderToUnary

/-! An actual fixed-width field subroutine. Its countdown is supplied on a real
stack; this module does not manufacture a width from semantic input metadata.
Specializing to polarity followed by address gives the external literal code. -/
namespace QecReliability.ExternalSATBridge.LiteralToUnary

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls
open HeaderToUnary

/-- Reuse the accepted extractor's finite table, skipping header-length scan. -/
def wordProgram : Program 2 3 11 := { HeaderExtractor.program with entry := 3 }

theorem word_trace (bits tail : List Bool) :
    Trace wordProgram (7 * bits.length + 5)
      ((⟨fun _ => false, ![bits ++ tail, List.replicate bits.length true, []]⟩ :
        StructuredProgram.State 2 3).withPC (some wordProgram.entry))
      ((⟨fun _ => false, ![tail, bits, []]⟩ : StructuredProgram.State 2 3).withPC none) := by
  have ht := HeaderExtractor.take_bits bits (fun _ => false) tail []
  have hr := HeaderExtractor.reverse_finish bits tail
  have ht' : Trace HeaderExtractor.program (4 * bits.length + 2)
      (HeaderExtractor.cfg 3 (fun _ => false) (bits ++ tail)
        (List.replicate bits.length true) [])
      (HeaderExtractor.cfg 7 (HeaderExtractor.regs none) tail [] bits.reverse) := by
    simpa using ht
  have hall := ht'.trans hr
  have hregs : HeaderExtractor.regs none = (fun _ => false) := by
    funext i
    fin_cases i <;> rfl
  have htime : (4 * bits.length + 2) + (3 * bits.length + 3) = 7 * bits.length + 5 := by omega
  rw [htime] at hall
  simpa only [BitProgram.Trace,
    show BitProgram.step wordProgram = BitProgram.step HeaderExtractor.program from rfl,
    show wordProgram.entry = 3 from rfl,
    HeaderExtractor.cfg, HeaderExtractor.finalCfg, hregs,
    StructuredProgram.State.withPC] using hall

def command : StructuredCalls.Cmd 3 4 :=
  .seq (.call (ProgramLinking.liftProgram wordProgram headerRegister headerStack))
    (.call (ProgramLinking.liftProgram CounterConversions.encodeNatProgram id counterStack))

noncomputable abbrev program := StructuredCalls.compiled command 0 2

/-- The supplied unary countdown is consumed, and the arbitrary suffix is
framed throughout both actual subroutine calls. -/
theorem eval_word (bits tail : List Bool) :
    ∃ steps, steps ≤ 7 * bits.length + 5 + CounterConversions.runtimeBound bits ∧
      StructuredCalls.Eval command steps
        (store (bits ++ tail) (List.replicate bits.length true) [] [])
        (store tail [] (Encoding.encodeNat (CounterPrograms.value bits)) []) := by
  have eh := eval_call_lifted wordProgram headerRegister headerStack
    (store [] [] [] []) headerRegister_injective headerStack_injective (word_trace bits tail)
  rw [header_embed, header_embed] at eh
  obtain ⟨k, hk, ht⟩ := CounterConversions.encodeNat_runs CounterConversions.zeroRegs bits
  have ec := eval_call_lifted CounterConversions.encodeNatProgram
    (id : Fin 3 → Fin 3) counterStack (store tail [] [] [])
    Function.injective_id counterStack_injective ht
  rw [counter_embed, counter_embed] at ec
  exact ⟨7 * bits.length + 5 + k, by omega, eh.seq ec⟩

theorem source_word (bits tail : List Bool) :
    BitProgram.RunsIn program (7 * bits.length + 6 + CounterConversions.runtimeBound bits)
      ((store (bits ++ tail) (List.replicate bits.length true) [] []).withPC (some program.entry))
      ((store tail [] (Encoding.encodeNat (CounterPrograms.value bits)) []).withPC none) := by
  obtain ⟨steps, hs, he⟩ := eval_word bits tail
  exact ⟨steps + 1, by omega, compiled_halt_trace he 0 2⟩

theorem literal_value (k i : ℕ) (sign : Bool) (hi : i < 2 ^ k) :
    CounterPrograms.value (sign :: QueryCodec.word k i) =
      2 * i + if sign then 1 else 0 := by
  have hv := PrimitiveTransport.binary_word_value k i hi
  cases sign <;> simp [CounterPrograms.value, hv, Nat.add_comm]

/-- No polarity relabeling assumption: the native polarity bit is precisely
the low binary bit of the actual external literal-code natural. -/
theorem source_literal {v : ℕ} (l : PrefixCNF.Literal v) (tail : List Bool) :
    BitProgram.RunsIn program
      (7 * (v.size + 1) + 6 +
        32 * (Encoding.literalCode (⟨l.1, l.2⟩ : SAT.Literal (Fin v)) + 1) * (v.size + 2))
      ((store (QueryCodec.literal v.size (l.1.val, l.2) ++ tail)
        (List.replicate (v.size + 1) true) [] []).withPC (some program.entry))
      ((store tail [] (Encoding.encodeNat
        (Encoding.literalCode (⟨l.1, l.2⟩ : SAT.Literal (Fin v)))) []).withPC none) := by
  have hv := literal_value v.size l.1.val l.2 (l.1.isLt.trans (Nat.lt_size_self v))
  simpa [QueryCodec.literal, CounterConversions.runtimeBound, hv,
    Encoding.literalCode, Nat.add_assoc] using source_word (l.2 :: QueryCodec.word v.size l.1.val) tail

noncomputable abbrev primitive := GuardedCompiler.primitive program

/-- Primitive execution from a real framed configuration, not an initial
single-input configuration. The caller must construct the countdown stack. -/
theorem primitive_word (bits tail : List Bool) :
    Computation.RunsIn primitive.step
      (7 * (7 * bits.length + 6 + CounterConversions.runtimeBound bits))
      (GuardedCompiler.primitiveCfg program
        ((store (bits ++ tail) (List.replicate bits.length true) [] []).withPC (some program.entry)))
      (GuardedCompiler.primitiveCfg program
        ((store tail [] (Encoding.encodeNat (CounterPrograms.value bits)) []).withPC none)) :=
  GuardedCompiler.primitive_execution program (source_word bits tail)

end QecReliability.ExternalSATBridge.LiteralToUnary
