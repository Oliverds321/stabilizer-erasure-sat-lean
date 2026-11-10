import ExternalSATLiteralToUnary

/-! The accepted literal parser uses countdown PRESENCE only, not countdown
bit values. These proofs extend its contract without changing one instruction.
In particular the actual encodeNat(width) produced by width preparation works. -/
namespace QecReliability.ExternalSATBridge.CountedLiteral

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls
open HeaderToUnary

 theorem take_one (r : Fin 2 → Bool) (marker b : Bool) (tail count out : List Bool) :
    Trace HeaderExtractor.program 4
      (HeaderExtractor.cfg 3 r (b :: tail) (marker :: count) out)
      (HeaderExtractor.cfg 3 (HeaderExtractor.regs (some b)) tail count (b :: out)) := by
  refine .cons (b := HeaderExtractor.cfg 4 (HeaderExtractor.regs (some marker)) (b :: tail) count out) ?_ ?_
  · simp [step, HeaderExtractor.program, HeaderExtractor.cfg, execInstr,
      funext_iff, Fin.forall_fin_succ]
  · refine .cons (b := HeaderExtractor.cfg 5 (HeaderExtractor.regs (some marker)) (b :: tail) count out) ?_ ?_
    · simp [step, HeaderExtractor.program, HeaderExtractor.cfg, execInstr, HeaderExtractor.regs]
    · refine .cons (b := HeaderExtractor.cfg 6 (HeaderExtractor.regs (some b)) tail count out) ?_ ?_
      · simp [step, HeaderExtractor.program, HeaderExtractor.cfg, execInstr,
          funext_iff, Fin.forall_fin_succ]
      · refine .cons ?_ (.refl _)
        simp [step, HeaderExtractor.program, HeaderExtractor.cfg, execInstr, HeaderExtractor.regs,
          funext_iff, Fin.forall_fin_succ]

theorem take_bits (bits count : List Bool) (hcount : count.length = bits.length)
    (r : Fin 2 → Bool) (tail out : List Bool) :
    Trace HeaderExtractor.program (4 * bits.length + 2)
      (HeaderExtractor.cfg 3 r (bits ++ tail) count out)
      (HeaderExtractor.cfg 7 (HeaderExtractor.regs none) tail [] (bits.reverse ++ out)) := by
  induction bits generalizing count r out with
  | nil =>
    have hc : count = [] := by simpa using hcount
    subst count
    simpa using HeaderExtractor.take_empty r tail out
  | cons b bits ih =>
    cases count with
    | nil => simp at hcount
    | cons marker count =>
      have hc : count.length = bits.length := by simpa using hcount
      have hfirst := take_one r marker b (bits ++ tail) count out
      have hrest := ih count hc (HeaderExtractor.regs (some b)) (b :: out)
      have hchain := hfirst.trans hrest
      convert hchain using 1 <;>
        simp [List.reverse_cons, List.append_assoc, Nat.mul_add,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem word_trace (bits count tail : List Bool) (hcount : count.length = bits.length) :
    Trace LiteralToUnary.wordProgram (7 * bits.length + 5)
      ((⟨fun _ => false, ![bits ++ tail, count, []]⟩ : StructuredProgram.State 2 3).withPC
        (some LiteralToUnary.wordProgram.entry))
      ((⟨fun _ => false, ![tail, bits, []]⟩ : StructuredProgram.State 2 3).withPC none) := by
  have ht := take_bits bits count hcount (fun _ => false) tail []
  have ht' : Trace HeaderExtractor.program (4 * bits.length + 2)
      (HeaderExtractor.cfg 3 (fun _ => false) (bits ++ tail) count [])
      (HeaderExtractor.cfg 7 (HeaderExtractor.regs none) tail [] bits.reverse) := by simpa using ht
  have hall := ht'.trans (HeaderExtractor.reverse_finish bits tail)
  have hr : HeaderExtractor.regs none = (fun _ => false) := by
    funext i
    fin_cases i <;> rfl
  have htime : (4 * bits.length + 2) + (3 * bits.length + 3) = 7 * bits.length + 5 := by omega
  rw [htime] at hall
  simpa only [BitProgram.Trace,
    show BitProgram.step LiteralToUnary.wordProgram = BitProgram.step HeaderExtractor.program from rfl,
    show LiteralToUnary.wordProgram.entry = 3 from rfl,
    HeaderExtractor.cfg, HeaderExtractor.finalCfg, hr, StructuredProgram.State.withPC] using hall

theorem eval_word (bits count tail : List Bool) (hcount : count.length = bits.length) :
    ∃ steps, steps ≤ 7 * bits.length + 5 + CounterConversions.runtimeBound bits ∧
      StructuredCalls.Eval LiteralToUnary.command steps (store (bits ++ tail) count [] [])
        (store tail [] (Encoding.encodeNat (CounterPrograms.value bits)) []) := by
  have eh := eval_call_lifted LiteralToUnary.wordProgram headerRegister headerStack
    (store [] [] [] []) headerRegister_injective headerStack_injective (word_trace bits count tail hcount)
  rw [header_embed, header_embed] at eh
  obtain ⟨k, hk, ht⟩ := CounterConversions.encodeNat_runs CounterConversions.zeroRegs bits
  have ec := eval_call_lifted CounterConversions.encodeNatProgram
    (id : Fin 3 → Fin 3) counterStack (store tail [] [] [])
    Function.injective_id counterStack_injective ht
  rw [counter_embed, counter_embed] at ec
  exact ⟨7 * bits.length + 5 + k, by omega, eh.seq ec⟩

theorem source_word (bits count tail : List Bool) (hcount : count.length = bits.length) :
    BitProgram.RunsIn LiteralToUnary.program (7 * bits.length + 6 + CounterConversions.runtimeBound bits)
      ((store (bits ++ tail) count [] []).withPC (some LiteralToUnary.program.entry))
      ((store tail [] (Encoding.encodeNat (CounterPrograms.value bits)) []).withPC none) := by
  obtain ⟨steps, hs, he⟩ := eval_word bits count tail hcount
  exact ⟨steps + 1, by omega, compiled_halt_trace he 0 2⟩

/-- The genuine width-preparation output, including its false terminator, is
accepted by the unchanged literal converter. -/
theorem source_literal {v : ℕ} (l : PrefixCNF.Literal v) (tail : List Bool) :
    BitProgram.RunsIn LiteralToUnary.program
      (7 * (v.size + 1) + 6 +
        32 * (Encoding.literalCode (⟨l.1, l.2⟩ : SAT.Literal (Fin v)) + 1) * (v.size + 2))
      ((store (QueryCodec.literal v.size (l.1.val, l.2) ++ tail)
        (Encoding.encodeNat v.size) [] []).withPC (some LiteralToUnary.program.entry))
      ((store tail [] (Encoding.encodeNat
        (Encoding.literalCode (⟨l.1, l.2⟩ : SAT.Literal (Fin v)))) []).withPC none) := by
  have hv := LiteralToUnary.literal_value v.size l.1.val l.2 (l.1.isLt.trans (Nat.lt_size_self v))
  have hc : (Encoding.encodeNat v.size).length = (l.2 :: QueryCodec.word v.size l.1.val).length := by simp
  simpa [QueryCodec.literal, CounterConversions.runtimeBound, hv,
    Encoding.literalCode, Nat.add_assoc] using
    source_word (l.2 :: QueryCodec.word v.size l.1.val) (Encoding.encodeNat v.size) tail hc

end QecReliability.ExternalSATBridge.CountedLiteral
