import ExternalSATRawBodyParser
import ExternalSATRawOutputReverse

/-! An entire valid native query is lowered by one fixed finite controller to
an explicit NONcanonical raw-unary body. Both headers are parsed from the actual
input, width is computed on real stacks, every clause/literal is consumed, and
output is physically reversed into forward order. Canonicalization is separate. -/
namespace QecReliability.ExternalSATBridge.RawQueryLowering

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls
open RawLiteralEmitter (state)

noncomputable def command : StructuredCalls.Cmd 5 8 :=
  .seq (.call (ProgramLinking.liftProgram QueryPreparation.program
    RawLiteralEmitter.registerPorts RawLiteralEmitter.stackPorts))
    (.seq RawBodyParser.command (.call RawOutputReverse.program))

noncomputable abbrev program := compiled command 0 7

def timeBound (q : SATRequest) : ℕ :=
  QueryPreparation.timeBound q.varCount q.formula.length + (1 + RawBodyParser.loopBound q.formula) +
    (9 * (RawBodyParser.output q.formula).length + 7) + 1

def ready (q : SATRequest) : StructuredProgram.State 5 8 :=
  state false false [] (QueryCodec.word q.varCount.size q.varCount)
    (Encoding.encodeNat q.varCount.size) (QueryCodec.word q.formula.length.size q.formula.length)
    [] [] [] (RawBodyParser.output q.formula)

/-- Real trace composition, including copied-width calls and final reversal.
The budget is expressed by the actual formula's explicit finite sums; a uniform
polynomial envelope is a subsequent resource lemma, not assumed here. -/
theorem query_eval (q : SATRequest) :
    ∃ steps, steps + 1 ≤ timeBound q ∧
      Eval command steps (state false false (QueryCodec.encode q) [] [] [] [] [] [] []) (ready q) := by
  obtain ⟨k, hk, ht⟩ := QueryPreparation.source_query q
  rw [← QueryPreparation.initial_eq] at ht
  have hp := eval_call_lifted QueryPreparation.program
    RawLiteralEmitter.registerPorts RawLiteralEmitter.stackPorts
    (state false false [] [] [] [] [] [] [] [])
    RawLiteralEmitter.registerPorts_injective RawLiteralEmitter.stackPorts_injective ht
  rw [QueryPreparation.ready, RawLiteralEmitter.parser_embed, RawLiteralEmitter.parser_embed] at hp
  obtain ⟨j, hj, hb⟩ := RawBodyParser.body_eval q.formula q.width
    (QueryCodec.word q.varCount.size q.varCount)
    (QueryCodec.word q.formula.length.size q.formula.length) []
  have hb' : Eval RawBodyParser.command j
      (state false false (QueryCodec.body q.varCount.size (QueryCodec.plain q.formula))
        (QueryCodec.word q.varCount.size q.varCount) (Encoding.encodeNat q.varCount.size)
        (QueryCodec.word q.formula.length.size q.formula.length) [] [] [] [])
      (state false false [] (QueryCodec.word q.varCount.size q.varCount) (Encoding.encodeNat q.varCount.size)
        (QueryCodec.word q.formula.length.size q.formula.length) [] [] []
        (RawBodyParser.output q.formula).reverse) := by
    simpa only [RawBodyParser.input, List.append_nil] using hb
  have hr := RawOutputReverse.eval_reverse [] (QueryCodec.word q.varCount.size q.varCount)
    (Encoding.encodeNat q.varCount.size) (QueryCodec.word q.formula.length.size q.formula.length)
    (RawBodyParser.output q.formula).reverse
  have hr' : Eval (.call RawOutputReverse.program) (9 * (RawBodyParser.output q.formula).length + 7)
      (state false false [] (QueryCodec.word q.varCount.size q.varCount) (Encoding.encodeNat q.varCount.size)
        (QueryCodec.word q.formula.length.size q.formula.length) [] [] []
        (RawBodyParser.output q.formula).reverse) (ready q) := by
    simpa only [List.length_reverse, List.reverse_reverse, ready] using hr
  refine ⟨k + (j + (9 * (RawBodyParser.output q.formula).length + 7)), ?_, hp.seq (hb'.seq hr')⟩
  dsimp only [timeBound]
  omega

theorem initial_eq (input : List Bool) :
    (state false false input [] [] [] [] [] [] []).withPC (some program.entry) =
      BitProgram.initial program input := by
  have hr : RawLiteralEmitter.regs false false = (fun _ => false) := by
    funext i; fin_cases i <;> rfl
  dsimp only [state, StructuredProgram.State.withPC, BitProgram.initial]
  rw [hr]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem source_query (q : SATRequest) :
    BitProgram.RunsIn program (timeBound q)
      (BitProgram.initial program (QueryCodec.encode q)) ((ready q).withPC none) := by
  obtain ⟨steps, hs, he⟩ := query_eval q
  have ht := compiled_halt_trace he 0 7
  rw [initial_eq] at ht
  exact ⟨steps + 1, hs, ht⟩

noncomputable abbrev primitive := GuardedCompiler.primitive program

/-- Actual finite primitive execution from the single encoded input. In
particular source tape7 contains the exact forward raw body and source tape0
is empty; the cleared input and scratch fields are accounted for in ready. -/
theorem primitive_query (q : SATRequest) :
    ∃ steps final,
      Computation.Trace primitive.step steps (primitive.init (QueryCodec.encode q)) final ∧
      steps ≤ 7 * timeBound q ∧
      (∀ i : Fin 8, final.tapes i = Turing.Tape.mk₁ (((ready q).stacks i).map some)) := by
  have hp := GuardedCompiler.primitive_execution program (source_query q)
  rw [GuardedCompiler.primitive_initial] at hp
  obtain ⟨steps, hs, ht⟩ := hp
  refine ⟨steps, GuardedCompiler.primitiveCfg program ((ready q).withPC none), ht, hs, ?_⟩
  intro i
  rw [GuardedCompiler.primitive_tape]

end QecReliability.ExternalSATBridge.RawQueryLowering
