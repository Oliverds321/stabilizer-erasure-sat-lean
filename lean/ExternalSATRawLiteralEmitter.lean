import ExternalSATRetainedLiteral

/-! A literal-to-raw-unary emission subroutine in the body parser's fixed layout.
Arity flags are real retained bit registers, and the output is a reversed stream
accumulator. No canonical ordering or whole-query parsing is asserted here. -/
namespace QecReliability.ExternalSATBridge.RawLiteralEmitter

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls

def regs (low high : Bool) : Fin 5 → Bool := ![false, false, false, low, high]

def state (low high : Bool)
    (input vars width clauses work literal scratch accumulator : List Bool) :
    StructuredProgram.State 5 8 :=
  ⟨regs low high, ![input, vars, width, clauses, work, literal, scratch, accumulator]⟩

abbrev registerPorts : Fin 3 → Fin 5 := fun i => i.castAdd 2
abbrev stackPorts : Fin 7 → Fin 8 := fun i => i.castAdd 1

theorem registerPorts_injective : Function.Injective registerPorts := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin 5 => x.val) h

theorem stackPorts_injective : Function.Injective stackPorts := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin 8 => x.val) h

/-- The two arity bits and accumulator are outside the lifted parser's ports. -/
theorem parser_embed (low high : Bool) (a b c d e f g accumulator : List Bool) :
    embedState registerPorts stackPorts (state low high [] [] [] [] [] [] [] accumulator)
      (QueryPreparation.store a b c d e f g) = state low high a b c d e f g accumulator := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ registerPorts_injective stackPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; rfl
  · intro i hi
    fin_cases i <;> simp_all [state, stackPorts, Fin.exists_fin_succ]

abbrev transferProgram : Program 5 8 4 := StackRoutines.transferProgram 5 7 0 1

/-- The transfer count includes the real halt after the library trace-to-exit.
It consumes stack5, reverses its word onto stack7, and preserves both arity bits. -/
theorem transfer_trace (low high : Bool) (input vars width clauses literal accumulator : List Bool) :
    Trace transferProgram (3 * literal.length + 3)
      ((state low high input vars width clauses [] literal [] accumulator).withPC
        (some transferProgram.entry))
      ((state low high input vars width clauses [] [] [] (literal.reverse ++ accumulator)).withPC none) := by
  have ht := StackRoutines.transferProgram_trace (5 : Fin 8) 7 (0 : Fin 5) 1
    (by decide) (by decide) (regs low high)
    (![input, vars, width, clauses, [], literal, [], accumulator] : Fin 8 → List Bool)
  have hh := StackRoutines.halt_after_trace transferProgram ht 3 rfl rfl
  have hregs : readRegs (regs low high) 0 1 none = regs low high := by
    funext i
    fin_cases i <;> simp [readRegs, regs]
  have hstacks : StackRoutines.transferStacks (5 : Fin 8) 7
      (![input, vars, width, clauses, [], literal, [], accumulator] : Fin 8 → List Bool) =
      ![input, vars, width, clauses, [], [], [], literal.reverse ++ accumulator] := by
    funext i
    fin_cases i <;> simp [StackRoutines.transferStacks]
  simpa only [StackRoutines.transferResult, hregs, hstacks, state,
    StructuredProgram.State.withPC, Nat.add_assoc,
    show (![input, vars, width, clauses, [], literal, [], accumulator] : Fin 8 → List Bool) 5 = literal from rfl,
    show (2 : ℕ) + 1 = 3 from rfl] using hh

noncomputable def command : StructuredCalls.Cmd 5 8 :=
  .seq (.call (ProgramLinking.liftProgram RetainedLiteral.program registerPorts stackPorts))
    (.call transferProgram)

noncomputable abbrev program := compiled command 0 7

/-- Bound for evaluating the command; the separately compiled source adds one
final caller halt. The retained parser's own halt is already in its bound. -/
def timeBound (k value : ℕ) : ℕ := RetainedLiteral.timeBound k value + 3 * (value + 1) + 3

theorem eval_word (bits width tail vars clauses accumulator : List Bool) (low high : Bool)
    (hw : width.length = bits.length) :
    ∃ steps, steps ≤ timeBound bits.length (CounterPrograms.value bits) ∧
      StructuredCalls.Eval command steps
        (state low high (bits ++ tail) vars width clauses [] [] [] accumulator)
        (state low high tail vars width clauses [] [] []
          ((Encoding.encodeNat (CounterPrograms.value bits)).reverse ++ accumulator)) := by
  obtain ⟨k, hk, ht⟩ := RetainedLiteral.source_word bits width tail vars clauses hw
  have ep := eval_call_lifted RetainedLiteral.program registerPorts stackPorts
    (state low high [] [] [] [] [] [] [] accumulator)
    registerPorts_injective stackPorts_injective ht
  rw [parser_embed, parser_embed] at ep
  have et : StructuredCalls.Eval (.call transferProgram)
      (3 * (Encoding.encodeNat (CounterPrograms.value bits)).length + 3)
      (state low high tail vars width clauses [] (Encoding.encodeNat (CounterPrograms.value bits)) [] accumulator)
      (state low high tail vars width clauses [] [] []
        ((Encoding.encodeNat (CounterPrograms.value bits)).reverse ++ accumulator)) :=
    .call transferProgram (transfer_trace low high tail vars width clauses
      (Encoding.encodeNat (CounterPrograms.value bits)) accumulator)
  refine ⟨k + (3 * (Encoding.encodeNat (CounterPrograms.value bits)).length + 3), ?_, ep.seq et⟩
  simp only [Encoding.length_encodeNat, timeBound]
  omega

theorem source_word (bits width tail vars clauses accumulator : List Bool) (low high : Bool)
    (hw : width.length = bits.length) :
    BitProgram.RunsIn program (timeBound bits.length (CounterPrograms.value bits) + 1)
      ((state low high (bits ++ tail) vars width clauses [] [] [] accumulator).withPC (some program.entry))
      ((state low high tail vars width clauses [] [] []
        ((Encoding.encodeNat (CounterPrograms.value bits)).reverse ++ accumulator)).withPC none) := by
  obtain ⟨steps, hs, he⟩ := eval_word bits width tail vars clauses accumulator low high hw
  exact ⟨steps + 1, Nat.add_le_add_right hs 1, compiled_halt_trace he 0 7⟩

theorem eval_literal {v : ℕ} (l : PrefixCNF.Literal v)
    (tail vars clauses accumulator : List Bool) (low high : Bool) :
    ∃ steps, steps ≤ timeBound (v.size + 1)
        (Encoding.literalCode (⟨l.1, l.2⟩ : SAT.Literal (Fin v))) ∧
      StructuredCalls.Eval command steps
        (state low high (QueryCodec.literal v.size (l.1.val, l.2) ++ tail)
          vars (Encoding.encodeNat v.size) clauses [] [] [] accumulator)
        (state low high tail vars (Encoding.encodeNat v.size) clauses [] [] []
          ((Encoding.encodeNat (Encoding.literalCode (⟨l.1, l.2⟩ : SAT.Literal (Fin v)))).reverse ++ accumulator)) := by
  have hv := LiteralToUnary.literal_value v.size l.1.val l.2 (l.1.isLt.trans (Nat.lt_size_self v))
  have hw : (Encoding.encodeNat v.size).length = (l.2 :: QueryCodec.word v.size l.1.val).length := by simp
  simpa [QueryCodec.literal, hv, Encoding.literalCode] using
    eval_word (l.2 :: QueryCodec.word v.size l.1.val) (Encoding.encodeNat v.size)
      tail vars clauses accumulator low high hw

theorem source_literal {v : ℕ} (l : PrefixCNF.Literal v)
    (tail vars clauses accumulator : List Bool) (low high : Bool) :
    BitProgram.RunsIn program
      (timeBound (v.size + 1) (Encoding.literalCode (⟨l.1, l.2⟩ : SAT.Literal (Fin v))) + 1)
      ((state low high (QueryCodec.literal v.size (l.1.val, l.2) ++ tail)
        vars (Encoding.encodeNat v.size) clauses [] [] [] accumulator).withPC (some program.entry))
      ((state low high tail vars (Encoding.encodeNat v.size) clauses [] [] []
        ((Encoding.encodeNat (Encoding.literalCode (⟨l.1, l.2⟩ : SAT.Literal (Fin v)))).reverse ++ accumulator)).withPC none) := by
  obtain ⟨steps, hs, he⟩ := eval_literal l tail vars clauses accumulator low high
  exact ⟨steps + 1, Nat.add_le_add_right hs 1, compiled_halt_trace he 0 7⟩

end QecReliability.ExternalSATBridge.RawLiteralEmitter
