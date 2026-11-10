import ExternalSATRawClauseParser

/-! Complete valid-body traversal by an actual presence-controlled while loop.
The raw output preserves clause/literal order and duplicates, not canonical CNF
order. Clause count is not consulted by a semantic runtime branch. -/
namespace QecReliability.ExternalSATBridge.RawBodyParser

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls
open RawLiteralEmitter (state regs)

def input {v : ℕ} (F : PrefixCNF.Formula v) : List Bool :=
  QueryCodec.body v.size (QueryCodec.plain F)

def output {v : ℕ} (F : PrefixCNF.Formula v) : List Bool := F.flatMap RawClauseParser.rawClause

def loopBound {v : ℕ} (F : PrefixCNF.Formula v) : ℕ :=
  1 + (F.map (fun c => 13 + RawClauseParser.fieldCost c)).sum

@[simp] theorem input_cons {v : ℕ} (c : List (PrefixCNF.Literal v)) (F : PrefixCNF.Formula v) :
    input (c :: F) = QueryCodec.clause v.size (c.map (fun l => (l.1.val, l.2))) ++ input F := by
  simp [input, QueryCodec.body, QueryCodec.plain]

theorem input_cons_ne_nil {v : ℕ} (c : List (PrefixCNF.Literal v)) (F : PrefixCNF.Formula v) :
    input (c :: F) ≠ [] := by
  simp [input_cons, QueryCodec.clause, QueryCodec.word]

def observed (bits vars width clauses accumulator : List Bool) : StructuredProgram.State 5 8 :=
  (StructuredProgram.Atom.peek 0 0 1).eval (state false false bits vars width clauses [] [] [] accumulator)

def peekCommand : StructuredCalls.Cmd 5 8 := .base (.atom (.peek 0 0 1))

theorem peek_eval (bits vars width clauses accumulator : List Bool) :
    Eval peekCommand 1 (state false false bits vars width clauses [] [] [] accumulator)
      (observed bits vars width clauses accumulator) := .base (.atom _ _)

theorem observed_present (bits vars width clauses accumulator : List Bool) (hb : bits ≠ []) :
    (observed bits vars width clauses accumulator).regs 1 = true := by
  cases bits with
  | nil => exact False.elim (hb rfl)
  | cons b bs => rfl

theorem observed_empty (vars width clauses accumulator : List Bool) :
    observed [] vars width clauses accumulator = state false false [] vars width clauses [] [] [] accumulator := by
  have hr : readRegs (regs false false) 0 1 none = regs false false := by
    funext i; fin_cases i <;> simp [readRegs, RawLiteralEmitter.regs]
  simpa [observed, state, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, hr]

def clearPeek : StructuredCalls.Cmd 5 8 := .base
  (.seq (.atom (.set 0 false)) (.atom (.set 1 false)))

theorem clear_peek_eval (bits vars width clauses accumulator : List Bool) :
    Eval clearPeek 2 (observed bits vars width clauses accumulator)
      (state false false bits vars width clauses [] [] [] accumulator) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 5) false)
    (observed bits vars width clauses accumulator)).seq
      (StructuredProgram.Eval.atom (.set (1 : Fin 5) false) _)
  have hr : Function.update (Function.update (readRegs (regs false false) 0 1 bits.head?)
      0 false) 1 false = regs false false := by
    funext i; fin_cases i <;> simp [readRegs, RawLiteralEmitter.regs]
  apply Eval.base
  simpa [clearPeek, observed, state, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, hr] using h

noncomputable def iteration : StructuredCalls.Cmd 5 8 :=
  .seq clearPeek (.seq RawClauseParser.command peekCommand)

noncomputable def loop : StructuredCalls.Cmd 5 8 := .while 1 iteration

/-- The loop tests actual stack presence, including before an empty clause.
Each nonempty input begins with two arity cells, so progress is physical. -/
theorem loop_eval {v : ℕ} (F : PrefixCNF.Formula v) (hw : PrefixCNF.Width 3 F)
    (vars clauses accumulator : List Bool) :
    ∃ steps, steps ≤ loopBound F ∧
      Eval loop steps (observed (input F) vars (Encoding.encodeNat v.size) clauses accumulator)
        (observed [] vars (Encoding.encodeNat v.size) clauses ((output F).reverse ++ accumulator)) := by
  induction F generalizing accumulator with
  | nil => exact ⟨1, by simp [loopBound], .while_false rfl⟩
  | cons c F ih =>
    have hc := hw c (by simp)
    have ht : PrefixCNF.Width 3 F := fun d hd => hw d (by simp [hd])
    have hclear := clear_peek_eval (input (c :: F)) vars (Encoding.encodeNat v.size) clauses accumulator
    obtain ⟨k, hk, hclause⟩ := RawClauseParser.clause_eval c hc (input F) vars clauses accumulator
    have hclause' : Eval RawClauseParser.command k
        (state false false (input (c :: F)) vars (Encoding.encodeNat v.size) clauses [] [] [] accumulator)
        (state false false (input F) vars (Encoding.encodeNat v.size) clauses [] [] []
          ((RawClauseParser.rawClause c).reverse ++ accumulator)) := by
      simpa only [input_cons] using hclause
    have hpeek := peek_eval (input F) vars (Encoding.encodeNat v.size) clauses
      ((RawClauseParser.rawClause c).reverse ++ accumulator)
    have hiter : Eval iteration (2 + (k + 1))
        (observed (input (c :: F)) vars (Encoding.encodeNat v.size) clauses accumulator)
        (observed (input F) vars (Encoding.encodeNat v.size) clauses
          ((RawClauseParser.rawClause c).reverse ++ accumulator)) := hclear.seq (hclause'.seq hpeek)
    obtain ⟨j, hj, hrest⟩ := ih ht ((RawClauseParser.rawClause c).reverse ++ accumulator)
    have hall := Eval.while_true
      (observed_present (input (c :: F)) vars (Encoding.encodeNat v.size) clauses accumulator
        (input_cons_ne_nil c F)) hiter hrest
    refine ⟨(2 + (k + 1)) + j + 1, ?_, ?_⟩
    · simp only [loopBound, List.map_cons, List.sum_cons] at hj ⊢
      omega
    · simpa only [loop, output, List.flatMap_cons, List.reverse_append, List.append_assoc] using hall

noncomputable def command : StructuredCalls.Cmd 5 8 := .seq peekCommand loop

/-- Actual whole-body evaluation. Input is exhausted; all other parser metadata
is retained; the accumulator receives exactly the reversed raw body. -/
theorem body_eval {v : ℕ} (F : PrefixCNF.Formula v) (hw : PrefixCNF.Width 3 F)
    (vars clauses accumulator : List Bool) :
    ∃ steps, steps ≤ 1 + loopBound F ∧
      Eval command steps
        (state false false (input F) vars (Encoding.encodeNat v.size) clauses [] [] [] accumulator)
        (state false false [] vars (Encoding.encodeNat v.size) clauses [] [] []
          ((output F).reverse ++ accumulator)) := by
  obtain ⟨k, hk, he⟩ := loop_eval F hw vars clauses accumulator
  have h := (peek_eval (input F) vars (Encoding.encodeNat v.size) clauses accumulator).seq he
  rw [observed_empty] at h
  exact ⟨1 + k, by omega, h⟩

noncomputable abbrev program := compiled command 0 7

theorem source_body {v : ℕ} (F : PrefixCNF.Formula v) (hw : PrefixCNF.Width 3 F)
    (vars clauses accumulator : List Bool) :
    BitProgram.RunsIn program (2 + loopBound F)
      ((state false false (input F) vars (Encoding.encodeNat v.size) clauses [] [] [] accumulator).withPC
        (some program.entry))
      ((state false false [] vars (Encoding.encodeNat v.size) clauses [] [] []
        ((output F).reverse ++ accumulator)).withPC none) := by
  obtain ⟨k, hk, he⟩ := body_eval F hw vars clauses accumulator
  exact ⟨k + 1, by omega, compiled_halt_trace he 0 7⟩

end QecReliability.ExternalSATBridge.RawBodyParser
