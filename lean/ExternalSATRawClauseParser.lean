import ExternalSATRawLiteralEmitter

/-! Fixed-width-three clause dispatch for the complete query frontend.
The intermediate output is explicitly NONcanonical: original two-bit arity,
followed by original-order unary literal codes, retaining duplicates. -/
namespace QecReliability.ExternalSATBridge.RawClauseParser

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls
open RawLiteralEmitter (state)

def input {v : ℕ} (c : List (PrefixCNF.Literal v)) : List Bool :=
  QueryCodec.literals v.size (c.map (fun l => (l.1.val, l.2)))

def fields {v : ℕ} (c : List (PrefixCNF.Literal v)) : List Bool :=
  c.flatMap (fun l => Encoding.encodeNat (Encoding.literalCode (⟨l.1, l.2⟩ : SAT.Literal (Fin v))))

def rawClause {v : ℕ} (c : List (PrefixCNF.Literal v)) : List Bool :=
  QueryCodec.word 2 c.length ++ fields c

def literalCost {v : ℕ} (l : PrefixCNF.Literal v) : ℕ :=
  RawLiteralEmitter.timeBound (v.size + 1) (Encoding.literalCode (⟨l.1, l.2⟩ : SAT.Literal (Fin v)))

def fieldCost {v : ℕ} (c : List (PrefixCNF.Literal v)) : ℕ := (c.map literalCost).sum

/-- Only the four fixed instances0,1,2,3 occur in the final instruction table.
This proof helper does not construct an input-dependent runtime controller. -/
noncomputable def repeatLiterals : ℕ → StructuredCalls.Cmd 5 8
  | 0 => .base .skip
  | n + 1 => .seq RawLiteralEmitter.command (repeatLiterals n)

theorem repeat_eval {v : ℕ} (c : List (PrefixCNF.Literal v))
    (tail vars clauses accumulator : List Bool) (low high : Bool) :
    ∃ steps, steps ≤ fieldCost c ∧
      StructuredCalls.Eval (repeatLiterals c.length) steps
        (state low high (input c ++ tail) vars (Encoding.encodeNat v.size) clauses [] [] [] accumulator)
        (state low high tail vars (Encoding.encodeNat v.size) clauses [] [] []
          ((fields c).reverse ++ accumulator)) := by
  induction c generalizing accumulator with
  | nil => exact ⟨0, by simp [fieldCost], .base (.skip _)⟩
  | cons l ls ih =>
    obtain ⟨k, hk, he⟩ := RawLiteralEmitter.eval_literal l (input ls ++ tail)
      vars clauses accumulator low high
    obtain ⟨j, hj, ht⟩ := ih
      ((Encoding.encodeNat (Encoding.literalCode (⟨l.1, l.2⟩ : SAT.Literal (Fin v)))).reverse ++ accumulator)
    refine ⟨k + j, ?_, ?_⟩
    · simpa only [fieldCost, literalCost, List.map_cons, List.sum_cons] using Nat.add_le_add hk hj
    · simpa only [repeatLiterals, List.length_cons, input, QueryCodec.literals,
        List.map_cons, List.flatMap_cons, fields, List.reverse_append, List.append_assoc] using he.seq ht

/-- Pop two arity bits into actual registers3/4, emit those bits to the reversed
accumulator, then clear the transient presence bit before the literal calls. -/
def prefixCommand : StructuredCalls.Cmd 5 8 := .base
  (.seq (.atom (.pop 0 3 0))
    (.seq (.atom (.push 7 3))
      (.seq (.atom (.pop 0 4 0))
        (.seq (.atom (.push 7 4)) (.atom (.set 0 false))))))

theorem prefix_eval (low high : Bool) (tail vars width clauses accumulator : List Bool) :
    StructuredCalls.Eval prefixCommand 5
      (state false false (low :: high :: tail) vars width clauses [] [] [] accumulator)
      (state low high tail vars width clauses [] [] [] (high :: low :: accumulator)) := by
  let d := state false false (low :: high :: tail) vars width clauses [] [] [] accumulator
  have h := (StructuredProgram.Eval.atom (.pop (0 : Fin 8) (3 : Fin 5) 0) d).seq
    ((StructuredProgram.Eval.atom (.push (7 : Fin 8) (3 : Fin 5)) _).seq
      ((StructuredProgram.Eval.atom (.pop (0 : Fin 8) (4 : Fin 5) 0) _).seq
        ((StructuredProgram.Eval.atom (.push (7 : Fin 8) (4 : Fin 5)) _).seq
          (StructuredProgram.Eval.atom (.set (0 : Fin 5) false) _))))
  have hregs : Function.update
      (Function.update (Function.update (Function.update
        (![false, false, false, false, false] : Fin 5 → Bool) 3 low) 0 true) 4 high) 0 false =
        ![false, false, false, low, high] := by
    funext i; fin_cases i <;> simp
  have hstacks : Function.update
      (Function.update (Function.update (Function.update
        (![low :: high :: tail, vars, width, clauses, [], [], [], accumulator] : Fin 8 → List Bool)
          0 (high :: tail)) 7 (low :: accumulator)) 0 tail) 7 (high :: low :: accumulator) =
        ![tail, vars, width, clauses, [], [], [], high :: low :: accumulator] := by
    funext i; fin_cases i <;> simp
  apply StructuredCalls.Eval.base
  simpa [hregs, hstacks, prefixCommand, d, state, RawLiteralEmitter.regs, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, StructuredProgram.State.withPC,
    execInstr, readRegs, funext_iff, Fin.forall_fin_succ] using h

def lowBit (n : ℕ) : Bool := decide (n % 2 = 1)
def highBit (n : ℕ) : Bool := decide (n / 2 % 2 = 1)

noncomputable def dispatch : StructuredCalls.Cmd 5 8 :=
  .ite 4 (.ite 3 (repeatLiterals 3) (repeatLiterals 2))
    (.ite 3 (repeatLiterals 1) (repeatLiterals 0))

theorem dispatch_eval {v : ℕ} (c : List (PrefixCNF.Literal v)) (hc : c.length ≤ 3)
    (tail vars clauses accumulator : List Bool) :
    ∃ steps, steps ≤ fieldCost c + 2 ∧
      StructuredCalls.Eval dispatch steps
        (state (lowBit c.length) (highBit c.length) (input c ++ tail)
          vars (Encoding.encodeNat v.size) clauses [] [] [] accumulator)
        (state (lowBit c.length) (highBit c.length) tail
          vars (Encoding.encodeNat v.size) clauses [] [] [] ((fields c).reverse ++ accumulator)) := by
  obtain ⟨k, hk, he⟩ := repeat_eval c tail vars clauses accumulator (lowBit c.length) (highBit c.length)
  refine ⟨k + 2, by omega, ?_⟩
  have hlen : c.length = 0 ∨ c.length = 1 ∨ c.length = 2 ∨ c.length = 3 := by omega
  rcases hlen with h | h | h | h
  · simp only [h] at he ⊢
    exact .ite_false rfl (.ite_false rfl he)
  · simp only [h] at he ⊢
    exact .ite_false rfl (.ite_true rfl he)
  · simp only [h] at he ⊢
    exact .ite_true rfl (.ite_false rfl he)
  · simp only [h] at he ⊢
    exact .ite_true rfl (.ite_true rfl he)

def cleanup : StructuredCalls.Cmd 5 8 :=
  .base (.seq (.atom (.set 3 false)) (.atom (.set 4 false)))

theorem cleanup_eval (low high : Bool) (tail vars width clauses accumulator : List Bool) :
    StructuredCalls.Eval cleanup 2
      (state low high tail vars width clauses [] [] [] accumulator)
      (state false false tail vars width clauses [] [] [] accumulator) := by
  have h := (StructuredProgram.Eval.atom (.set (3 : Fin 5) false)
    (state low high tail vars width clauses [] [] [] accumulator)).seq
      (StructuredProgram.Eval.atom (.set (4 : Fin 5) false) _)
  have hregs : Function.update (Function.update
      (![false, false, false, low, high] : Fin 5 → Bool) 3 false) 4 false =
        ![false, false, false, false, false] := by
    funext i; fin_cases i <;> simp
  apply StructuredCalls.Eval.base
  simpa [hregs, cleanup, state, RawLiteralEmitter.regs, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, StructuredProgram.State.withPC,
    execInstr, funext_iff, Fin.forall_fin_succ] using h

noncomputable def command : StructuredCalls.Cmd 5 8 := .seq prefixCommand (.seq dispatch cleanup)

/-- Every valid native width-three clause is consumed by the SAME finite table,
with exact raw unary output and retained suffix/header/width invariants. -/
theorem clause_eval {v : ℕ} (c : List (PrefixCNF.Literal v)) (hc : c.length ≤ 3)
    (tail vars clauses accumulator : List Bool) :
    ∃ steps, steps ≤ 9 + fieldCost c ∧
      StructuredCalls.Eval command steps
        (state false false
          (QueryCodec.clause v.size (c.map (fun l => (l.1.val, l.2))) ++ tail)
          vars (Encoding.encodeNat v.size) clauses [] [] [] accumulator)
        (state false false tail vars (Encoding.encodeNat v.size) clauses [] [] []
          ((rawClause c).reverse ++ accumulator)) := by
  have hp := prefix_eval (lowBit c.length) (highBit c.length) (input c ++ tail)
    vars (Encoding.encodeNat v.size) clauses accumulator
  obtain ⟨k, hk, hd⟩ := dispatch_eval c hc tail vars clauses
    (highBit c.length :: lowBit c.length :: accumulator)
  have he := cleanup_eval (lowBit c.length) (highBit c.length) tail vars
    (Encoding.encodeNat v.size) clauses
    ((fields c).reverse ++ highBit c.length :: lowBit c.length :: accumulator)
  refine ⟨5 + (k + 2), by omega, ?_⟩
  simpa only [command, QueryCodec.clause, List.length_map, QueryCodec.word,
    List.nil_append, lowBit, highBit, input, rawClause, List.reverse_cons,
    List.reverse_nil, List.reverse_append, List.append_assoc, List.cons_append] using hp.seq (hd.seq he)

noncomputable abbrev program := compiled command 0 7

theorem source_clause {v : ℕ} (c : List (PrefixCNF.Literal v)) (hc : c.length ≤ 3)
    (tail vars clauses accumulator : List Bool) :
    BitProgram.RunsIn program (10 + fieldCost c)
      ((state false false (QueryCodec.clause v.size (c.map (fun l => (l.1.val, l.2))) ++ tail)
        vars (Encoding.encodeNat v.size) clauses [] [] [] accumulator).withPC (some program.entry))
      ((state false false tail vars (Encoding.encodeNat v.size) clauses [] [] []
        ((rawClause c).reverse ++ accumulator)).withPC none) := by
  obtain ⟨k, hk, he⟩ := clause_eval c hc tail vars clauses accumulator
  exact ⟨k + 1, by omega, compiled_halt_trace he 0 7⟩

end QecReliability.ExternalSATBridge.RawClauseParser
