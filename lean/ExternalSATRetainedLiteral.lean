import ExternalSATQueryPreparation
import ExternalSATCountedLiteral

/-! One repeated-use literal parser in the query controller's real seven-stack
layout. It copies the retained width, consumes one native literal, and preserves
both header words and the width for the next literal. -/
namespace QecReliability.ExternalSATBridge.RetainedLiteral

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls
open QueryPreparation (store)

def copyPorts : Fin 5 → Fin 7 := ![0, 2, 4, 5, 6]
def literalPorts : Fin 4 → Fin 7 := ![0, 4, 5, 6]

theorem copyPorts_injective : Function.Injective copyPorts := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [copyPorts]
theorem literalPorts_injective : Function.Injective literalPorts := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [literalPorts]

theorem copy_embed (vars clauses a b c d e : List Bool) :
    embedState (id : Fin 3 → Fin 3) copyPorts (store [] vars [] clauses [] [] [])
      (WidthPreparation.store a b c d e) = store a vars b clauses c d e := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ Function.injective_id copyPorts_injective
  · intro i; rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; rfl
  · intro i hi
    fin_cases i <;> simp_all [QueryPreparation.store, copyPorts, Fin.exists_fin_succ]

theorem literal_embed (vars width clauses a b c d : List Bool) :
    embedState (id : Fin 3 → Fin 3) literalPorts (store [] vars width clauses [] [] [])
      (HeaderToUnary.store a b c d) = store a vars width clauses b c d := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ Function.injective_id literalPorts_injective
  · intro i; rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; rfl
  · intro i hi
    fin_cases i <;> simp_all [QueryPreparation.store, literalPorts, Fin.exists_fin_succ]

noncomputable def command : StructuredCalls.Cmd 3 7 :=
  .seq (.call (ProgramLinking.liftProgram WidthPreparation.copyProgram id copyPorts))
    (.call (ProgramLinking.liftProgram LiteralToUnary.program id literalPorts))

noncomputable abbrev program := compiled command 0 5

def timeBound (k value : ℕ) : ℕ := 14 * k + 12 + 32 * (value + 1) * (k + 1)

theorem eval_word (bits width tail vars clauses : List Bool) (hw : width.length = bits.length) :
    ∃ steps, steps + 1 ≤ timeBound bits.length (CounterPrograms.value bits) ∧
      StructuredCalls.Eval command steps (store (bits ++ tail) vars width clauses [] [] [])
        (store tail vars width clauses [] (Encoding.encodeNat (CounterPrograms.value bits)) []) := by
  have ec := eval_call_lifted WidthPreparation.copyProgram (id : Fin 3 → Fin 3) copyPorts
    (store [] vars [] clauses [] [] []) Function.injective_id copyPorts_injective
    (WidthPreparation.copy_trace (bits ++ tail) width)
  rw [copy_embed, copy_embed] at ec
  obtain ⟨k, hk, ht⟩ := CountedLiteral.source_word bits width tail hw
  have el := eval_call_lifted LiteralToUnary.program (id : Fin 3 → Fin 3) literalPorts
    (store [] vars width clauses [] [] []) Function.injective_id literalPorts_injective ht
  rw [literal_embed, literal_embed] at el
  refine ⟨7 * width.length + 5 + k, ?_, ec.seq el⟩
  simp only [hw, CounterConversions.runtimeBound] at hk ⊢
  dsimp only [timeBound]
  omega

theorem source_word (bits width tail vars clauses : List Bool) (hw : width.length = bits.length) :
    BitProgram.RunsIn program (timeBound bits.length (CounterPrograms.value bits))
      ((store (bits ++ tail) vars width clauses [] [] []).withPC (some program.entry))
      ((store tail vars width clauses [] (Encoding.encodeNat (CounterPrograms.value bits)) []).withPC none) := by
  obtain ⟨steps, hs, he⟩ := eval_word bits width tail vars clauses hw
  exact ⟨steps + 1, hs, compiled_halt_trace he 0 5⟩

/-- The retained width is genuinely reused, not supplied anew from v at each
invocation. Its equality to encodeNat(v.size) is a caller-state invariant. -/
theorem source_literal {v : ℕ} (l : PrefixCNF.Literal v) (tail vars clauses : List Bool) :
    BitProgram.RunsIn program
      (timeBound (v.size + 1) (Encoding.literalCode (⟨l.1, l.2⟩ : SAT.Literal (Fin v))))
      ((store (QueryCodec.literal v.size (l.1.val, l.2) ++ tail) vars
        (Encoding.encodeNat v.size) clauses [] [] []).withPC (some program.entry))
      ((store tail vars (Encoding.encodeNat v.size) clauses []
        (Encoding.encodeNat (Encoding.literalCode (⟨l.1, l.2⟩ : SAT.Literal (Fin v)))) []).withPC none) := by
  have hv := LiteralToUnary.literal_value v.size l.1.val l.2 (l.1.isLt.trans (Nat.lt_size_self v))
  have hw : (Encoding.encodeNat v.size).length = (l.2 :: QueryCodec.word v.size l.1.val).length := by simp
  simpa [QueryCodec.literal, hv, Encoding.literalCode] using
    source_word (l.2 :: QueryCodec.word v.size l.1.val) (Encoding.encodeNat v.size) tail vars clauses hw

noncomputable abbrev primitive := GuardedCompiler.primitive program

theorem primitive_word (bits width tail vars clauses : List Bool) (hw : width.length = bits.length) :
    Computation.RunsIn primitive.step (7 * timeBound bits.length (CounterPrograms.value bits))
      (GuardedCompiler.primitiveCfg program
        ((store (bits ++ tail) vars width clauses [] [] []).withPC (some program.entry)))
      (GuardedCompiler.primitiveCfg program
        ((store tail vars width clauses [] (Encoding.encodeNat (CounterPrograms.value bits)) []).withPC none)) :=
  GuardedCompiler.primitive_execution program (source_word bits width tail vars clauses hw)

end QecReliability.ExternalSATBridge.RetainedLiteral
