import ExternalSATPreservingEquality

/-! Real nested-loop setup for streaming canonical candidates. Parent code and
remaining unary counter are retained; child code is incremented and the remaining
counter copied. No semantic natural is read by the fixed instruction table. -/
namespace QecReliability.ExternalSATBridge.CandidateChild

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls
open PreservingEquality (store zeroRegs copyLeft copyRight)

def increment : StructuredCalls.Cmd 5 6 := .base
  (.seq (.atom (.set 0 true)) (.seq (.atom (.push 2 0)) (.atom (.set 0 false))))

theorem increment_eval (parent remaining child counter : List Bool) :
    Eval increment 3 (store zeroRegs parent remaining child counter [] [])
      (store zeroRegs parent remaining (true :: child) counter [] []) := by
  apply Eval.base
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 5) true)
      (store zeroRegs parent remaining child counter [] [])).seq
    ((StructuredProgram.Eval.atom (.push (2 : Fin 6) (0 : Fin 5)) _).seq
      (StructuredProgram.Eval.atom (.set (0 : Fin 5) false) _))
  have hr : Function.update (Function.update zeroRegs 0 true) 0 false = zeroRegs := by
    funext i; fin_cases i <;> simp [zeroRegs]
  have ht : Function.update (![parent, remaining, child, counter, [], []] : Fin 6 → List Bool)
      2 (true :: child) = ![parent, remaining, true :: child, counter, [], []] := by
    funext i; fin_cases i <;> simp
  simpa only [store, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
    Function.update_same, hr,
    show (![parent, remaining, child, counter, [], []] : Fin 6 → List Bool) 2 = child from rfl,
    ht] using h

def command : StructuredCalls.Cmd 5 6 :=
  .seq (.call copyLeft) (.seq (.call copyRight) increment)

noncomputable abbrev program := compiled command 0 2

theorem eval_child (parent remaining : List Bool) :
    Eval command (7 * parent.length + 5 + (7 * remaining.length + 5 + 3))
      (store zeroRegs parent remaining [] [] [] [])
      (store zeroRegs parent remaining (true :: parent) remaining [] []) :=
  (PreservingEquality.copy_left_eval parent remaining).seq
    ((PreservingEquality.copy_right_eval parent remaining).seq
      (increment_eval parent remaining parent remaining))

/-- Source transition budget includes both copy halts and the caller halt.
Stacks0/1 are unchanged;2/3 are the child code/counter;4/5 remain empty. -/
theorem source_child (a r : ℕ) :
    BitProgram.RunsIn program (7 * a + 7 * r + 28)
      ((store zeroRegs (Encoding.encodeNat a) (Encoding.encodeNat r) [] [] [] []).withPC
        (some program.entry))
      ((store zeroRegs (Encoding.encodeNat a) (Encoding.encodeNat r)
        (Encoding.encodeNat (a + 1)) (Encoding.encodeNat r) [] []).withPC none) := by
  have h := compiled_halt_trace (eval_child (Encoding.encodeNat a) (Encoding.encodeNat r)) 0 2
  have hn : true :: Encoding.encodeNat a = Encoding.encodeNat (a + 1) := by
    simp [Encoding.encodeNat, List.replicate_succ]
  have hl (n : ℕ) : (Encoding.encodeNat n).length = n + 1 := by
    simp [Encoding.encodeNat]
  have hc : 7 * (a + 1) + 5 + (7 * (r + 1) + 5 + 3) + 1 =
      7 * a + 7 * r + 28 := by omega
  refine ⟨7 * a + 7 * r + 28, le_rfl, ?_⟩
  simpa only [hl, hc, hn] using h

noncomputable abbrev primitive := GuardedCompiler.primitive program

theorem primitive_child (a r : ℕ) :
    Computation.RunsIn primitive.step (7 * (7 * a + 7 * r + 28))
      (GuardedCompiler.primitiveCfg program
        ((store zeroRegs (Encoding.encodeNat a) (Encoding.encodeNat r) [] [] [] []).withPC
          (some program.entry)))
      (GuardedCompiler.primitiveCfg program
        ((store zeroRegs (Encoding.encodeNat a) (Encoding.encodeNat r)
          (Encoding.encodeNat (a + 1)) (Encoding.encodeNat r) [] []).withPC none)) :=
  GuardedCompiler.primitive_execution program (source_child a r)

end QecReliability.ExternalSATBridge.CandidateChild
