import ExternalSATFrameEmitter

/-! Actual outer-list terminator and final physical reversal. The input is a
real reversed accumulator, not a semantic list supplied to the machine. -/
namespace QecReliability.ExternalSATBridge.CanonicalFinalize

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls

def store (outer : List Bool) : StructuredProgram.State 2 3 :=
  ⟨(fun _ => false), ![outer, [], []]⟩

def terminate : StructuredCalls.Cmd 2 3 :=
  .base (.seq (.atom (.set 0 false)) (.atom (.push 0 0)))

abbrev reverseProgram : Program 2 3 10 := StackRoutines.reverseProgram 0 1 2 0 1

theorem terminate_eval (outer : List Bool) :
    Eval terminate 2 (store outer) (store (false :: outer)) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 2) false) (store outer)).seq
    (StructuredProgram.Eval.atom (.push (0 : Fin 3) 0) _)
  have hr : Function.update (fun _ : Fin 2 => false) 0 false = (fun _ => false) := by
    funext i; fin_cases i <;> simp
  have hs : Function.update (![outer, [], []] : Fin 3 → List Bool) 0 (false :: outer) =
      ![false :: outer, [], []] := by
    funext i; fin_cases i <;> simp
  apply Eval.base
  simpa [terminate, store, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, hr, hs,
    funext_iff, Fin.forall_fin_succ] using h

theorem reverse_trace (outer : List Bool) :
    Trace reverseProgram (9 * outer.length + 7)
      ((store outer).withPC (some reverseProgram.entry))
      ((store outer.reverse).withPC none) := by
  have ht := StackRoutines.reverseProgram_trace (0 : Fin 3) 1 2 (0 : Fin 2) 1
    (by decide) (by decide) (by decide) (by decide)
    (fun _ => false) (![outer, [], []] : Fin 3 → List Bool) rfl rfl
  have hh := StackRoutines.halt_after_trace reverseProgram ht 9 rfl rfl
  have hr : readRegs (fun _ : Fin 2 => false) 0 1 none = (fun _ => false) := by
    funext i; fin_cases i <;> simp [readRegs]
  have hs : StackRoutines.reverseStacks (0 : Fin 3)
      (![outer, [], []] : Fin 3 → List Bool) = ![outer.reverse, [], []] := by
    funext i; fin_cases i <;> simp [StackRoutines.reverseStacks]
  simpa only [StackRoutines.reverseResult, hr, hs, store, StructuredProgram.State.withPC,
    Nat.add_assoc, show (![outer, [], []] : Fin 3 → List Bool) 0 = outer from rfl,
    show (6 : ℕ) + 1 = 7 from rfl] using hh

def command : StructuredCalls.Cmd 2 3 := .seq terminate (.call reverseProgram)
noncomputable abbrev program := compiled command 0 0

theorem eval_finalize (outer : List Bool) :
    Eval command (9 * outer.length + 18) (store outer) (store (outer.reverse ++ [false])) := by
  have h := (terminate_eval outer).seq
    (Eval.call reverseProgram (reverse_trace (false :: outer)))
  have hn : 2 + (9 * (false :: outer).length + 7) = 9 * outer.length + 18 := by
    simp only [List.length_cons]; omega
  simpa only [command, hn, List.reverse_cons] using h

theorem source_finalize (outer : List Bool) :
    BitProgram.RunsIn program (9 * outer.length + 19)
      ((store outer).withPC (some program.entry))
      ((store (outer.reverse ++ [false])).withPC none) := by
  have h := compiled_halt_trace (eval_finalize outer) 0 0
  refine ⟨9 * outer.length + 18 + 1, by omega, h⟩

/-- Forward-byte specialization; the trailing false is precisely the outer
encodeList terminator, not another literal or frame terminator. -/
theorem source_forward (bytes : List Bool) :
    BitProgram.RunsIn program (9 * bytes.length + 19)
      ((store bytes.reverse).withPC (some program.entry))
      ((store (bytes ++ [false])).withPC none) := by
  simpa only [List.length_reverse, List.reverse_reverse] using source_finalize bytes.reverse

end QecReliability.ExternalSATBridge.CanonicalFinalize
