import ExternalSATRawLiteralEmitter

/-! Final physical reversal for the raw-body output accumulator. This uses the
actual ten-label reverse program and two real empty scratch stacks. It does not
perform canonical CNF normalization or assert a complete query parser. -/
namespace QecReliability.ExternalSATBridge.RawOutputReverse

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls
open RawLiteralEmitter (regs state)

abbrev program : Program 5 8 10 := StackRoutines.reverseProgram 7 4 6 0 1

/-- Includes the halt at label9 after the library trace-to-exit. All metadata,
input and cleared scratch stacks are retained exactly. -/
theorem reverse_trace (input vars width clauses accumulator : List Bool) :
    Trace program (9 * accumulator.length + 7)
      ((state false false input vars width clauses [] [] [] accumulator).withPC (some program.entry))
      ((state false false input vars width clauses [] [] [] accumulator.reverse).withPC none) := by
  have ht := StackRoutines.reverseProgram_trace (7 : Fin 8) 4 6 (0 : Fin 5) 1
    (by decide) (by decide) (by decide) (by decide) (regs false false)
    (![input, vars, width, clauses, [], [], [], accumulator] : Fin 8 → List Bool) rfl rfl
  have hh := StackRoutines.halt_after_trace program ht 9 rfl rfl
  have hregs : readRegs (regs false false) 0 1 none = regs false false := by
    funext i
    fin_cases i <;> simp [readRegs, RawLiteralEmitter.regs]
  have hstacks : StackRoutines.reverseStacks (7 : Fin 8)
      (![input, vars, width, clauses, [], [], [], accumulator] : Fin 8 → List Bool) =
      ![input, vars, width, clauses, [], [], [], accumulator.reverse] := by
    funext i
    fin_cases i <;> simp [StackRoutines.reverseStacks]
  simpa only [StackRoutines.reverseResult, hregs, hstacks, state,
    StructuredProgram.State.withPC, Nat.add_assoc,
    show (![input, vars, width, clauses, [], [], [], accumulator] : Fin 8 → List Bool) 7 = accumulator from rfl,
    show (6 : ℕ) + 1 = 7 from rfl] using hh

/-- A caller may use this exact measured evaluation directly, without compiling
an extra wrapper or silently dropping the reverse program's halt transition. -/
theorem eval_reverse (input vars width clauses accumulator : List Bool) :
    StructuredCalls.Eval (.call program) (9 * accumulator.length + 7)
      (state false false input vars width clauses [] [] [] accumulator)
      (state false false input vars width clauses [] [] [] accumulator.reverse) :=
  .call program (reverse_trace input vars width clauses accumulator)

noncomputable abbrev primitive := GuardedCompiler.primitive program

theorem primitive_reverse (input vars width clauses accumulator : List Bool) :
    Computation.RunsIn primitive.step (7 * (9 * accumulator.length + 7))
      (GuardedCompiler.primitiveCfg program
        ((state false false input vars width clauses [] [] [] accumulator).withPC (some program.entry)))
      (GuardedCompiler.primitiveCfg program
        ((state false false input vars width clauses [] [] [] accumulator.reverse).withPC none)) :=
  GuardedCompiler.primitive_execution program ⟨_, le_rfl, reverse_trace input vars width clauses accumulator⟩

end QecReliability.ExternalSATBridge.RawOutputReverse
