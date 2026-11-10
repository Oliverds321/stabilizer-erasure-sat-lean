import ExternalSATQueryCanonicalController

/-! Observed native execution for the complete canonical-query controller.
Space is bounded from its ACTUAL trace and visited-cell growth, not inferred from
output length. The final Boolean is the canonical word's head, not a SAT answer. -/
namespace QecReliability.ExternalSATBridge.QueryCanonicalCompleted

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open PrimitiveTransport

noncomputable abbrev sourceMachine := QueryCanonicalController.primitive

@[simp] theorem source_tapeCount : sourceMachine.tapeCount = 20 := rfl

def outputIndex : Fin sourceMachine.tapeCount := ⟨5, by rw [source_tapeCount]; decide⟩

theorem primitive_run (q : SATRequest) :
    ∃ steps final,
      Computation.Trace sourceMachine.step steps (sourceMachine.init (QueryCodec.encode q)) final ∧
      steps ≤ 7 * QueryCanonicalController.timeBound q ∧
      final.state = .inl ((Encoding.encodeCNF (FormulaBridge.formula q.formula)).head?.getD false) ∧
      final.tapes outputIndex = Turing.Tape.mk₁ ((Encoding.encodeCNF (FormulaBridge.formula q.formula)).map some) := by
  obtain ⟨final, ⟨steps, hs, ht⟩, hh, ho⟩ := GuardedCompiler.primitive_word_execution
    QueryCanonicalController.program (QueryCanonicalController.source_query q) rfl
    (show (QueryCanonicalController.ready q).stacks QueryCanonicalController.program.outputStack =
      Encoding.encodeCNF (FormulaBridge.formula q.formula) from rfl)
  refine ⟨steps, final, ht, hs, hh, ?_⟩
  have hi : (QueryCanonicalController.program.outputStack : Fin sourceMachine.tapeCount) = outputIndex := by
    apply Fin.ext
    rfl
  simpa only [hi] using ho

/-- Twenty-one actual native tapes: twenty source tapes plus the idle adapter tape.
The source output index5 maps to native slot6; visited cells and final halt
inspection are charged on the very same successful observed execution. -/
theorem completed_query (q : SATRequest) :
    ∃ run : MultiTape.Completed (machine sourceMachine) (QueryCodec.encode q),
      run.time ≤ 7 * QueryCanonicalController.timeBound q + 1 ∧
      run.cells ≤ (QueryCodec.encode q).length + 21 + 21 * (7 * QueryCanonicalController.timeBound q) ∧
      run.final.core.tapes (slot sourceMachine outputIndex) =
        Turing.Tape.mk₁ ((Encoding.encodeCNF (FormulaBridge.formula q.formula)).map some) ∧
      run.output = (Encoding.encodeCNF (FormulaBridge.formula q.formula)).head?.getD false := by
  obtain ⟨steps, final, htrace, hsteps, hhalt, hout⟩ := primitive_run q
  obtain ⟨located, hlocated, hconfig⟩ := locatedTrace_lift
    (c := locatedInit sourceMachine (QueryCodec.encode q)) htrace
  obtain ⟨s, hs, hrel⟩ := lift_observedTrace sourceMachine hlocated
    (MultiTape.initialObserved (machine sourceMachine) (QueryCodec.encode q))
    (related_initial sourceMachine (QueryCodec.encode q))
  have hproj : project sourceMachine s.core = final := hrel.core.trans hconfig
  have hstate : s.core.label = .inl ((Encoding.encodeCNF (FormulaBridge.formula q.formula)).head?.getD false) :=
    (congrArg Computation.PrimitiveMachine.Cfg.state hproj).trans hhalt
  let run : MultiTape.Completed (machine sourceMachine) (QueryCodec.encode q) :=
    ⟨steps, s, _, hs, answer_of_halting_label sourceMachine s.core _ hstate⟩
  have hspace := observed_trace_cells hs
  have hinitial := initial_cells_le sourceMachine (QueryCodec.encode q)
  have htapes := congrArg (fun c : sourceMachine.Cfg => c.tapes outputIndex) hproj
  refine ⟨run, ?_, ?_, htapes.trans hout, rfl⟩
  · change steps + 1 ≤ _
    omega
  · change MultiTape.visitedCells s ≤ _
    change MultiTape.visitedCells s ≤
      MultiTape.visitedCells (MultiTape.initialObserved (machine sourceMachine) (QueryCodec.encode q)) +
        steps * 21 at hspace
    have hi : MultiTape.visitedCells (MultiTape.initialObserved (machine sourceMachine)
        (QueryCodec.encode q)) ≤ (QueryCodec.encode q).length + 21 := by
      simpa only [source_tapeCount] using hinitial
    omega

end QecReliability.ExternalSATBridge.QueryCanonicalCompleted
