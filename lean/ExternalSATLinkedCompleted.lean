import ExternalSATLocatedSpace

/-! One actual native completed run from the original query through the finite
frontend/engine link. The engine is explicit and its located run is a premise;
this module does not assert existence or correctness of a SAT solver. Time and
space refer to the same linked execution, including fresh/idle physical cells. -/
namespace QecReliability.ExternalSATBridge.PrimitiveLink

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open Computation SqrtLogSpace

variable (F M : PrimitiveMachine) (out : Fin F.tapeCount)

theorem sequential_located_trace (bits word : List Bool)
    {nf nm : ℕ} {f : LocatedCfg F} {m : LocatedCfg M} {marker answer : Bool}
    (hf : Trace (locatedStep F) nf (locatedInit F bits) f)
    (hfh : f.config.state = .inl marker)
    (hword : f.config.tapes out = Turing.Tape.mk₁ (word.map some))
    (hm : Trace (locatedStep M) nm (locatedInit M word) m)
    (hmh : m.config.state = .inl answer) :
    ∃ final : LocatedCfg (machine F M out),
      Trace (locatedStep (machine F M out)) (nf + nm)
        (locatedInit (machine F M out) bits) final ∧
      final.config.state = .inl answer ∧
      visitedSpace final ≤ visitedSpace f + visitedSpace m + 1 := by
  have hinit : ∀ i, (locatedInit F bits).lower i ≤ (locatedInit F bits).position i ∧
      (locatedInit F bits).position i ≤ (locatedInit F bits).upper i := by
    intro i
    simp only [locatedInit, Int.ofNat_eq_natCast]
    split_ifs <;> omega
  have hfront := front_located_trace F M out hf hinit
  rw [front_located_initial] at hfront
  have henc := locatedTrace_init_encloses hf
  obtain ⟨final, heng, hrel⟩ := engine_located_trace F M out hm _
    (handoff_located F M out hfh hword henc)
  refine ⟨final, hfront.trans heng, ?_,
    engine_located_space F M out hrel henc (locatedTrace_contains_origin hm)⟩
  exact hrel.core.1.trans (congrArg (engineState F M) hmh)

theorem sequential_completed (bits word : List Bool)
    {nf nm : ℕ} {f : LocatedCfg F} {m : LocatedCfg M} {marker answer : Bool}
    (hf : Trace (locatedStep F) nf (locatedInit F bits) f)
    (hfh : f.config.state = .inl marker)
    (hword : f.config.tapes out = Turing.Tape.mk₁ (word.map some))
    (hm : Trace (locatedStep M) nm (locatedInit M word) m)
    (hmh : m.config.state = .inl answer) :
    ∃ run : MultiTape.Completed (PrimitiveTransport.machine (machine F M out)) bits,
      run.output = answer ∧ run.time = nf + nm + 1 ∧
      run.cells ≤ visitedSpace f + visitedSpace m + 2 := by
  obtain ⟨final, htrace, hhalt, hspace⟩ :=
    sequential_located_trace F M out bits word hf hfh hword hm hmh
  obtain ⟨run, ho, ht, hs⟩ := PrimitiveTransport.completed_run
    (machine F M out) bits answer (nf + nm) final htrace hhalt
  exact ⟨run, ho, ht, by omega⟩

/-- The frontend is the accepted complete canonical encoder. Only its own
polynomial transition count is used to bound its visited interval; engine space
remains the actually measured engine interval, never its running time. -/
theorem query_then_engine_completed (M : PrimitiveMachine) (q : SATRequest)
    {nm : ℕ} {m : LocatedCfg M} {answer : Bool}
    (hm : Trace (locatedStep M) nm
      (locatedInit M (Encoding.encodeCNF (FormulaBridge.formula q.formula))) m)
    (hmh : m.config.state = .inl answer) :
    ∃ run : MultiTape.Completed (PrimitiveTransport.machine (queryMachine M)) (QueryCodec.encode q),
      run.output = answer ∧ run.time ≤ 7 * QueryCanonicalController.timeBound q + nm + 1 ∧
      run.cells ≤ 20 * ((QueryCodec.encode q).length +
        2 * (7 * QueryCanonicalController.timeBound q) + 1) + visitedSpace m + 2 := by
  obtain ⟨nf, final, hf, hnf, hfh, hword⟩ := QueryCanonicalCompleted.primitive_run q
  obtain ⟨f, hfl, hfc⟩ := locatedTrace_lift
    (c := locatedInit QueryCanonicalCompleted.sourceMachine (QueryCodec.encode q)) hf
  have hh : f.config.state =
      .inl ((Encoding.encodeCNF (FormulaBridge.formula q.formula)).head?.getD false) :=
    (congrArg PrimitiveMachine.Cfg.state hfc).trans hfh
  have hw : f.config.tapes QueryCanonicalCompleted.outputIndex =
      Turing.Tape.mk₁ ((Encoding.encodeCNF (FormulaBridge.formula q.formula)).map some) :=
    (congrArg (fun c : QueryCanonicalCompleted.sourceMachine.Cfg =>
      c.tapes QueryCanonicalCompleted.outputIndex) hfc).trans hword
  obtain ⟨run, ho, ht, hs⟩ := sequential_completed QueryCanonicalCompleted.sourceMachine M
    QueryCanonicalCompleted.outputIndex (QueryCodec.encode q)
    (Encoding.encodeCNF (FormulaBridge.formula q.formula)) hfl hh hw hm hmh
  have hfs := locatedTrace_space_le_of_length hfl
  change visitedSpace f ≤ 20 * ((QueryCodec.encode q).length + 2 * nf + 1) at hfs
  exact ⟨run, ho, by omega, by omega⟩

end QecReliability.ExternalSATBridge.PrimitiveLink
