import ExternalSATLinkedCompleted

/-! Explicit polynomial frontend overhead on the same completed native linked
run. The engine's actual transition count and visited interval are retained
separately. No engine existence, SAT correctness, or engine-space estimate is
introduced by this corollary. -/
namespace QecReliability.ExternalSATBridge.PrimitiveLink

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open Computation SqrtLogSpace

theorem query_then_engine_polynomial (M : PrimitiveMachine) (q : SATRequest)
    {nm : ℕ} {m : LocatedCfg M} {answer : Bool}
    (hm : Trace (locatedStep M) nm
      (locatedInit M (Encoding.encodeCNF (FormulaBridge.formula q.formula))) m)
    (hmh : m.config.state = .inl answer) :
    ∃ run : MultiTape.Completed (PrimitiveTransport.machine (queryMachine M)) (QueryCodec.encode q),
      run.output = answer ∧
      run.time ≤ 4194304 * (RawQueryBounds.extent q + 1) ^ 5 + nm ∧
      run.cells ≤ 268435456 * (RawQueryBounds.extent q + 1) ^ 5 + visitedSpace m := by
  obtain ⟨run, ho, ht, hs⟩ := query_then_engine_completed M q hm hmh
  have htime := CanonicalQueryBounds.timeBound_le q
  have hone := TraversalBudgetHierarchy.one_le_power (RawQueryBounds.extent q) 5
  have hlinear := TraversalBudgetHierarchy.base_le_power (RawQueryBounds.extent q) 4
  change RawQueryBounds.extent q + 1 ≤ (RawQueryBounds.extent q + 1) ^ 5 at hlinear
  have hbits : (QueryCodec.encode q).length ≤ RawQueryBounds.extent q := by
    simp only [RawQueryBounds.extent]
    omega
  exact ⟨run, ho, by omega, by omega⟩

end QecReliability.ExternalSATBridge.PrimitiveLink
