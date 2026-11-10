import ExternalSATCanonicalQueryBounds
import ExternalSATQueryCanonicalCompleted

/-! Measured complete canonical frontend, with one actual native observed run.
R is declared variable dimension plus binary query length. The output word is the
genuine external SAT encoding; the halt Boolean is only its head, NOT a SAT
answer. No external solver witness, counting theorem or engine contract is assumed.
-/
namespace QecReliability.ExternalSATBridge.CanonicalFrontend

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open PrimitiveTransport QueryCanonicalCompleted

/-- Twenty source tapes, twenty-one native tapes including the idle adapter.
Source output5 maps to native6. Time and visited-space bounds concern the SAME
completed physical run from the single actual binary input. -/
theorem completed_query (q : SATRequest) :
    ∃ run : MultiTape.Completed (machine sourceMachine) (QueryCodec.encode q),
      run.time ≤ 4194304 * (RawQueryBounds.extent q + 1) ^ 5 ∧
      run.cells ≤ 134217728 * (RawQueryBounds.extent q + 1) ^ 5 ∧
      run.final.core.tapes (slot sourceMachine outputIndex) =
        Turing.Tape.mk₁ ((Encoding.encodeCNF (FormulaBridge.formula q.formula)).map some) ∧
      run.output = (Encoding.encodeCNF (FormulaBridge.formula q.formula)).head?.getD false := by
  obtain ⟨run, ht, hs, ho, hb⟩ := QueryCanonicalCompleted.completed_query q
  have htime := CanonicalQueryBounds.timeBound_le q
  have hone := TraversalBudgetHierarchy.one_le_power (RawQueryBounds.extent q) 5
  have hlinear := TraversalBudgetHierarchy.base_le_power (RawQueryBounds.extent q) 4
  change RawQueryBounds.extent q + 1 ≤ (RawQueryBounds.extent q + 1) ^ 5 at hlinear
  have hbits : (QueryCodec.encode q).length ≤ RawQueryBounds.extent q := by
    simp only [RawQueryBounds.extent]
    omega
  exact ⟨run, by omega, by omega, ho, hb⟩

/-- Decision satisfiability is preserved by the actual formula written above.
This is a semantic equivalence, not a claim that the frontend decides SAT. -/
theorem satisfiability_preserved (q : SATRequest) :
    SAT.Satisfiable (FormulaBridge.formula q.formula) ↔
      ∃ a, PrefixCNF.eval q.formula a = true :=
  FormulaBridge.satisfiable_iff q.formula

end QecReliability.ExternalSATBridge.CanonicalFrontend
