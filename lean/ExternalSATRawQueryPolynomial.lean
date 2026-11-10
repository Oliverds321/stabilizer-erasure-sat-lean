import ExternalSATRawQueryBounds
import ExternalSATRawQueryCompleted

/-! Uniform dimension-aware resources for the actual raw-query frontend.
This is not canonical SAT input and its halt Boolean is not a SAT decision. -/
namespace QecReliability.ExternalSATBridge.RawQueryPolynomial

open QecReliability.OracleCost
open PrimitiveTransport RawQueryCompleted

/-- The same observed run carries the physical output and both cubic bounds.
Space comes from visited-cell growth of this run, not from its output length. -/
theorem completed_query (q : SATRequest) :
    ∃ run : MultiTape.Completed (machine sourceMachine) (QueryCodec.encode q),
      run.time ≤ 32768 * (RawQueryBounds.extent q + 1) ^ 3 ∧
      run.cells ≤ 524288 * (RawQueryBounds.extent q + 1) ^ 3 ∧
      run.final.core.tapes (slot sourceMachine outputIndex) =
        Turing.Tape.mk₁ ((RawBodyParser.output q.formula).map some) ∧
      run.output = (RawBodyParser.output q.formula).head?.getD false := by
  obtain ⟨run, ht, hs, ho, hb⟩ := RawQueryCompleted.completed_query q
  have htime := RawQueryBounds.timeBound_polynomial q
  have hone : 1 ≤ (RawQueryBounds.extent q + 1) ^ 3 :=
    Nat.succ_le_of_lt (by positivity)
  have hsquare : 1 ≤ (RawQueryBounds.extent q + 1) ^ 2 :=
    Nat.succ_le_of_lt (by positivity)
  have hlinear : RawQueryBounds.extent q + 1 ≤ (RawQueryBounds.extent q + 1) ^ 3 := by
    calc
      RawQueryBounds.extent q + 1 = (RawQueryBounds.extent q + 1) * 1 := by omega
      _ ≤ (RawQueryBounds.extent q + 1) * (RawQueryBounds.extent q + 1) ^ 2 :=
        Nat.mul_le_mul_left _ hsquare
      _ = (RawQueryBounds.extent q + 1) ^ 3 := by ring
  have hbits : (QueryCodec.encode q).length ≤ RawQueryBounds.extent q := by
    simp only [RawQueryBounds.extent]
    omega
  exact ⟨run, by omega, by omega, ho, hb⟩

end QecReliability.ExternalSATBridge.RawQueryPolynomial
