import TensorCountingAnswers

/-! The actual counting schedule, including both forward-table reversals,
terminates at the boundary intercepted by the tensor repair controller. -/
set_option autoImplicit false
namespace QecReliability.TensorMachine.CountingTrace
open OracleCost OracleCost.WholeWrapperCandidate

theorem initial_to_tables_trace (q r B m : ℕ) (shape : Bool) (ext : External) :
    let js := List.finRange (r+1)
    let good := sideEntries q r B m ext true js
    let bad := sideEntries q r B m ext false js
    ∃ t totals events,
      Trace q r B m shape ext (initial q r m) totals events t ∧
      t.pc = .endpointZero ∧ t.code = [] ∧
      t.goodTable = good ∧ t.badTable = bad ∧
      totals.calls = sideCalls q r B m ext true js + sideCalls q r B m ext false js ∧
      totals.oracleTime = sideTime q r B m ext true js + sideTime q r B m ext false js ∧
      totals.endpointTime = 0 ∧
      totals.dispatches ≤ 8*totals.calls + 2*(r+1)*coefficientLocalBound q m + 2*(r+1)+3 := by
  let js := List.finRange (r+1)
  let tailCode := js.flatMap (fun j => coefficientCode q m false j.val) ++ [.finish]
  obtain ⟨mid,gt,ge,hg,hmp,hmc,hmg,hmb,_,hgc,hgtime,hge,hgs⟩ :=
    coefficients_trace q r B m ext shape true js (initial q r m) tailCode rfl
      (by simp only [initial, program_finRange, tailCode, js, List.append_assoc])
  obtain ⟨last,bt,be,hb,hlp,hlc,hlg,hlb,_,hbc,hbtime,hbe,hbs⟩ :=
    coefficients_trace q r B m ext shape false js mid [.finish] hmp hmc
  have hgood : last.goodRev = (sideEntries q r B m ext true js).reverse := by
    simpa [hmg, initial] using hlg
  have hbad : last.badRev = (sideEntries q r B m ext false js).reverse := by
    simpa [hmb, initial] using hlb
  let final : Config := { last with
    pc := .endpointZero, code := [], goodRev := [], badRev := [],
    goodTable := last.goodRev.reverse, badTable := last.badRev.reverse,
    pairSrc := [], pairDst := [] }
  let totals := Totals.append (Totals.append gt bt)
    (localTotals (last.goodRev.length + last.badRev.length + 3))
  have hf := (finish_tables_trace q r B m shape ext last [] hlp hlc).toTrace
  refine ⟨final,totals,ge++be,?_,rfl,rfl,?_,?_,?_,?_,?_,?_⟩
  · simpa [final, totals] using (hg.trans hb).trans hf
  · simp [final, hgood, js]
  · simp [final, hbad, js]
  · simp only [totals, Totals.append, localTotals, hgc, hbc, Nat.add_zero, js]
  · simp only [totals, Totals.append, localTotals, hgtime, hbtime, Nat.add_zero, js]
  · simp only [totals, Totals.append, localTotals, hge, hbe, Nat.add_zero]
  · have hgl : last.goodRev.length = r+1 := by
      simp [hgood, sideEntries, js]
    have hbl : last.badRev.length = r+1 := by
      simp [hbad, sideEntries, js]
    simp only [js, List.length_finRange] at hgs hbs
    simp only [totals, Totals.append, localTotals, hgc, hbc, hgl, hbl, Nat.add_zero]
    nlinarith

end QecReliability.TensorMachine.CountingTrace
