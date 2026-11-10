import OracleCost.Interface

/-! Instrument the actual capped prefix recursion. No trace is retained: each
return carries the count and scalar accounting only. The accounting is ghost
measurement data, not additional retained algorithm storage. `oracleCharge pre` is the
cost of the single callback on that concrete prefix. Visits and frames are
control events, not yet a bit-cost or native-heap simulation theorem.
-/
namespace QecReliability.OracleCost.PrefixControl
open PrefixEnumeration

structure Result where
  count : ℕ
  calls : ℕ
  visits : ℕ
  oracleTime : ℕ
  peakFrames : ℕ
  deriving DecidableEq

def run : (q : ℕ) → (List Bool → Bool) → (List Bool → ℕ) → ℕ → Result
  | 0, answer, charge, cap =>
      if cap=0 then ⟨0,0,1,0,1⟩
      else if answer [] then ⟨1,1,1,charge [],1⟩ else ⟨0,1,1,charge [],1⟩
  | q+1, answer, charge, cap =>
      if cap=0 then ⟨0,0,1,0,1⟩
      else if answer [] then
        let left := run q (fun pre => answer (false::pre))
          (fun pre => charge (false::pre)) cap
        let right := run q (fun pre => answer (true::pre))
          (fun pre => charge (true::pre)) (cap-left.count)
        ⟨left.count+right.count, 1+left.calls+right.calls,
          1+left.visits+right.visits, charge []+left.oracleTime+right.oracleTime,
          1+max left.peakFrames right.peakFrames⟩
      else ⟨0,1,1,charge [],1⟩

@[simp] theorem run_zero_cap (q : ℕ) (answer : List Bool → Bool)
    (charge : List Bool → ℕ) : run q answer charge 0=⟨0,0,1,0,1⟩ := by
  cases q <;> simp [run]

/-- Literal agreement with the existing evaluator, on arbitrary callbacks. -/
theorem erase (q : ℕ) (answer : List Bool → Bool) (charge : List Bool → ℕ) (cap : ℕ) :
    (run q answer charge cap).count=(enumerate q answer cap).1 ∧
    (run q answer charge cap).calls=(enumerate q answer cap).2 := by
  induction q generalizing answer charge cap with
  | zero => by_cases hc : cap=0 <;> cases ha : answer [] <;> simp [run, enumerate, hc, ha]
  | succ q ih =>
    by_cases hc : cap=0
    · subst cap; simp
    · cases ha : answer [] with
      | false => simp [run, enumerate, hc, ha]
      | true =>
        have hl := ih (fun pre => answer (false::pre)) (fun pre => charge (false::pre)) cap
        have hr := ih (fun pre => answer (true::pre)) (fun pre => charge (true::pre))
          (cap-(run q (fun pre => answer (false::pre)) (fun pre => charge (false::pre)) cap).count)
        simp only [run, enumerate, if_neg hc, ha, ↓reduceIte]
        rw [hl.1] at hr
        rw [hl.1, hl.2, hr.1, hr.2]
        exact ⟨rfl,rfl⟩

/-- Cap-zero children are counted as visits, even though they make no query. -/
theorem visits_le (q : ℕ) (answer : List Bool → Bool) (charge : List Bool → ℕ) (cap : ℕ) :
    (run q answer charge cap).visits ≤ 2*(run q answer charge cap).calls+1 := by
  induction q generalizing answer charge cap with
  | zero => by_cases hc : cap=0 <;> cases ha : answer [] <;> simp [run, hc, ha]
  | succ q ih =>
    by_cases hc : cap=0
    · subst cap; simp
    · cases ha : answer [] with
      | false => simp [run,hc,ha]
      | true =>
        have hl := ih (fun pre => answer (false::pre)) (fun pre => charge (false::pre)) cap
        have hr := ih (fun pre => answer (true::pre)) (fun pre => charge (true::pre))
          (cap-(run q (fun pre => answer (false::pre)) (fun pre => charge (false::pre)) cap).count)
        simp only [run,if_neg hc,ha,↓reduceIte]
        omega

theorem peakFrames_le (q : ℕ) (answer : List Bool → Bool) (charge : List Bool → ℕ) (cap : ℕ) :
    (run q answer charge cap).peakFrames ≤ q+1 := by
  induction q generalizing answer charge cap with
  | zero => by_cases hc : cap=0 <;> cases ha : answer [] <;> simp [run, hc, ha]
  | succ q ih =>
    by_cases hc : cap=0
    · subst cap; simp
    · cases ha : answer [] with
      | false => simp [run,hc,ha]
      | true =>
        have hl := ih (fun pre => answer (false::pre)) (fun pre => charge (false::pre)) cap
        have hr := ih (fun pre => answer (true::pre)) (fun pre => charge (true::pre))
          (cap-(run q (fun pre => answer (false::pre)) (fun pre => charge (false::pre)) cap).count)
        simp only [run,if_neg hc,ha,↓reduceIte]
        omega

/-- Each callback is charged once. The caller need only bound prefixes that
the recursion can actually reach; no superlinear function of `bound` occurs. -/
theorem oracleTime_le (q : ℕ) (answer : List Bool → Bool) (charge : List Bool → ℕ)
    (cap bound : ℕ) (h : ∀ pre, pre.length≤q → charge pre≤bound) :
    (run q answer charge cap).oracleTime ≤ (run q answer charge cap).calls*bound := by
  induction q generalizing answer charge cap with
  | zero =>
    have hz := h [] (by simp)
    simp only [run]
    split <;> simp_all
    split <;> simp_all
  | succ q ih =>
    have hz := h [] (by simp)
    by_cases hc : cap=0
    · subst cap; simp
    · cases ha : answer [] with
      | false => simpa [run,hc,ha] using hz
      | true =>
        have hl := ih (fun pre => answer (false::pre)) (fun pre => charge (false::pre)) cap
          (fun pre hp => h (false::pre) (by simpa using Nat.succ_le_succ hp))
        have hr := ih (fun pre => answer (true::pre)) (fun pre => charge (true::pre))
          (cap-(run q (fun pre => answer (false::pre)) (fun pre => charge (false::pre)) cap).count)
          (fun pre hp => h (true::pre) (by simpa using Nat.succ_le_succ hp))
        simp only [run,if_neg hc,ha,↓reduceIte]
        nlinarith

theorem exact_count_and_calls {q : ℕ} {P : BitModels q → Prop}
    (D : ExactDecision P) (charge : List Bool → ℕ) (cap : ℕ) :
    (run q D.answer charge cap).count=min cap (modelCount P) ∧
    (run q D.answer charge cap).calls≤1+2*q*min cap (modelCount P) := by
  rw [(erase q D.answer charge cap).1,(erase q D.answer charge cap).2]
  exact enumerate_spec D cap

end QecReliability.OracleCost.PrefixControl
