import OracleCost.PrefixControl

/-! A concrete-prefix evaluator with a single external invocation at each query.
The returned service reply supplies both its Boolean result and cost observation.
Prefix append work is measured where the copy occurs; no query log is retained.
The service workspace observation is separate from retained wrapper frames.
-/
namespace QecReliability.OracleCost.PrefixMachine

structure Result where
  control : PrefixControl.Result
  prefixCopies : ℕ
  oraclePeak : ℕ

def execute : ℕ → (List Bool → SATReply) → List Bool → ℕ → Result
  | 0, oracle, pre, cap =>
    if cap=0 then ⟨⟨0,0,1,0,1⟩,0,0⟩ else
    let reply := oracle pre
    ⟨⟨if reply.value then 1 else 0,1,1,reply.time,1⟩,0,reply.workspace⟩
  | q+1, oracle, pre, cap =>
    if cap=0 then ⟨⟨0,0,1,0,1⟩,0,0⟩ else
    let reply := oracle pre
    if reply.value then
      let left := execute q oracle (pre++[false]) cap
      let right := execute q oracle (pre++[true]) (cap-left.control.count)
      ⟨⟨left.control.count+right.control.count,1+left.control.calls+right.control.calls,
         1+left.control.visits+right.control.visits,
         reply.time+left.control.oracleTime+right.control.oracleTime,
         1+max left.control.peakFrames right.control.peakFrames⟩,
       2*(pre.length+1)+left.prefixCopies+right.prefixCopies,
       max reply.workspace (max left.oraclePeak right.oraclePeak)⟩
    else ⟨⟨0,1,1,reply.time,1⟩,0,reply.workspace⟩

/-- Copy count charges both traversing an existing prefix and allocating its
new final list cell; it is not a claim about constant-time list append. -/
theorem control_eq (q : ℕ) (oracle : List Bool → SATReply) (pre : List Bool) (cap : ℕ) :
    (execute q oracle pre cap).control=
      PrefixControl.run q (fun tail => (oracle (pre++tail)).value)
        (fun tail => (oracle (pre++tail)).time) cap := by
  induction q generalizing pre cap with
  | zero =>
    by_cases hc : cap=0 <;> cases ho : (oracle pre).value <;>
      simp [execute,PrefixControl.run,hc,ho]
  | succ q ih =>
    by_cases hc : cap=0
    · simp [execute,PrefixControl.run,hc]
    · cases ho : (oracle pre).value with
      | false => simp [execute,PrefixControl.run,hc,ho]
      | true =>
        simp only [execute,PrefixControl.run,hc,↓reduceIte,List.append_nil,ho]
        rw [ih,ih]
        simp only [List.append_assoc,List.singleton_append]

/-- The external peak is a maximum over executed calls, not a sum over time. -/
theorem oraclePeak_le (q : ℕ) (oracle : List Bool → SATReply) (pre : List Bool)
    (cap bound : ℕ)
    (h : ∀ tail, tail.length≤q → (oracle (pre++tail)).workspace≤bound) :
    (execute q oracle pre cap).oraclePeak≤bound := by
  induction q generalizing pre cap with
  | zero =>
    have hz := h [] (by simp)
    by_cases hc : cap=0
    · simp [execute,hc]
    · simpa [execute,hc] using hz
  | succ q ih =>
    have hz : (oracle pre).workspace≤bound := by simpa using h [] (by simp)
    by_cases hc : cap=0
    · simp [execute,hc]
    · cases ho : (oracle pre).value with
      | false => simpa [execute,hc,ho] using hz
      | true =>
        have hl := ih (pre++[false]) cap (fun tail ht => by
          simpa only [List.append_assoc,List.singleton_append] using
            h (false::tail) (by simpa using Nat.succ_le_succ ht))
        have hr := ih (pre++[true]) (cap-(execute q oracle (pre++[false]) cap).control.count)
          (fun tail ht => by
            simpa only [List.append_assoc,List.singleton_append] using
              h (true::tail) (by simpa using Nat.succ_le_succ ht))
        simpa only [execute,hc,↓reduceIte,ho] using max_le hz (max_le hl hr)

/-- List-prefix construction has polynomial traversal cost on every run,
including cap-zero children and unsatisfiable roots. -/
theorem prefixCopies_le (q : ℕ) (oracle : List Bool → SATReply) (pre : List Bool) (cap : ℕ) :
    (execute q oracle pre cap).prefixCopies≤
      2*(pre.length+q+1)*(execute q oracle pre cap).control.calls := by
  induction q generalizing pre cap with
  | zero => by_cases hc : cap=0 <;> simp [execute,hc]
  | succ q ih =>
    by_cases hc : cap=0
    · simp [execute,hc]
    · cases ho : (oracle pre).value with
      | false => simp [execute,hc,ho]
      | true =>
        have hl := ih (pre++[false]) cap
        have hr := ih (pre++[true]) (cap-(execute q oracle (pre++[false]) cap).control.count)
        simp only [List.length_append,List.length_singleton] at hl hr
        simp only [execute,hc,↓reduceIte,ho]
        nlinarith

end QecReliability.OracleCost.PrefixMachine
