import OracleCost.PrefixTransitions

/-! A fuelled interpreter for the explicit controller. Fuel is a safety bound,
not a prescribed iteration count: terminal control returns immediately. The
finite trace theorem supplies termination and exact observations for all inputs.
Macro instruction implementation on bit tapes remains separate. -/
namespace QecReliability.OracleCost.PrefixTransitions

structure RunResult where
  final : Config
  steps : ℕ
  calls : ℕ
  serviceTime : ℕ
  deriving DecidableEq

def drive (oracle : List Bool → SATReply) : ℕ → Config → Option RunResult
  | 0,_ => none
  | fuel+1,s =>
    match step oracle s with
    | none => some ⟨s,0,0,0⟩
    | some e => do
      let result ← drive oracle fuel e.next
      pure ⟨result.final,result.steps+1,e.calls+result.calls,
        e.serviceTime+result.serviceTime⟩

theorem Trace.drive_result {oracle : List Bool → SATReply} {s t : Config} {n c time : ℕ}
    (h : Trace oracle s n c time t) (ht : step oracle t=none)
    (fuel : ℕ) (hf : n<fuel) : drive oracle fuel s=some ⟨t,n,c,time⟩ := by
  induction h generalizing fuel with
  | nil s =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [drive,ht]
  | @cons s e t n c time he tail ih =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [drive,he,ih ht fuel (by omega)]

theorem drive_trace {oracle : List Bool → SATReply} {fuel : ℕ} {s : Config}
    {result : RunResult} (h : drive oracle fuel s=some result) :
    Trace oracle s result.steps result.calls result.serviceTime result.final ∧
      step oracle result.final=none := by
  induction fuel generalizing s result with
  | zero => simp [drive] at h
  | succ fuel ih =>
    cases he : step oracle s with
    | none =>
      simp only [drive,he,Option.some.injEq] at h
      subst result
      exact ⟨Trace.nil _,he⟩
    | some e =>
      cases hr : drive oracle fuel e.next with
      | none => simp [drive,he,hr] at h
      | some next =>
        simp [drive,he,hr] at h
        subst result
        have hh := ih hr
        exact ⟨Trace.cons he hh.1,hh.2⟩

/-- A full binary tree bounds arbitrary inconsistent callback responses.
This deliberately does not use the much smaller exact-decision call bound. -/
theorem full_tree_bound (q : ℕ) (oracle : List Bool → SATReply)
    (pre : List Bool) (cap : ℕ) :
    (PrefixMachine.execute q oracle pre cap).control.calls<2^(q+1) ∧
    (PrefixMachine.execute q oracle pre cap).control.visits<2^(q+1) := by
  induction q generalizing pre cap with
  | zero =>
    by_cases hc : cap=0 <;> cases ho : (oracle pre).value <;>
      simp [PrefixMachine.execute,hc,ho]
  | succ q ih =>
    have pos : 0<2^(q+1) := pow_pos (by decide) _
    have hs : 2^(q+1+1)=2*2^(q+1) := by rw [pow_succ]; omega
    by_cases hc : cap=0
    · simp only [PrefixMachine.execute,hc,↓reduceIte,hs]
      omega
    · cases ho : (oracle pre).value with
      | false =>
        simp only [PrefixMachine.execute,hc,↓reduceIte,ho,Bool.false_eq_true,hs]
        omega
      | true =>
        have hl := ih (pre++[false]) cap
        have hr := ih (pre++[true])
          (cap-(PrefixMachine.execute q oracle (pre++[false]) cap).control.count)
        simp only [PrefixMachine.execute,hc,↓reduceIte,ho,hs]
        omega

def fuelBound (q : ℕ) : ℕ := 3*2^(q+1)

def run (q : ℕ) (oracle : List Bool → SATReply) (cap : ℕ) : Option RunResult :=
  drive oracle (fuelBound q) ⟨.enter q [] cap,[]⟩

/-- The implemented driver always succeeds and has exactly the recursive
enumerator's output and callback observations. No termination hypothesis. -/
theorem run_spec (q : ℕ) (oracle : List Bool → SATReply) (cap : ℕ) :
    ∃ result, run q oracle cap=some result ∧
      result.final=⟨.ret (PrefixMachine.execute q oracle [] cap).control.count,[]⟩ ∧
      result.calls=(PrefixMachine.execute q oracle [] cap).control.calls ∧
      result.serviceTime=(PrefixMachine.execute q oracle [] cap).control.oracleTime ∧
      result.steps≤5*result.calls+1 := by
  obtain ⟨steps,h,eq⟩ := execute_trace q oracle [] cap []
  have full := full_tree_bound q oracle [] cap
  have hf : steps<fuelBound q := by unfold fuelBound; omega
  have hd := h.drive_result (by rfl) (fuelBound q) hf
  have v := PrefixControl.visits_le q (fun pre => (oracle pre).value)
    (fun pre => (oracle pre).time) cap
  have ce := PrefixMachine.control_eq q oracle [] cap
  simp only [List.nil_append] at ce
  rw [← ce] at v
  exact ⟨_,hd,rfl,rfl,rfl,by dsimp; omega⟩

end QecReliability.OracleCost.PrefixTransitions
