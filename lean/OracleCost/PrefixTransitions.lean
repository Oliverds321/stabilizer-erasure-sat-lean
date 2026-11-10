import OracleCost.PrefixMachine

/-! A first-order controller for the capped prefix traversal. Configurations
contain only natural registers, Boolean lists and a stack of two frame tags;
no continuation functions are stored. `await` is the sole service-invocation
phase. A finite trace is a proof object, not a retained execution log.

The steps here are macro instructions (including list append and arithmetic).
This module does not identify one macro step with one bit-machine instruction.
-/
namespace QecReliability.OracleCost.PrefixTransitions

inductive Frame where
  | left (depth : ℕ) (pre : List Bool) (cap : ℕ)
  | right (leftCount : ℕ)
  deriving DecidableEq

inductive Control where
  | enter (depth : ℕ) (pre : List Bool) (cap : ℕ)
  | await (depth : ℕ) (pre : List Bool) (cap : ℕ)
  | ret (count : ℕ)
  deriving DecidableEq

structure Config where
  control : Control
  stack : List Frame
  deriving DecidableEq

structure Edge where
  next : Config
  calls : ℕ
  serviceTime : ℕ

/-- Exactly one service invocation in the await case, none in local control.
The wrapper stack is unchanged while obtaining that invocation's reply. -/
def step (oracle : List Bool → SATReply) : Config → Option Edge
  | ⟨.enter q pre cap, stack⟩ =>
    some ⟨⟨if cap=0 then .ret 0 else .await q pre cap, stack⟩,0,0⟩
  | ⟨.await q pre cap, stack⟩ =>
    let reply := oracle pre
    let next := if reply.value then
      match q with
      | 0 => ⟨.ret 1,stack⟩
      | d+1 => ⟨.enter d (pre++[false]) cap,.left d pre cap::stack⟩
      else ⟨.ret 0,stack⟩
    some ⟨next,1,reply.time⟩
  | ⟨.ret _, []⟩ => none
  | ⟨.ret count, .left q pre cap::stack⟩ =>
    some ⟨⟨.enter q (pre++[true]) (cap-count),.right count::stack⟩,0,0⟩
  | ⟨.ret count, .right leftCount::stack⟩ =>
    some ⟨⟨.ret (leftCount+count),stack⟩,0,0⟩

theorem step_enter_zero (oracle : List Bool → SATReply) (q : ℕ)
    (pre : List Bool) (cap : ℕ) (stack : List Frame) (hc : cap=0) :
    step oracle ⟨.enter q pre cap,stack⟩=some ⟨⟨.ret 0,stack⟩,0,0⟩ := by simp [step,hc]

theorem step_enter_pos (oracle : List Bool → SATReply) (q : ℕ)
    (pre : List Bool) (cap : ℕ) (stack : List Frame) (hc : cap≠0) :
    step oracle ⟨.enter q pre cap,stack⟩=some ⟨⟨.await q pre cap,stack⟩,0,0⟩ := by simp [step,hc]

theorem step_await_false (oracle : List Bool → SATReply) (q : ℕ)
    (pre : List Bool) (cap : ℕ) (stack : List Frame) (ho : (oracle pre).value=false) :
    step oracle ⟨.await q pre cap,stack⟩=some ⟨⟨.ret 0,stack⟩,1,(oracle pre).time⟩ := by simp [step,ho]

theorem step_await_leaf (oracle : List Bool → SATReply)
    (pre : List Bool) (cap : ℕ) (stack : List Frame) (ho : (oracle pre).value=true) :
    step oracle ⟨.await 0 pre cap,stack⟩=some ⟨⟨.ret 1,stack⟩,1,(oracle pre).time⟩ := by simp [step,ho]

theorem step_await_branch (oracle : List Bool → SATReply) (q : ℕ)
    (pre : List Bool) (cap : ℕ) (stack : List Frame) (ho : (oracle pre).value=true) :
    step oracle ⟨.await (q+1) pre cap,stack⟩=
      some ⟨⟨.enter q (pre++[false]) cap,.left q pre cap::stack⟩,1,(oracle pre).time⟩ := by simp [step,ho]

/-- Finite operational traces with actual edge counters. -/
inductive Trace (oracle : List Bool → SATReply) : Config → ℕ → ℕ → ℕ → Config → Prop
  | nil (s) : Trace oracle s 0 0 0 s
  | cons {s e t n calls time} (h : step oracle s=some e)
      (tail : Trace oracle e.next n calls time t) :
      Trace oracle s (n+1) (e.calls+calls) (e.serviceTime+time) t

theorem Trace.single {oracle : List Bool → SATReply} {s : Config} {e : Edge}
    (h : step oracle s=some e) : Trace oracle s 1 e.calls e.serviceTime e.next := by
  simpa using Trace.cons h (Trace.nil e.next)

theorem Trace.trans {oracle : List Bool → SATReply} {s t u : Config}
    {n₁ c₁ t₁ n₂ c₂ t₂ : ℕ}
    (h₁ : Trace oracle s n₁ c₁ t₁ t) (h₂ : Trace oracle t n₂ c₂ t₂ u) :
    Trace oracle s (n₁+n₂) (c₁+c₂) (t₁+t₂) u := by
  induction h₁ with
  | nil => simpa using h₂
  | cons h tail ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Trace.cons h (ih h₂)

/-- Determinism is about the operational transition, for a fixed service. -/
theorem step_deterministic {oracle : List Bool → SATReply} {s : Config} {a b : Edge}
    (ha : step oracle s=some a) (hb : step oracle s=some b) : a=b := by
  exact Option.some.inj (ha.symm.trans hb)

theorem terminal_iff (oracle : List Bool → SATReply) (s : Config) :
    step oracle s=none ↔ ∃ count, s=⟨.ret count,[]⟩ := by
  rcases s with ⟨control,stack⟩
  cases control with
  | enter q pre cap => simp [step]
  | await q pre cap => simp [step]
  | ret count =>
    cases stack with
    | nil => simp [step]
    | cons frame stack => cases frame <;> simp [step]

/-- Totality and value/call/time refinement are proved together, for arbitrary
callbacks. No exactness or assumed termination premise is needed. The final
configuration retains exactly the caller's stack. -/
theorem execute_trace (q : ℕ) (oracle : List Bool → SATReply) (pre : List Bool)
    (cap : ℕ) (stack : List Frame) :
    ∃ steps, Trace oracle ⟨.enter q pre cap,stack⟩ steps
      (PrefixMachine.execute q oracle pre cap).control.calls
      (PrefixMachine.execute q oracle pre cap).control.oracleTime
      ⟨.ret (PrefixMachine.execute q oracle pre cap).control.count,stack⟩ ∧
      steps+1=2*(PrefixMachine.execute q oracle pre cap).control.visits+
        (PrefixMachine.execute q oracle pre cap).control.calls := by
  induction q generalizing pre cap stack with
  | zero =>
    by_cases hc : cap=0
    · refine ⟨1,?_,?_⟩
      · simpa [PrefixMachine.execute,hc] using
          (Trace.single (step_enter_zero oracle 0 pre cap stack hc))
      · simp [PrefixMachine.execute,hc]
    · cases ho : (oracle pre).value with
      | false =>
        refine ⟨2,?_,?_⟩
        · simpa [PrefixMachine.execute,hc,ho] using
            (Trace.cons (step_enter_pos oracle 0 pre cap stack hc)
              (Trace.single (step_await_false oracle 0 pre cap stack ho)))
        · simp [PrefixMachine.execute,hc,ho]
      | true =>
        refine ⟨2,?_,?_⟩
        · simpa [PrefixMachine.execute,hc,ho] using
            (Trace.cons (step_enter_pos oracle 0 pre cap stack hc)
              (Trace.single (step_await_leaf oracle pre cap stack ho)))
        · simp [PrefixMachine.execute,hc,ho]
  | succ q ih =>
    by_cases hc : cap=0
    · refine ⟨1,?_,?_⟩
      · simpa [PrefixMachine.execute,hc] using
          (Trace.single (step_enter_zero oracle (q+1) pre cap stack hc))
      · simp [PrefixMachine.execute,hc]
    · cases ho : (oracle pre).value with
      | false =>
        refine ⟨2,?_,?_⟩
        · simpa [PrefixMachine.execute,hc,ho] using
            (Trace.cons (step_enter_pos oracle (q+1) pre cap stack hc)
              (Trace.single (step_await_false oracle (q+1) pre cap stack ho)))
        · simp [PrefixMachine.execute,hc,ho]
      | true =>
        let left := PrefixMachine.execute q oracle (pre++[false]) cap
        let right := PrefixMachine.execute q oracle (pre++[true]) (cap-left.control.count)
        obtain ⟨nl,hl,el⟩ := ih (pre++[false]) cap (.left q pre cap::stack)
        obtain ⟨nr,hr,er⟩ := ih (pre++[true]) (cap-left.control.count) (.right left.control.count::stack)
        change Trace oracle _ nl left.control.calls left.control.oracleTime _ at hl
        change Trace oracle _ nr right.control.calls right.control.oracleTime _ at hr
        have join := Trace.cons (oracle:=oracle)
          (s:=⟨.ret left.control.count,.left q pre cap::stack⟩) (by rfl)
          (hr.trans (Trace.single (by rfl)))
        have all := Trace.cons (step_enter_pos oracle (q+1) pre cap stack hc)
          (Trace.cons (step_await_branch oracle q pre cap stack ho) (hl.trans join))
        refine ⟨nl+nr+4,?_,?_⟩
        · simp only [PrefixMachine.execute,hc,↓reduceIte,ho]
          change Trace oracle _ (nl+nr+4) (1+left.control.calls+right.control.calls)
            ((oracle pre).time+left.control.oracleTime+right.control.oracleTime)
            ⟨.ret (left.control.count+right.control.count),stack⟩
          convert all using 1 <;> simp only [Nat.zero_add,Nat.add_zero] <;> omega
        · change nl+1=2*left.control.visits+left.control.calls at el
          change nr+1=2*right.control.visits+right.control.calls at er
          simp only [PrefixMachine.execute,hc,↓reduceIte,ho]
          change nl+nr+4+1=2*(1+left.control.visits+right.control.visits)+
            (1+left.control.calls+right.control.calls)
          omega

/-- Two completed traces of this deterministic controller coincide, including
their measured calls and service-time sum. -/
theorem Trace.terminal_unique {oracle : List Bool → SATReply} {s t u : Config}
    {n c time n' c' time' : ℕ} (h : Trace oracle s n c time t)
    (h' : Trace oracle s n' c' time' u) (ht : step oracle t=none)
    (hu : step oracle u=none) : t=u ∧ n=n' ∧ c=c' ∧ time=time' := by
  induction h generalizing n' c' time' u with
  | nil s =>
    cases h' with
    | nil => exact ⟨rfl,rfl,rfl,rfl⟩
    | cons he _ => rw [ht] at he; cases he
  | @cons s e t n c time he tail ih =>
    cases h' with
    | nil => rw [hu] at he; cases he
    | @cons _ e' _ n' c' time' he' tail' =>
      have ee := step_deterministic he he'
      subst e'
      obtain ⟨h₁,h₂,h₃,h₄⟩ := ih tail' ht hu
      exact ⟨h₁,congrArg (·+1) h₂,congrArg (e.calls+·) h₃,
        congrArg (e.serviceTime+·) h₄⟩

/-- Every root invocation halts; arbitrary callback responses are allowed.
The linear macro-step bound is in its actual number of calls. A polynomial
bound on those calls requires the separate exact-decision theorem. -/
theorem halts (q : ℕ) (oracle : List Bool → SATReply) (cap : ℕ) :
    ∃ steps, Trace oracle ⟨.enter q [] cap,[]⟩ steps
      (PrefixMachine.execute q oracle [] cap).control.calls
      (PrefixMachine.execute q oracle [] cap).control.oracleTime
      ⟨.ret (PrefixMachine.execute q oracle [] cap).control.count,[]⟩ ∧
      steps≤5*(PrefixMachine.execute q oracle [] cap).control.calls+1 := by
  obtain ⟨steps,h,e⟩ := execute_trace q oracle [] cap []
  have v := PrefixControl.visits_le q (fun pre => (oracle pre).value)
    (fun pre => (oracle pre).time) cap
  have eq := PrefixMachine.control_eq q oracle [] cap
  simp only [List.nil_append] at eq
  rw [← eq] at v
  exact ⟨steps,h,by omega⟩

end QecReliability.OracleCost.PrefixTransitions
