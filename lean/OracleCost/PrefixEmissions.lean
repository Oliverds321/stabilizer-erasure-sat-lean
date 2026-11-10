import OracleCost.PrefixDriver
import OracleCost.PrefixInvariant

/-! The emitted prefix sequence is derived from actual Await transitions.
It is a ghost execution record, not stored by the controller. In particular,
the empty pending sequence at Done is not confused with total emitted calls.
-/
namespace QecReliability.OracleCost.PrefixTransitions

def emitted (s : Config) : List (List Bool) :=
  match s.control with
  | .await _ pre _ => [pre]
  | _ => []

inductive EmissionTrace (oracle : List Bool → SATReply) :
    Config → ℕ → List (List Bool) → Config → Prop
  | nil (s) : EmissionTrace oracle s 0 [] s
  | cons {s e t n requests} (he : step oracle s=some e)
      (tail : EmissionTrace oracle e.next n requests t) :
      EmissionTrace oracle s (n+1) (emitted s++requests) t

theorem emitted_step {oracle : List Bool → SATReply} {s : Config} {e : Edge}
    (h : step oracle s=some e) :
    (emitted s).length=e.calls ∧
      ((emitted s).map (fun pre => (oracle pre).time)).sum=e.serviceTime := by
  rcases s with ⟨control,stack⟩
  cases control with
  | enter q pre cap =>
    simp only [step,Option.some.injEq] at h
    subst e
    simp [emitted]
  | await q pre cap =>
    simp only [step,Option.some.injEq] at h
    subst e
    simp [emitted]
  | ret count =>
    cases stack with
    | nil => simp [step] at h
    | cons f stack =>
      cases f <;> simp only [step,Option.some.injEq] at h <;>
        subst e <;> simp [emitted]

theorem Trace.emissions {oracle : List Bool → SATReply} {s t : Config}
    {n calls time : ℕ} (h : Trace oracle s n calls time t) :
    ∃ requests, EmissionTrace oracle s n requests t ∧ requests.length=calls ∧
      (requests.map (fun pre => (oracle pre).time)).sum=time := by
  induction h with
  | nil s => exact ⟨[],.nil _,rfl,rfl⟩
  | cons he tail ih =>
    obtain ⟨requests,hr,hc,ht⟩ := ih
    have edge := emitted_step he
    exact ⟨_,.cons he hr,by simp [edge.1,hc],by simp [List.map_append,edge.2,ht]⟩

theorem emitted_valid {Q cap : ℕ} {s : Config} (hs : Valid Q cap s) :
    ∀ pre∈emitted s, pre.length≤Q := by
  rcases s with ⟨control,stack⟩
  cases control with
  | enter => simp [emitted]
  | ret => simp [emitted]
  | await depth path budget =>
    intro pre hpre
    simp only [emitted,List.mem_singleton] at hpre
    subst pre
    exact (valid_await hs).1

theorem EmissionTrace.valid_prefixes {oracle : List Bool → SATReply} {s t : Config}
    {n : ℕ} {requests : List (List Bool)} (h : EmissionTrace oracle s n requests t)
    {Q cap : ℕ} (hs : Valid Q cap s) : ∀ pre∈requests, pre.length≤Q := by
  induction h with
  | nil => simp
  | cons he tail ih =>
    intro pre hp
    rcases List.mem_append.mp hp with hp|hp
    · exact emitted_valid hs pre hp
    · exact ih (step_valid oracle hs he) pre hp

end QecReliability.OracleCost.PrefixTransitions
