import OracleCost.TraceDisplacementCandidate
import Mathlib.Data.Fintype.Sigma

/-! Actual finite block union whose handoff table inspects the ACTUAL terminal
child label as well as its Boolean result. This permits a finite seven-tag
fetch block and other PC phases to return to a shared cyclic dispatcher.
Only real child halts trigger routing; an ordinary child advance preserves
its exact writes/moves. Every routed edge writes self/stays and costs ONE.
No ghost source PC, schedule, free reset, recursive whole-machine embedding,
or primitive implementation/resource contract is introduced. -/
namespace QecReliability.OracleCost.MultiTape.LabelRoutedNetwork
open Turing Displacement
variable {k : ℕ} {Γ I : Type} [Fintype Γ] [Inhabited Γ] [Fintype I]
variable (Labels : I → Type) [∀ i, Fintype (Labels i)]
variable (blocks : ∀ i, Machine k Γ (Labels i)) (first : I) (next : (i : I) → Labels i → Bool → Option I)

abbrev Control := Sigma Labels

def machine : Machine k Γ (Control Labels) where
  start := ⟨first,(blocks first).start⟩
  inputSymbol := (blocks first).inputSymbol
  input_injective := (blocks first).input_injective
  input_not_blank := (blocks first).input_not_blank
  transition state heads :=
    match (blocks state.1).transition state.2 heads with
    | .advance label write move => .advance ⟨state.1,label⟩ write move
    | .halt b => match next state.1 state.2 b with
      | none => .halt b
      | some j => .advance ⟨j,(blocks j).start⟩ heads (fun _ => .stay)

def embed (i : I) (s : Config k Γ (Labels i)) : Config k Γ (Control Labels) :=
  ⟨⟨i,s.label⟩,s.tapes⟩

@[simp] theorem initial (bits : List Bool) :
    (machine Labels blocks first next).initial bits=embed Labels first ((blocks first).initial bits) := rfl

theorem step {i : I} {s t : Config k Γ (Labels i)}
    (he : (blocks i).step s=some t) :
    (machine Labels blocks first next).step (embed Labels i s)=some (embed Labels i t) := by
  cases ha : (blocks i).transition s.label (fun j => (s.tapes j).head) with
  | halt b => simp [Machine.step,Machine.action,ha] at he
  | advance label write move =>
    simp only [Machine.step,Machine.action,ha,Option.some.injEq] at he
    subst t
    simp [Machine.step,Machine.action,machine,embed,ha]

theorem delta_embed (i : I) (s : Config k Γ (Labels i)) :
    delta (machine Labels blocks first next) (embed Labels i s)=delta (blocks i) s := by
  cases ha : (blocks i).transition s.label (fun j => (s.tapes j).head) with
  | halt b =>
    cases hn : next i s.label b <;> simp [delta,Machine.action,machine,embed,ha,hn,Move.delta]
  | advance label write move => simp [delta,Machine.action,machine,embed,ha]

/-- Actual component traces lift with identical physical edge count and signed
movement. This does not materialize component endpoints or erase their history. -/
theorem run {i : I} {s t : Config k Γ (Labels i)} {n d}
    (h : Run (blocks i) s n d t) :
    Run (machine Labels blocks first next) (embed Labels i s) n d (embed Labels i t) := by
  induction h with
  | nil => exact .nil _
  | cons he tail ih =>
    simpa only [delta_embed] using Run.cons (step Labels blocks first next he) ih

/-- The dispatcher is a literal one-edge finite transition, not a free jump. -/
theorem handoff {i j : I} (s : Config k Γ (Labels i)) (b : Bool)
    (halt : (blocks i).answer s=some b) (route : next i s.label b=some j) :
    Run (machine Labels blocks first next) (embed Labels i s) 1 (fun _ => 0)
      (embed Labels j ⟨(blocks j).start,s.tapes⟩) := by
  cases ha : (blocks i).transition s.label (fun j => (s.tapes j).head) with
  | halt c =>
    have hb : c=b := by simpa [Machine.answer,Machine.action,ha] using halt
    subst c
    have hs : (machine Labels blocks first next).step (embed Labels i s)=
        some (embed Labels j ⟨(blocks j).start,s.tapes⟩) := by
      simp [Machine.step,Machine.action,machine,embed,ha,route,Move.apply,Tape.write_self]
    simpa [delta,Machine.action,machine,embed,ha,route,Move.delta] using single hs
  | advance l w m => simp [Machine.answer,Machine.action,ha] at halt

theorem terminal {i : I} (s : Config k Γ (Labels i)) (b : Bool)
    (halt : (blocks i).answer s=some b) (route : next i s.label b=none) :
    (machine Labels blocks first next).answer (embed Labels i s)=some b := by
  cases ha : (blocks i).transition s.label (fun j => (s.tapes j).head) with
  | halt c =>
    have hb : c=b := by simpa [Machine.answer,Machine.action,ha] using halt
    subst c
    simp [Machine.answer,Machine.action,machine,embed,ha,route]
  | advance l w m => simp [Machine.answer,Machine.action,ha] at halt

end QecReliability.OracleCost.MultiTape.LabelRoutedNetwork
