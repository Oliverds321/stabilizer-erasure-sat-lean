import OracleCost.MultiTape
import OAI.Algorithms.SubexponentialSAT.Computation

/-! Concrete same-word primitive-machine adapter. This file uses the actual
external PrimitiveMachine and internal MultiTape.Machine, not a new abstract
engine assumption. Intended for the isolated common4.34.1 probe. The source
below is pending compiler verification. Visited-space and completed-trace
transport are intentionally not claimed by this first transition milestone.
-/
namespace QecReliability.ExternalSATBridge.PrimitiveTransport

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT

abbrev Control (M : Computation.PrimitiveMachine) := Bool ⊕ Fin M.stateCount
abbrev TargetConfig (M : Computation.PrimitiveMachine) :=
  MultiTape.Config M.tapeCount (Option Bool) (Control M)

/-- Source input goes to target tape0; one of the t+1 target tapes is idle. -/
def slot (M : Computation.PrimitiveMachine) (i : Fin M.tapeCount) : Fin (M.tapeCount + 1) :=
  if i = M.inputTape then 0 else i.succ

theorem slot_injective (M : Computation.PrimitiveMachine) : Function.Injective (slot M) := by
  intro i j h
  by_cases hi : i = M.inputTape
  · by_cases hj : j = M.inputTape
    · exact hi.trans hj.symm
    · have hh := congrArg Fin.val h
      simp [slot, hi, hj] at hh
  · by_cases hj : j = M.inputTape
    · have hh := congrArg Fin.val h
      simp [slot, hi, hj] at hh
    · apply Fin.ext
      have hh := congrArg Fin.val h
      simpa [slot, hi, hj] using hh

@[simp] theorem slot_eq_slot (M : Computation.PrimitiveMachine) (i j : Fin M.tapeCount) :
    slot M i = slot M j ↔ i = j := (slot_injective M).eq_iff

@[simp] theorem slot_eq_zero (M : Computation.PrimitiveMachine) (i : Fin M.tapeCount) :
    slot M i = 0 ↔ i = M.inputTape := by
  by_cases hi : i = M.inputTape
  · simp [slot, hi]
  · simp [slot, hi]

def commandWrite (a : Turing.TM0.Stmt (Option Bool)) (old : Option Bool) : Option Bool :=
  match a with
  | .write b => b
  | .move _ => old

def commandMove : Turing.TM0.Stmt (Option Bool) → MultiTape.Move
  | .write _ => .stay
  | .move .left => .left
  | .move .right => .right

def writes (M : Computation.PrimitiveMachine) (i : Fin M.tapeCount)
    (a : Turing.TM0.Stmt (Option Bool))
    (heads : Fin (M.tapeCount + 1) → Option Bool) : Fin (M.tapeCount + 1) → Option Bool :=
  fun j => if j = slot M i then commandWrite a (heads j) else heads j

def moves (M : Computation.PrimitiveMachine) (i : Fin M.tapeCount)
    (a : Turing.TM0.Stmt (Option Bool)) : Fin (M.tapeCount + 1) → MultiTape.Move :=
  fun j => if j = slot M i then commandMove a else .stay

def machine (M : Computation.PrimitiveMachine) :
    MultiTape.Machine M.tapeCount (Option Bool) (Control M) where
  start := .inr M.start
  inputSymbol := some
  input_injective := fun _ _ h => Option.some.inj h
  input_not_blank := by intro b; simp
  transition state heads :=
    match state with
    | .inl answer => .halt answer
    | .inr q =>
      match M.transition q (heads (slot M (M.scan q))) with
      | .inl answer => .advance (.inl answer) heads (fun _ => .stay)
      | .inr (q', action) =>
        .advance (.inr q') (writes M (M.scan q) action heads) (moves M (M.scan q) action)

def project (M : Computation.PrimitiveMachine) (c : TargetConfig M) : M.Cfg :=
  ⟨c.label, fun i => c.tapes (slot M i)⟩

def perform (a : Turing.TM0.Stmt (Option Bool))
    (t : Turing.Tape (Option Bool)) : Turing.Tape (Option Bool) :=
  match a with
  | .write b => t.write b
  | .move d => t.move d

/-- The finite target transition updates exactly the source-selected tape.
Writing an unchanged head on an inactive tape is mathematically the identity. -/
theorem tapes_projection (M : Computation.PrimitiveMachine) (i : Fin M.tapeCount)
    (a : Turing.TM0.Stmt (Option Bool))
    (tapes : Fin (M.tapeCount + 1) → Turing.Tape (Option Bool)) :
    (fun j => (moves M i a (slot M j)).apply
      ((tapes (slot M j)).write (writes M i a (fun k => (tapes k).head) (slot M j)))) =
      Function.update (fun j => tapes (slot M j)) i (perform a (tapes (slot M i))) := by
  funext j
  by_cases hj : j = i
  · subst j
    cases a with
    | write b => simp [writes, moves, commandWrite, commandMove, perform, MultiTape.Move.apply]
    | move d => cases d <;>
        simp [writes, moves, commandWrite, commandMove, perform, MultiTape.Move.apply]
  · cases a with
    | write b => simp [writes, moves, hj, commandWrite, commandMove, perform, MultiTape.Move.apply]
    | move d => cases d <;>
        simp [writes, moves, hj, commandWrite, commandMove, perform, MultiTape.Move.apply]

theorem project_initial (M : Computation.PrimitiveMachine) (bits : List Bool) :
    project M ((machine M).initial bits) = M.init bits := by
  unfold project MultiTape.Machine.initial Computation.PrimitiveMachine.init
  change (⟨Sum.inr M.start, fun i =>
    if slot M i = 0 then Turing.Tape.mk₁ (bits.map some) else default⟩ : M.Cfg) =
    ⟨Sum.inr M.start, fun i =>
    if i = M.inputTape then Turing.Tape.mk₁ (bits.map some) else Turing.Tape.mk₁ []⟩
  congr 1
  funext i
  by_cases hi : i = M.inputTape
  · simp [hi]
  · simp only [slot_eq_zero, if_neg hi]
    rfl

/-- Every target core step projects to the same single external primitive step,
including the transition into a Boolean halting state. -/
theorem project_step (M : Computation.PrimitiveMachine) (c : TargetConfig M) :
    ((machine M).step c).map (project M) = M.step (project M c) := by
  cases hc : c.label with
  | inl answer =>
    simp [MultiTape.Machine.step, MultiTape.Machine.action, machine, project,
      Computation.PrimitiveMachine.step, hc]
  | inr q =>
    cases ht : M.transition q (c.tapes (slot M (M.scan q))).head with
    | inl answer =>
      simp [MultiTape.Machine.step, MultiTape.Machine.action, machine, project,
        Computation.PrimitiveMachine.step, hc, ht, MultiTape.Move.apply]
    | inr pair =>
      obtain ⟨q', action⟩ := pair
      simp only [MultiTape.Machine.step, MultiTape.Machine.action, machine, hc, project,
        Computation.PrimitiveMachine.step, ht, Option.map_some]
      congr 2
      cases action with
      | move direction =>
        simpa only [perform] using tapes_projection M (M.scan q) (.move direction) c.tapes
      | write symbol =>
        simpa only [perform] using tapes_projection M (M.scan q) (.write symbol) c.tapes

theorem lift_step {M : Computation.PrimitiveMachine} {c : TargetConfig M} {d : M.Cfg}
    (hs : M.step (project M c) = some d) :
    ∃ c', (machine M).step c = some c' ∧ project M c' = d := by
  have hp := project_step M c
  rw [hs] at hp
  cases ht : (machine M).step c with
  | none => simp [ht] at hp
  | some c' =>
    refine ⟨c', by simp [ht], ?_⟩
    simpa [ht] using hp

/-- Forward existence, not only projection: every genuine external primitive
trace has a target core trace with exactly the same number of transitions. -/
theorem lift_coreTrace (M : Computation.PrimitiveMachine) {a b : M.Cfg} {n : ℕ}
    (tr : Computation.Trace M.step n a b) (c : TargetConfig M) (hc : project M c = a) :
    ∃ d, MultiTape.CoreTrace (machine M) c n d ∧ project M d = b := by
  induction tr generalizing c with
  | refl a => exact ⟨c, .nil c, hc⟩
  | @cons n a a' b hs ht ih =>
    have hs' : M.step (project M c) = some a' := by rwa [hc]
    obtain ⟨c', hstep, hproj⟩ := lift_step hs'
    obtain ⟨d, htrace, hd⟩ := ih c' hproj
    exact ⟨d, .cons hstep htrace, hd⟩

theorem answer_of_halting_label (M : Computation.PrimitiveMachine) (c : TargetConfig M)
    (b : Bool) (hc : c.label = .inl b) : (machine M).answer c = some b := by
  simp [MultiTape.Machine.answer, MultiTape.Machine.action, machine, hc]

theorem finite_core_run (M : Computation.PrimitiveMachine) (bits : List Bool)
    (answer : Bool) (time : ℕ) (final : M.Cfg)
    (tr : Computation.Trace M.step time (M.init bits) final)
    (halt : final.state = .inl answer) :
    ∃ c, MultiTape.CoreTrace (machine M) ((machine M).initial bits) time c ∧
      (machine M).answer c = some answer := by
  obtain ⟨c, htrace, hc⟩ :=
    lift_coreTrace M tr ((machine M).initial bits) (project_initial M bits)
  refine ⟨c, htrace, answer_of_halting_label M c answer ?_⟩
  have hstate := congrArg Computation.PrimitiveMachine.Cfg.state hc
  exact hstate.trans halt

end QecReliability.ExternalSATBridge.PrimitiveTransport
