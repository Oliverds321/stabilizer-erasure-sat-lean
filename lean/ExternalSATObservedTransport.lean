import ExternalSATPrimitiveTransport
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.VisitedTape
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Fin

/-! Same-word passive-observation transport. Observations are proof-level only:
none are accessible to the finite machine's transition function. This module
adds no SAT-engine or preprocessing hypothesis. Pending compiler verification. -/
namespace QecReliability.ExternalSATBridge.PrimitiveTransport

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open scoped BigOperators

abbrev TargetObserved (M : Computation.PrimitiveMachine) :=
  MultiTape.Observed M.tapeCount (Option Bool) (Control M)

def idle (M : Computation.PrimitiveMachine) : Fin (M.tapeCount + 1) := M.inputTape.succ

@[simp] theorem idle_ne_zero (M : Computation.PrimitiveMachine) : idle M ≠ 0 := by
  simp [idle]

@[simp] theorem slot_ne_idle (M : Computation.PrimitiveMachine) (i : Fin M.tapeCount) :
    slot M i ≠ idle M := by
  by_cases hi : i = M.inputTape
  · simp only [slot, if_pos hi]
    exact (idle_ne_zero M).symm
  · simp [slot, hi, idle]

theorem sum_slots (M : Computation.PrimitiveMachine) (f : Fin (M.tapeCount + 1) → ℕ) :
    (∑ j, f j) = f (idle M) + ∑ i, f (slot M i) := by
  let σ := Equiv.swap (0 : Fin (M.tapeCount + 1)) (idle M)
  have hσ : (∑ j, f (σ j)) = ∑ j, f j :=
    Equiv.Perm.sum_comp σ Finset.univ f (by intro j hj; exact Finset.mem_univ j)
  rw [← hσ, Fin.sum_univ_succ]
  have hzero : σ 0 = idle M := by simp [σ]
  have hsucc : ∀ i : Fin M.tapeCount, σ i.succ = slot M i := by
    intro i
    by_cases hi : i = M.inputTape
    · subst i
      simp [σ, idle, slot]
    · have hni : i.succ ≠ idle M := by simpa [idle] using hi
      simp [σ, Equiv.swap_apply_def, hni, slot, hi]
  simp only [hzero, hsucc]

/-- Physical source head displacement; used only in the ghost invariant. -/
def displacement (M : Computation.PrimitiveMachine) (c : M.Cfg) (i : Fin M.tapeCount) : ℤ :=
  match c.state with
  | .inl _ => 0
  | .inr q =>
    match M.transition q (c.tapes (M.scan q)).head with
    | .inl _ => 0
    | .inr result => if i = M.scan q then headDisplacement result.2 else 0

@[simp] theorem commandMove_delta (a : Turing.TM0.Stmt (Option Bool)) :
    (commandMove a).delta = headDisplacement a := by
  cases a with
  | write b => rfl
  | move d => cases d <;> rfl

theorem located_position_step {M : Computation.PrimitiveMachine} {e e' : LocatedCfg M}
    (hs : locatedStep M e = some e') (i : Fin M.tapeCount) :
    e'.position i = e.position i + displacement M e.config i := by
  obtain ⟨config, _, rfl⟩ := Option.map_eq_some_iff.mp hs
  cases hstate : e.config.state with
  | inl b => simp [LocatedCfg.monitor, displacement, hstate]
  | inr q =>
    cases ht : M.transition q (e.config.tapes (M.scan q)).head with
    | inl b => simp [LocatedCfg.monitor, displacement, hstate, ht]
    | inr result =>
      obtain ⟨next, a⟩ := result
      by_cases hi : i = M.scan q
      · subst i
        simp [LocatedCfg.monitor, displacement, hstate, ht]
      · simp [LocatedCfg.monitor, displacement, hstate, ht, hi]

theorem observed_step_map_core (M : Computation.PrimitiveMachine) (s : TargetObserved M) :
    (MultiTape.observedStep (machine M) s).map MultiTape.Observed.core =
      (machine M).step s.core := by
  cases ha : (machine M).action s.core <;>
    simp [MultiTape.observedStep, MultiTape.Machine.step, ha]

theorem observed_step_lift {M : Computation.PrimitiveMachine} (s : TargetObserved M)
    {c : TargetConfig M} (hs : (machine M).step s.core = some c) :
    ∃ s', MultiTape.observedStep (machine M) s = some s' ∧ s'.core = c := by
  apply Option.map_eq_some_iff.mp
  rw [observed_step_map_core, hs]

theorem observed_visited_step {M : Computation.PrimitiveMachine} {s s' : TargetObserved M}
    (hs : MultiTape.observedStep (machine M) s = some s') (j : Fin (M.tapeCount + 1)) :
    s'.visited j = insert (s'.position j) (s.visited j) := by
  cases ha : (machine M).action s.core with
  | halt b => simp [MultiTape.observedStep, ha] at hs
  | advance label write move =>
    simp only [MultiTape.observedStep, ha, Option.some.injEq] at hs
    subst s'
    rfl

theorem observed_position_step {M : Computation.PrimitiveMachine} {s s' : TargetObserved M}
    (hs : MultiTape.observedStep (machine M) s = some s') (i : Fin M.tapeCount) :
    s'.position (slot M i) = s.position (slot M i) + displacement M (project M s.core) i := by
  cases hstate : s.core.label with
  | inl b => simp [MultiTape.observedStep, MultiTape.Machine.action, machine, hstate] at hs
  | inr q =>
    cases ht : M.transition q (s.core.tapes (slot M (M.scan q))).head with
    | inl b =>
      simp only [MultiTape.observedStep, MultiTape.Machine.action, machine, hstate, ht,
        Option.some.injEq] at hs
      subst s'
      simp [displacement, project, hstate, ht, MultiTape.Move.delta]
    | inr result =>
      obtain ⟨next, a⟩ := result
      simp only [MultiTape.observedStep, MultiTape.Machine.action, machine, hstate, ht,
        Option.some.injEq] at hs
      subst s'
      by_cases hi : i = M.scan q
      · subst i
        simp [displacement, project, hstate, ht, moves]
      · simp [displacement, project, hstate, ht, moves, hi, MultiTape.Move.delta]

theorem observed_idle_step {M : Computation.PrimitiveMachine} {s s' : TargetObserved M}
    (hs : MultiTape.observedStep (machine M) s = some s') :
    s'.position (idle M) = s.position (idle M) := by
  cases hstate : s.core.label with
  | inl b => simp [MultiTape.observedStep, MultiTape.Machine.action, machine, hstate] at hs
  | inr q =>
    cases ht : M.transition q (s.core.tapes (slot M (M.scan q))).head with
    | inl b =>
      simp only [MultiTape.observedStep, MultiTape.Machine.action, machine, hstate, ht,
        Option.some.injEq] at hs
      subst s'
      simp [MultiTape.Move.delta]
    | inr result =>
      obtain ⟨next, a⟩ := result
      simp only [MultiTape.observedStep, MultiTape.Machine.action, machine, hstate, ht,
        Option.some.injEq] at hs
      subst s'
      have hne : idle M ≠ slot M (M.scan q) := (slot_ne_idle M _).symm
      simp [moves, hne, MultiTape.Move.delta]

structure Related (M : Computation.PrimitiveMachine) (e : LocatedCfg M)
    (s : TargetObserved M) : Prop where
  core : project M s.core = e.config
  position : ∀ i, s.position (slot M i) = e.position i
  bounded : ∀ i z, z ∈ s.visited (slot M i) → e.lower i ≤ z ∧ z ≤ e.upper i
  enclosed : ∀ i, e.lower i ≤ e.position i ∧ e.position i ≤ e.upper i
  idle_position : s.position (idle M) = 0
  idle_visited : s.visited (idle M) = {0}

theorem related_initial (M : Computation.PrimitiveMachine) (bits : List Bool) :
    Related M (locatedInit M bits) (MultiTape.initialObserved (machine M) bits) := by
  refine ⟨project_initial M bits, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; rfl
  · intro i z hz
    by_cases hi : i = M.inputTape
    · subst i
      rw [(slot_eq_zero M M.inputTape).mpr rfl] at hz
      change z ∈ (insert (0 : ℤ)
        ((Finset.range bits.length).image (fun j : ℕ => (j : ℤ)))) at hz
      rcases Finset.mem_insert.mp hz with hz | hz
      · subst z
        simp [locatedInit]
      · obtain ⟨j, hj, hz⟩ := Finset.mem_image.mp hz
        have hj' := Finset.mem_range.mp hj
        subst z
        simp only [locatedInit, if_pos rfl, Int.ofNat_eq_natCast, ↓reduceIte]
        omega
    · have hslot : slot M i ≠ 0 := fun h0 => hi ((slot_eq_zero M i).mp h0)
      simp only [MultiTape.initialObserved, if_neg hslot, Finset.mem_singleton] at hz
      subst z
      simp [locatedInit, hi]
  · intro i
    simp only [locatedInit, Int.ofNat_eq_natCast]
    split_ifs <;> omega
  · rfl
  · simp [MultiTape.initialObserved]

theorem related_step {M : Computation.PrimitiveMachine} {e e' : LocatedCfg M}
    {s : TargetObserved M} (h : Related M e s) (he : locatedStep M e = some e') :
    ∃ s', MultiTape.observedStep (machine M) s = some s' ∧ Related M e' s' := by
  have hc : M.step (project M s.core) = some e'.config := by
    rw [h.core]
    exact locatedStep_config he
  obtain ⟨c', hstep, hproj⟩ := lift_step hc
  obtain ⟨s', hs, hsc⟩ := observed_step_lift s hstep
  have hp : ∀ i, s'.position (slot M i) = e'.position i := by
    intro i
    rw [observed_position_step hs, h.position, h.core, located_position_step he]
  have henc := locatedStep_encloses he h.enclosed
  have hip : s'.position (idle M) = 0 := (observed_idle_step hs).trans h.idle_position
  refine ⟨s', hs, ⟨?_, hp, ?_, henc, hip, ?_⟩⟩
  · rw [hsc]
    exact hproj
  · intro i z hz
    rw [observed_visited_step hs] at hz
    rcases Finset.mem_insert.mp hz with hz | hz
    · subst z
      rw [hp]
      exact henc i
    · have hb := h.bounded i z hz
      have hex := locatedStep_expands he i
      exact ⟨hex.1.trans hb.1, hb.2.trans hex.2⟩
  · rw [observed_visited_step hs, hip, h.idle_visited]
    simp

theorem lift_observedTrace (M : Computation.PrimitiveMachine)
    {a b : LocatedCfg M} {n : ℕ} (tr : Computation.Trace (locatedStep M) n a b)
    (s : TargetObserved M) (h : Related M a s) :
    ∃ s', MultiTape.Trace (machine M) s n s' ∧ Related M b s' := by
  induction tr generalizing s with
  | refl a => exact ⟨s, .nil s, h⟩
  | @cons n a a' b he ht ih =>
    obtain ⟨s', hs, hrel⟩ := related_step h he
    obtain ⟨last, htrace, hlast⟩ := ih s' hrel
    exact ⟨last, .cons hs htrace, hlast⟩

theorem bounded_card {V : Finset ℤ} {lo hi : ℤ}
    (h : ∀ z ∈ V, lo ≤ z ∧ z ≤ hi) : V.card ≤ (hi - lo + 1).toNat := by
  have hsub : V ⊆ Finset.Icc lo hi := fun z hz => Finset.mem_Icc.mpr (h z hz)
  have hc := Finset.card_le_card hsub
  rw [Int.card_Icc] at hc
  have heq : hi + 1 - lo = hi - lo + 1 := by omega
  simpa only [heq] using hc

theorem Related.cells {M : Computation.PrimitiveMachine} {e : LocatedCfg M}
    {s : TargetObserved M} (h : Related M e s) :
    MultiTape.visitedCells s ≤ visitedSpace e + 1 := by
  unfold MultiTape.visitedCells
  rw [sum_slots M, h.idle_visited, Finset.card_singleton]
  have hb : (∑ i, (s.visited (slot M i)).card) ≤ visitedSpace e :=
    Finset.sum_le_sum (fun i _ => bounded_card (h.bounded i))
  omega

/-- The very same input word and exactly the source transitions, plus the
native final halt inspection. No frontend-machine resource claim is made. -/
theorem completed_run (M : Computation.PrimitiveMachine) (bits : List Bool)
    (answer : Bool) (n : ℕ) (final : LocatedCfg M)
    (tr : Computation.Trace (locatedStep M) n (locatedInit M bits) final)
    (halt : final.config.state = .inl answer) :
    ∃ run : MultiTape.Completed (machine M) bits,
      run.output = answer ∧ run.time = n + 1 ∧ run.cells ≤ visitedSpace final + 1 := by
  obtain ⟨s, hs, hrel⟩ := lift_observedTrace M tr
    (MultiTape.initialObserved (machine M) bits) (related_initial M bits)
  have hstate : s.core.label = .inl answer :=
    (congrArg Computation.PrimitiveMachine.Cfg.state hrel.core).trans halt
  let run : MultiTape.Completed (machine M) bits :=
    ⟨n, s, answer, hs, answer_of_halting_label M s.core answer hstate⟩
  exact ⟨run, rfl, rfl, hrel.cells⟩

end QecReliability.ExternalSATBridge.PrimitiveTransport
