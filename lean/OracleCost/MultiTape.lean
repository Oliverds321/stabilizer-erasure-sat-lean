import Mathlib.Computability.TuringMachine.Tape
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Range
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Fixed finite-alphabet, finite-control, multiple two-way tape machines.
One transition reads all heads, writes one symbol per tape, and moves each head
at most one cell. The number of tapes is a machine constant. Head coordinates
and visited sets below are ghost observations: the transition table cannot
read them. They supply physical visited-cell accounting, not a free runtime
oracle for available space. No single-tape polynomial simulation is invoked.
-/
namespace QecReliability.OracleCost.MultiTape
open Turing

inductive Move where
  | left | stay | right
  deriving DecidableEq

instance : Fintype Move := ⟨{.left,.stay,.right},by intro m; cases m <;> simp⟩

def Move.delta : Move → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

def Move.apply {Γ : Type*} [Inhabited Γ] : Move → Tape Γ → Tape Γ
  | .left,t => t.move .left
  | .stay,t => t
  | .right,t => t.move .right

inductive Action (k : ℕ) (Γ Λ : Type*) where
  | halt (answer : Bool)
  | advance (label : Λ) (write : Fin (k+1) → Γ) (move : Fin (k+1) → Move)

structure Machine (k : ℕ) (Γ Λ : Type*) [Fintype Γ] [Inhabited Γ] [Fintype Λ] where
  start : Λ
  inputSymbol : Bool → Γ
  input_injective : Function.Injective inputSymbol
  input_not_blank : ∀ b, inputSymbol b≠default
  transition : Λ → (Fin (k+1) → Γ) → Action k Γ Λ

structure Config (k : ℕ) (Γ Λ : Type*) [Inhabited Γ] where
  label : Λ
  tapes : Fin (k+1) → Tape Γ

variable {k : ℕ} {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ] [Fintype Λ]

def Machine.action (M : Machine k Γ Λ) (s : Config k Γ Λ) : Action k Γ Λ :=
  M.transition s.label (fun i => (s.tapes i).head)

def Machine.initial (M : Machine k Γ Λ) (bits : List Bool) : Config k Γ Λ :=
  ⟨M.start,fun i => if i=0 then Tape.mk₁ (bits.map M.inputSymbol) else default⟩

def Machine.step (M : Machine k Γ Λ) (s : Config k Γ Λ) : Option (Config k Γ Λ) :=
  match M.action s with
  | .halt _ => none
  | .advance label write move =>
    some ⟨label,fun i => (move i).apply ((s.tapes i).write (write i))⟩

def Machine.answer (M : Machine k Γ Λ) (s : Config k Γ Λ) : Option Bool :=
  match M.action s with
  | .halt b => some b
  | .advance _ _ _ => none

theorem Machine.halt_iff (M : Machine k Γ Λ) (s : Config k Γ Λ) :
    M.step s=none ↔ ∃ b, M.answer s=some b := by
  cases h : M.action s <;> simp [Machine.step,Machine.answer,h]

omit [Inhabited Γ] in
/-- The transition-table domain is finite, with this exact number of entries.
There is no unbounded internal register hidden in a transition callback. -/
theorem Machine.table_entries :
    Fintype.card (Λ × (Fin (k+1) → Γ))=Fintype.card Λ*(Fintype.card Γ)^(k+1) := by
  simp

inductive CoreTrace (M : Machine k Γ Λ) : Config k Γ Λ → ℕ → Config k Γ Λ → Prop
  | nil (s) : CoreTrace M s 0 s
  | cons {s t u n} (h : M.step s=some t) (tail : CoreTrace M t n u) :
      CoreTrace M s (n+1) u

structure Observed (k : ℕ) (Γ Λ : Type*) [Inhabited Γ] where
  core : Config k Γ Λ
  position : Fin (k+1) → ℤ
  visited : Fin (k+1) → Finset ℤ

def initialObserved (M : Machine k Γ Λ) (bits : List Bool) : Observed k Γ Λ :=
  ⟨M.initial bits,fun _ => 0,fun i =>
    if i=0 then insert 0 ((Finset.range bits.length).image (fun j : ℕ => (j : ℤ)))
    else {0}⟩

def observedStep (M : Machine k Γ Λ) (s : Observed k Γ Λ) : Option (Observed k Γ Λ) :=
  match M.action s.core with
  | .halt _ => none
  | .advance label write move =>
    let pos := fun i => s.position i+(move i).delta
    some ⟨⟨label,fun i => (move i).apply ((s.core.tapes i).write (write i))⟩,
      pos,fun i => insert (pos i) (s.visited i)⟩

theorem observedStep_core {M : Machine k Γ Λ} {s t : Observed k Γ Λ}
    (h : observedStep M s=some t) : M.step s.core=some t.core := by
  cases ha : M.action s.core with
  | halt b => simp [observedStep,ha] at h
  | advance label write move =>
    simp only [observedStep,ha,Option.some.injEq] at h
    subst t
    simp [Machine.step,ha]

theorem observedStep_mono {M : Machine k Γ Λ} {s t : Observed k Γ Λ}
    (h : observedStep M s=some t) : ∀ i, s.visited i⊆t.visited i := by
  cases ha : M.action s.core with
  | halt b => simp [observedStep,ha] at h
  | advance label write move =>
    simp only [observedStep,ha,Option.some.injEq] at h
    subst t
    intro i
    exact Finset.subset_insert _ _

theorem observedStep_head_mem {M : Machine k Γ Λ} {s t : Observed k Γ Λ}
    (h : observedStep M s=some t) : ∀ i, t.position i∈t.visited i := by
  cases ha : M.action s.core with
  | halt b => simp [observedStep,ha] at h
  | advance label write move =>
    simp only [observedStep,ha,Option.some.injEq] at h
    subst t
    intro i
    exact Finset.mem_insert_self _ _

inductive Trace (M : Machine k Γ Λ) : Observed k Γ Λ → ℕ → Observed k Γ Λ → Prop
  | nil (s) : Trace M s 0 s
  | cons {s t u n} (h : observedStep M s=some t) (tail : Trace M t n u) :
      Trace M s (n+1) u

theorem Trace.erase {M : Machine k Γ Λ} {s t : Observed k Γ Λ} {n : ℕ}
    (h : Trace M s n t) : CoreTrace M s.core n t.core := by
  induction h with
  | nil => exact .nil _
  | cons he _ ih => exact .cons (observedStep_core he) ih

theorem Trace.visited_mono {M : Machine k Γ Λ} {s t : Observed k Γ Λ} {n : ℕ}
    (h : Trace M s n t) : ∀ i, s.visited i⊆t.visited i := by
  induction h with
  | nil => exact fun _ => Finset.Subset.refl _
  | cons he _ ih => exact fun i => (observedStep_mono he i).trans (ih i)

def visitedCells (s : Observed k Γ Λ) : ℕ := ∑ i, (s.visited i).card

theorem Trace.space_mono {M : Machine k Γ Λ} {s t : Observed k Γ Λ} {n : ℕ}
    (h : Trace M s n t) : visitedCells s≤visitedCells t := by
  exact Finset.sum_le_sum (fun i _ => Finset.card_le_card (h.visited_mono i))

/-- The complete finite execution is a witness about the fixed bit machine.
It is not retained by that machine. Time includes the final halt inspection. -/
structure Completed (M : Machine k Γ Λ) (bits : List Bool) where
  transitions : ℕ
  final : Observed k Γ Λ
  output : Bool
  trace : Trace M (initialObserved M bits) transitions final
  halt : M.answer final.core=some output

def Completed.time {M : Machine k Γ Λ} {bits : List Bool}
    (run : Completed M bits) : ℕ := run.transitions+1

def Completed.cells {M : Machine k Γ Λ} {bits : List Bool}
    (run : Completed M bits) : ℕ := visitedCells run.final

theorem Completed.core_run {M : Machine k Γ Λ} {bits : List Bool}
    (run : Completed M bits) :
    CoreTrace M (M.initial bits) run.transitions run.final.core ∧
      M.step run.final.core=none :=
  ⟨run.trace.erase,(M.halt_iff _).mpr ⟨run.output,run.halt⟩⟩

theorem observedStep_halt {M : Machine k Γ Λ} {s : Observed k Γ Λ}
    (h : M.step s.core=none) : observedStep M s=none := by
  cases ha : M.action s.core <;> simp_all [Machine.step,observedStep]

/-- Finite completed runs of this deterministic machine have unique final
observations and length; choosing a proof witness does not choose an execution. -/
theorem Trace.terminal_unique {M : Machine k Γ Λ} {s t u : Observed k Γ Λ}
    {n m : ℕ} (h : Trace M s n t) (g : Trace M s m u)
    (ht : observedStep M t=none) (hu : observedStep M u=none) : t=u ∧ n=m := by
  induction h generalizing m u with
  | nil s =>
    cases g with
    | nil => exact ⟨rfl,rfl⟩
    | cons he _ => rw [ht] at he; cases he
  | @cons s v t n he tail ih =>
    cases g with
    | nil => rw [hu] at he; cases he
    | @cons _ v' _ m he' tail' =>
      have hv : v=v' := Option.some.inj (he.symm.trans he')
      subst v'
      obtain ⟨hf,hn⟩ := ih tail' ht hu
      exact ⟨hf,congrArg (·+1) hn⟩

theorem Completed.unique {M : Machine k Γ Λ} {bits : List Bool}
    (a b : Completed M bits) :
    a.final=b.final ∧ a.time=b.time ∧ a.cells=b.cells ∧ a.output=b.output := by
  obtain ⟨hf,hn⟩ := a.trace.terminal_unique b.trace
    (observedStep_halt a.core_run.2) (observedStep_halt b.core_run.2)
  refine ⟨hf,congrArg (·+1) hn,congrArg visitedCells hf,?_⟩
  have ha := a.halt
  rw [hf,b.halt] at ha
  exact (Option.some.inj ha).symm

end QecReliability.OracleCost.MultiTape
