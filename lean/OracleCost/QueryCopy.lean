import OracleCost.MachineObservations

/-! A concrete two-tape query copier. The finite control copies nonblank bits
from tape zero to the initially blank tape one, then rewinds both heads.
Every step is a transition of MultiTape.Machine, not a decorated list operation.
The proof uses lists only to describe the invariant of those actual tapes.
-/
namespace QecReliability.OracleCost.MultiTape.QueryCopy
open Turing

def copier : Machine 1 (Option Bool) (Fin 3) where
  start := 0
  inputSymbol := some
  input_injective := Option.some_injective _
  input_not_blank := fun _ => by simp
  transition label heads :=
    if label=0 then
      match heads 0 with
      | some b => .advance 0 (fun _ => some b) (fun _ => .right)
      | none => .advance 1 heads (fun _ => .left)
    else if label=1 then
      match heads 0 with
      | some _ => .advance 1 heads (fun _ => .left)
      | none => .advance 2 heads (fun _ => .right)
    else .halt true

def tape (left right : List Bool) : Tape (Option Bool) :=
  Tape.mk₂ (left.map some) (right.map some)

def copying (left right : List Bool) : Config 1 (Option Bool) (Fin 3) :=
  ⟨0,fun i => if i=0 then tape left right else tape left []⟩

def rewinding (left right : List Bool) : Config 1 (Option Bool) (Fin 3) :=
  ⟨1,fun _ => tape left right⟩

def sentinel (right : List Bool) : Config 1 (Option Bool) (Fin 3) :=
  ⟨1,fun _ => (tape [] right).move .left⟩

def finished (bits : List Bool) : Config 1 (Option Bool) (Fin 3) :=
  ⟨2,fun _ => tape [] bits⟩

theorem tape_head (left : List Bool) (b : Bool) (right : List Bool) :
    (tape left (b::right)).head=some b := rfl

theorem tape_empty_head (left : List Bool) : (tape left []).head=none := rfl

theorem tape_move_right (left right : List Bool) (b : Bool) :
    (tape left (b::right)).move .right=tape (b::left) right := by
  simp [tape,Tape.mk₂]

theorem tape_move_left (left right : List Bool) (b : Bool) :
    (tape (b::left) right).move .left=tape left (b::right) := by
  simp [tape,Tape.mk₂]

theorem tape_write_right (left : List Bool) (b : Bool) :
    ((tape left []).write (some b)).move .right=tape (b::left) [] := rfl

theorem copy_step (left right : List Bool) (b : Bool) :
    copier.step (copying left (b::right))=some (copying (b::left) right) := by
  simp only [Machine.step,Machine.action,copier,copying,↓reduceIte,tape_head]
  congr 1
  congr 1
  funext i
  by_cases hi : i=0
  · simp only [hi,↓reduceIte,Move.apply]
    exact tape_move_right left right b
  · simp only [hi,↓reduceIte,Move.apply,tape_write_right]

theorem rewind_step (left right : List Bool) (b a : Bool) :
    copier.step (rewinding (a::left) (b::right))=
      some (rewinding left (a::b::right)) := by
  simp only [Machine.step,Machine.action,copier,rewinding,Fin.isValue,Fin.reduceEq,
    ↓reduceIte,tape_head]
  congr 1

theorem rewind_origin (right : List Bool) (b : Bool) :
    copier.step (rewinding [] (b::right))=some (sentinel (b::right)) := by
  simp only [Machine.step,Machine.action,copier,rewinding,Fin.isValue,Fin.reduceEq,
    ↓reduceIte,tape_head]
  congr 1

theorem sentinel_step (right : List Bool) :
    copier.step (sentinel right)=some (finished right) := by
  have hh : ((tape [] right).move .left).head=none := rfl
  simp only [Machine.step,Machine.action,copier,sentinel,Fin.isValue,Fin.reduceEq,
    ↓reduceIte,hh]
  congr 1
  congr 1
  funext i
  change ((tape [] right).move .left |>.write none).move .right=tape [] right
  rw [← hh,Tape.write_self,Tape.move_left_right]

theorem copy_end (left : List Bool) :
    copier.step (copying left [])=
      some ⟨1,fun _ => (tape left []).move .left⟩ := by
  simp only [copying,ite_self,Machine.step,Machine.action,copier,↓reduceIte,tape_empty_head]
  congr 1

theorem CoreTrace.trans {s t u : Config 1 (Option Bool) (Fin 3)} {n m : ℕ}
    (h : MultiTape.CoreTrace copier s n t) (g : MultiTape.CoreTrace copier t m u) :
    MultiTape.CoreTrace copier s (n+m) u := by
  induction h with
  | nil => simpa using g
  | cons he _ ih => simpa only [Nat.add_right_comm] using MultiTape.CoreTrace.cons he (ih g)

theorem rewind_trace (left : List Bool) (b : Bool) (right : List Bool) :
    MultiTape.CoreTrace copier (rewinding left (b::right)) (left.length+2)
      (finished (left.reverse++b::right)) := by
  induction left generalizing b right with
  | nil =>
    simpa using MultiTape.CoreTrace.cons (rewind_origin right b)
      (MultiTape.CoreTrace.cons (sentinel_step (b::right)) (MultiTape.CoreTrace.nil _))
  | cons a left ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm] using
      MultiTape.CoreTrace.cons (rewind_step left right b a) (ih a (b::right))

theorem copy_trace (left right : List Bool) :
    MultiTape.CoreTrace copier (copying left right) (2*right.length+left.length+2)
      (finished (left.reverse++right)) := by
  induction right generalizing left with
  | nil =>
    cases left with
    | nil =>
      exact MultiTape.CoreTrace.cons (copy_end [])
        (MultiTape.CoreTrace.cons (sentinel_step []) (MultiTape.CoreTrace.nil _))
    | cons b left =>
      have hc : copier.step (copying (b::left) [])=some (rewinding left [b]) := by
        simpa only [tape_move_left,rewinding] using copy_end (b::left)
      simpa [List.reverse_cons] using MultiTape.CoreTrace.cons hc (rewind_trace left b [])
  | cons b right ih =>
    convert MultiTape.CoreTrace.cons (copy_step left right b) (ih (b::left)) using 1
    · simp only [List.length_cons]; omega
    · simp [List.reverse_cons,List.append_assoc]

/-- A uniform finite machine copies every finite bit string, including empty
input. Both final relative tapes contain exactly the original input. Time
below excludes halt inspection. Absolute origins need a separate coordinate
invariant before composition into a reusable global tape-space theorem. -/
theorem copy_correct (bits : List Bool) :
    MultiTape.CoreTrace copier (copier.initial bits) (2*bits.length+2) (finished bits) ∧
    copier.answer (finished bits)=some true := by
  have hi : copier.initial bits=copying [] bits := rfl
  rw [hi]
  exact ⟨by simpa using copy_trace [] bits,rfl⟩

/-- Actual completed execution, including halt inspection and an explicit
visited-cell bound. The list length is only in the proof, not a free register
or input length oracle in the copier's three-state transition table. -/
theorem copy_completed (bits : List Bool) :
    ∃ run : Completed copier bits, run.final.core=finished bits ∧
      run.time=2*bits.length+3 ∧ run.cells≤6*bits.length+6 := by
  obtain ⟨run,hf,ht,hspace⟩ := completed_of_core (copy_correct bits).1 (copy_correct bits).2
  exact ⟨run,hf,by omega,hspace.trans (by omega)⟩

end QecReliability.OracleCost.MultiTape.QueryCopy
