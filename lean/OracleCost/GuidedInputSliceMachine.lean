import OracleCost.TraceDisplacementCandidate
import OracleCost.QueryCopy

/-! Actual fixed-width stream parsing, controlled by a preserved tape word.
Copy advances input/guide/target; rewind advances ONLY guide/target back to
origin. Blank input before the guide delimiter halts false, never pads a byte.
This is distinct from FixedWidthField's source-restoring/output-advancing API. -/
namespace QecReliability.OracleCost.MultiTape.GuidedInputSlice
open Turing Displacement
variable {k : ℕ} {Λ : Type} [Fintype Λ]
abbrev Label (Λ : Type) := Bool ⊕ Λ
abbrev tape := QueryCopy.tape

def attach (M : Machine k (Option Bool) Λ) (source guide target : Fin (k+1)) :
    Machine k (Option Bool) (Label Λ) where
  start := .inl false
  inputSymbol := M.inputSymbol
  input_injective := M.input_injective
  input_not_blank := M.input_not_blank
  transition label heads := match label with
    | .inl false => match heads guide with
      | some _ => match heads source with
        | none => .halt false
        | some b => .advance (.inl false)
            (fun j => if j=target then some b else heads j)
            (fun j => if j=source ∨ j=guide ∨ j=target then .right else .stay)
      | none => .advance (.inl true) heads
          (fun j => if j=guide ∨ j=target then .left else .stay)
    | .inl true => match heads guide with
      | some _ => .advance (.inl true) heads
          (fun j => if j=guide ∨ j=target then .left else .stay)
      | none => .advance (.inr M.start) heads
          (fun j => if j=guide ∨ j=target then .right else .stay)
    | .inr state => match M.transition state heads with
      | .halt b => .halt b
      | .advance next write move => .advance (.inr next) write move

def frame (source guide target : Fin (k+1)) (others : Fin (k+1) → Tape (Option Bool))
    (label : Label Λ) (s g t : Tape (Option Bool)) : Config k (Option Bool) (Label Λ) :=
  ⟨label,fun j => if j=source then s else if j=guide then g else if j=target then t else others j⟩

def copying (source guide target : Fin (k+1)) (others : Fin (k+1) → Tape (Option Bool)) (sl sr gl gr out : List Bool) :
    Config k (Option Bool) (Label Λ) :=
  frame source guide target others (.inl false) (tape sl sr) (tape gl gr) (tape out [])

def rewindStart (source guide target : Fin (k+1)) (others : Fin (k+1) → Tape (Option Bool)) (s : Tape (Option Bool))
    (gl gr tl tr : List Bool) : Config k (Option Bool) (Label Λ) :=
  frame source guide target others (.inl true) s ((tape gl gr).move .left) ((tape tl tr).move .left)

def finished (M : Machine k (Option Bool) Λ) (source guide target : Fin (k+1)) (others : Fin (k+1) → Tape (Option Bool))
    (s : Tape (Option Bool)) (g t : List Bool) : Config k (Option Bool) (Label Λ) :=
  frame source guide target others (.inr M.start) s (tape [] g) (tape [] t)

def offsets (source guide target : Fin (k+1)) (a b : ℤ) (j : Fin (k+1)) : ℤ :=
  if j=source then a else if j=guide ∨ j=target then b else 0

def embed (s : Config k (Option Bool) Λ) : Config k (Option Bool) (Label Λ) := ⟨.inr s.label,s.tapes⟩

variable (M : Machine k (Option Bool) Λ) (source guide target : Fin (k+1))
variable (hsep : source≠guide ∧ source≠target ∧ guide≠target)
variable (others : Fin (k+1) → Tape (Option Bool))
include hsep

theorem copy_step (sl sr gl gr out : List Bool) (b c : Bool) :
    (attach M source guide target).step (copying source guide target others sl (b::sr) gl (c::gr) out)=
      some (copying source guide target others (b::sl) sr (c::gl) gr (b::out)) := by
  simp only [Machine.step,Machine.action,attach,copying,frame,hsep.1,Ne.symm hsep.1,
    hsep.2.1,Ne.symm hsep.2.1,hsep.2.2,Ne.symm hsep.2.2,↓reduceIte,QueryCopy.tape_head]
  congr 1; congr 1; funext j
  by_cases hs : j=source <;> by_cases hg : j=guide <;> by_cases ht : j=target <;>
    simp_all [Move.apply,Tape.write_self,QueryCopy.tape_move_right,QueryCopy.tape_write_right]

theorem copy_end (sl sr gl out : List Bool) :
    (attach M source guide target).step (copying source guide target others sl sr gl [] out)=
      some (rewindStart source guide target others (tape sl sr) gl [] out []) := by
  simp only [Machine.step,Machine.action,attach,copying,rewindStart,frame,hsep.1,Ne.symm hsep.1,
    hsep.2.1,Ne.symm hsep.2.1,hsep.2.2,Ne.symm hsep.2.2,↓reduceIte,QueryCopy.tape_empty_head]
  congr 1; congr 1; funext j
  by_cases hs : j=source <;> by_cases hg : j=guide <;> by_cases ht : j=target <;>
    simp_all [Move.apply,Tape.write_self]

theorem rewind_step (s : Tape (Option Bool)) (gl gr tl tr : List Bool) (b c : Bool) :
    (attach M source guide target).step
      (rewindStart source guide target others s (c::gl) gr (b::tl) tr)=
      some (rewindStart source guide target others s gl (c::gr) tl (b::tr)) := by
  simp only [rewindStart,QueryCopy.tape_move_left]
  simp only [Machine.step,Machine.action,attach,frame,hsep.1,Ne.symm hsep.1,
    hsep.2.1,Ne.symm hsep.2.1,hsep.2.2,Ne.symm hsep.2.2,↓reduceIte,QueryCopy.tape_head]
  congr 1; congr 1; funext j
  by_cases hs : j=source <;> by_cases hg : j=guide <;> by_cases ht : j=target <;>
    simp_all [Move.apply,Tape.write_self]

theorem rewind_return (s : Tape (Option Bool)) (gr tr : List Bool) :
    (attach M source guide target).step (rewindStart source guide target others s [] gr [] tr)=
      some (finished M source guide target others s gr tr) := by
  have hh : ((tape [] gr).move .left).head=none := rfl
  have hw : ((tape [] gr).move .left).write none=(tape [] gr).move .left := by
    simpa only [hh] using Tape.write_self ((tape [] gr).move .left)
  simp only [Machine.step,Machine.action,attach,rewindStart,finished,frame,hsep.1,Ne.symm hsep.1,
    hsep.2.1,Ne.symm hsep.2.1,hsep.2.2,Ne.symm hsep.2.2,↓reduceIte,hh]
  congr 1; congr 1; funext j
  by_cases hs : j=source <;> by_cases hg : j=guide <;> by_cases ht : j=target <;>
    simp_all [Move.apply,hw,Tape.write_self,Tape.move_left_right]

/-- Explicit truncation behavior: rejected partial registers are NOT asserted clean. -/
theorem truncated_halt (sl gl gr out : List Bool) (c : Bool) :
    (attach M source guide target).answer (copying source guide target others sl [] gl (c::gr) out)=
      some false := by
  simp [Machine.answer,Machine.action,attach,copying,frame,hsep.1,Ne.symm hsep.1,
    hsep.2.1,Ne.symm hsep.2.1,hsep.2.2,Ne.symm hsep.2.2,QueryCopy.tape_head,QueryCopy.tape_empty_head]

omit hsep others in
theorem continuation_run {s t : Config k (Option Bool) Λ} {n d} (h : Run M s n d t) :
    Run (attach M source guide target) (embed s) n d (embed t) := by
  have hs (s : Config k (Option Bool) Λ) :
      (attach M source guide target).step (embed s)=(M.step s).map embed := by
    cases ha : M.transition s.label (fun j => (s.tapes j).head) <;>
      simp [Machine.step,Machine.action,attach,embed,ha]
  have hd (s : Config k (Option Bool) Λ) :
      delta (attach M source guide target) (embed s)=delta M s := by
    cases ha : M.transition s.label (fun j => (s.tapes j).head) <;>
      simp [delta,Machine.action,attach,embed,ha]
  induction h with
  | nil => exact .nil _
  | @cons s v t n d he tail ih =>
    have he' : (attach M source guide target).step (embed s)=some (embed v) := by rw [hs,he]; rfl
    simpa only [hd] using Run.cons he' ih

end QecReliability.OracleCost.MultiTape.GuidedInputSlice
