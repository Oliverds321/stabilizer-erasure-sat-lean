import OracleCost.GuidedInputSliceTrace

/-! Literal in-place fixed-width slot exchange. Runtime width comes from an
unchanged guide word. An array cursor advances across the overwritten slot;
the register receives the old slot and rewinds, so no fresh scratch is needed.
The exact already-checked guide/register rewind rows are reused. -/
namespace QecReliability.OracleCost.MultiTape.FixedSlotExchange
open Turing Displacement
variable {k : ℕ} {Λ : Type} [Fintype Λ]
abbrev Label (Λ : Type) := Unit ⊕ GuidedInputSlice.Label Λ
abbrev tape := QueryCopy.tape

def attach (M : Machine k (Option Bool) Λ) (array guide register : Fin (k+1)) :
    Machine k (Option Bool) (Label Λ) where
  start := .inl ()
  inputSymbol := M.inputSymbol
  input_injective := M.input_injective
  input_not_blank := M.input_not_blank
  transition state heads := match state with
    | .inl _ => match heads guide with
      | none => .advance (.inr (.inl true)) heads
          (fun j => if j=guide ∨ j=register then .left else .stay)
      | some _ => match heads array, heads register with
        | some a, some b => .advance (.inl ())
            (fun j => if j=array then some b else if j=register then some a else heads j)
            (fun j => if j=array ∨ j=guide ∨ j=register then .right else .stay)
        | _, _ => .halt false
    | .inr label => match (GuidedInputSlice.attach M array guide register).transition label heads with
      | .halt b => .halt b
      | .advance next write move => .advance (.inr next) write move

def scanning (array guide register : Fin (k+1)) (others : Fin (k+1) → Tape (Option Bool))
    (al ar gl gr rl rr : List Bool) : Config k (Option Bool) (Label Λ) :=
  ⟨.inl (),fun j => if j=array then tape al ar else if j=guide then tape gl gr
    else if j=register then tape rl rr else others j⟩

def embed (s : Config k (Option Bool) (GuidedInputSlice.Label Λ)) :
    Config k (Option Bool) (Label Λ) := ⟨.inr s.label,s.tapes⟩

def finished (M : Machine k (Option Bool) Λ) (array guide register : Fin (k+1))
    (others : Fin (k+1) → Tape (Option Bool)) (a : Tape (Option Bool)) (g r : List Bool) :
    Config k (Option Bool) (Label Λ) :=
  embed (GuidedInputSlice.finished M array guide register others a g r)

theorem write_right (left right : List Bool) (old new : Bool) :
    ((tape left (old::right)).write (some new)).move .right=tape (new::left) right := rfl

variable (M : Machine k (Option Bool) Λ) (array guide register : Fin (k+1))

theorem delegate_run {s t : Config k (Option Bool) (GuidedInputSlice.Label Λ)} {n d}
    (h : Run (GuidedInputSlice.attach M array guide register) s n d t) :
    Run (attach M array guide register) (embed s) n d (embed t) := by
  have hs (s) : (attach M array guide register).step (embed s)=
      ((GuidedInputSlice.attach M array guide register).step s).map embed := by
    cases ha : (GuidedInputSlice.attach M array guide register).transition s.label
        (fun j => (s.tapes j).head) <;> simp [Machine.step,Machine.action,attach,embed,ha]
  have hd (s) : delta (attach M array guide register) (embed s)=
      delta (GuidedInputSlice.attach M array guide register) s := by
    cases ha : (GuidedInputSlice.attach M array guide register).transition s.label
        (fun j => (s.tapes j).head) <;> simp [delta,Machine.action,attach,embed,ha]
  induction h with
  | nil => exact .nil _
  | @cons s v t n d he tail ih =>
    have he' : (attach M array guide register).step (embed s)=some (embed v) := by rw [hs,he]; rfl
    simpa only [hd] using Run.cons he' ih

variable (hsep : array≠guide ∧ array≠register ∧ guide≠register)
variable (others : Fin (k+1) → Tape (Option Bool))
include hsep

theorem swap_step (al ar gl gr rl rr : List Bool) (a b c : Bool) :
    (attach M array guide register).step (scanning array guide register others al (a::ar) gl (c::gr) rl (b::rr))=
      some (scanning array guide register others (b::al) ar (c::gl) gr (a::rl) rr) := by
  simp only [Machine.step,Machine.action,attach,scanning,hsep.1,Ne.symm hsep.1,
    hsep.2.1,Ne.symm hsep.2.1,hsep.2.2,Ne.symm hsep.2.2,↓reduceIte,QueryCopy.tape_head]
  congr 1; congr 1; funext j
  by_cases ha : j=array <;> by_cases hg : j=guide <;> by_cases hr : j=register <;>
    simp_all [Move.apply,write_right,Tape.write_self,QueryCopy.tape_move_right]

theorem swap_end (al ar gl rl rr : List Bool) :
    (attach M array guide register).step (scanning array guide register others al ar gl [] rl rr)=
      some (embed (GuidedInputSlice.rewindStart array guide register others (tape al ar) gl [] rl rr)) := by
  simp only [Machine.step,Machine.action,attach,scanning,embed,GuidedInputSlice.rewindStart,
    GuidedInputSlice.frame,hsep.1,Ne.symm hsep.1,hsep.2.1,Ne.symm hsep.2.1,
    hsep.2.2,Ne.symm hsep.2.2,↓reduceIte,QueryCopy.tape_empty_head]
  congr 1; congr 1; funext j
  by_cases ha : j=array <;> by_cases hg : j=guide <;> by_cases hr : j=register <;>
    simp_all [Move.apply,Tape.write_self]

theorem missing_array (al gl gr rl rr : List Bool) (c : Bool) :
    (attach M array guide register).answer (scanning array guide register others al [] gl (c::gr) rl rr)=some false := by
  simp [Machine.answer,Machine.action,attach,scanning,hsep.1,Ne.symm hsep.1,
    hsep.2.1,Ne.symm hsep.2.1,hsep.2.2,Ne.symm hsep.2.2,QueryCopy.tape_head,QueryCopy.tape_empty_head]

theorem missing_register (al ar gl gr rl : List Bool) (a c : Bool) :
    (attach M array guide register).answer (scanning array guide register others al (a::ar) gl (c::gr) rl [])=some false := by
  simp [Machine.answer,Machine.action,attach,scanning,hsep.1,Ne.symm hsep.1,
    hsep.2.1,Ne.symm hsep.2.1,hsep.2.2,Ne.symm hsep.2.2,QueryCopy.tape_head,QueryCopy.tape_empty_head]

end QecReliability.OracleCost.MultiTape.FixedSlotExchange
