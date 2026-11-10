import OracleCost.FixedSlotExchangeMachine

/-! Constructed physical swap path with exact origins and unchanged capacity.
The exchanged old slot is returned in the existing register, not allocated in
proof-only storage. Arbitrary array prefix/suffix survive. -/
namespace QecReliability.OracleCost.MultiTape.FixedSlotExchange
open Turing Displacement
variable {k : ℕ} {Λ : Type} [Fintype Λ]
variable (M : Machine k (Option Bool) Λ) (array guide register : Fin (k+1))
variable (hsep : array≠guide ∧ array≠register ∧ guide≠register)
variable (others : Fin (k+1) → Tape (Option Bool))
include hsep

theorem exchange_run (old new guideBits al suffix gl rl : List Bool)
    (hnew : new.length=old.length) (hguide : guideBits.length=old.length) (hleft : rl.length=gl.length) :
    Run (attach M array guide register)
      (scanning array guide register others al (old++suffix) gl guideBits rl new)
      (2*old.length+gl.length+2) (GuidedInputSlice.offsets array guide register old.length (-(gl.length:ℤ)))
      (finished M array guide register others (tape (new.reverse++al) suffix)
        (gl.reverse++guideBits) (rl.reverse++old)) := by
  induction old generalizing new guideBits al gl rl with
  | nil =>
    have hn : new=[] := List.length_eq_zero_iff.mp hnew
    have hg : guideBits=[] := List.length_eq_zero_iff.mp hguide
    subst new; subst guideBits
    have h := Run.cons (swap_end M array guide register hsep others al suffix gl rl [])
      (delegate_run M array guide register
        (GuidedInputSlice.rewind_run M array guide register hsep others (tape al suffix) gl [] rl [] hleft))
    have hd : (fun j => delta (attach M array guide register)
        (scanning array guide register others al suffix gl [] rl []) j+
        GuidedInputSlice.offsets array guide register 0 (1-(gl.length:ℤ)) j)=
        GuidedInputSlice.offsets array guide register 0 (-(gl.length:ℤ)) := by
      funext j
      by_cases ha : j=array <;> by_cases hg : j=guide <;> by_cases hr : j=register <;>
        simp [GuidedInputSlice.offsets,delta,Machine.action,attach,scanning,hsep.1,Ne.symm hsep.1,
          hsep.2.1,Ne.symm hsep.2.1,hsep.2.2,Ne.symm hsep.2.2,ha,hg,hr,
          QueryCopy.tape_empty_head,Move.delta] <;> omega
    rw [hd] at h
    simpa [finished,Nat.add_assoc] using h
  | cons a old ih =>
    cases new with
    | nil => simp at hnew
    | cons b new =>
      cases guideBits with
      | nil => simp at hguide
      | cons c guideBits =>
        have hn : new.length=old.length := by simpa using hnew
        have hg : guideBits.length=old.length := by simpa using hguide
        have hl : (a::rl).length=(c::gl).length := by simpa using hleft
        have h := Run.cons (swap_step M array guide register hsep others al (old++suffix) gl guideBits rl new a b c)
          (ih new guideBits (b::al) (c::gl) (a::rl) hn hg hl)
        have hd : (fun j => delta (attach M array guide register)
            (scanning array guide register others al (a::(old++suffix)) gl (c::guideBits) rl (b::new)) j+
            GuidedInputSlice.offsets array guide register old.length (-((c::gl).length:ℤ)) j)=
            GuidedInputSlice.offsets array guide register (a::old).length (-(gl.length:ℤ)) := by
          funext j
          by_cases ha : j=array <;> by_cases hg : j=guide <;> by_cases hr : j=register <;>
            simp [GuidedInputSlice.offsets,delta,Machine.action,attach,scanning,hsep.1,Ne.symm hsep.1,
              hsep.2.1,Ne.symm hsep.2.1,hsep.2.2,Ne.symm hsep.2.2,ha,hg,hr,
              QueryCopy.tape_head,Move.delta] <;> omega
        rw [hd] at h
        have ht : (2*old.length+(c::gl).length+2)+1=2*(a::old).length+gl.length+2 := by
          simp only [List.length_cons]; omega
        rw [ht] at h
        simpa [List.reverse_cons,List.append_assoc] using h

/-- One slot transaction, including rewind. The array cursor advances w;
register/guide return to their inherited absolute origins. -/
theorem slot_run (old new guideBits al suffix : List Bool)
    (hnew : new.length=old.length) (hguide : guideBits.length=old.length) :
    Run (attach M array guide register)
      (scanning array guide register others al (old++suffix) [] guideBits [] new)
      (2*old.length+2) (fun j => if j=array then (old.length:ℤ) else 0)
      (finished M array guide register others (tape (new.reverse++al) suffix) guideBits old) := by
  have h := exchange_run M array guide register hsep others old new guideBits al suffix [] [] hnew hguide rfl
  have hd : GuidedInputSlice.offsets array guide register old.length 0=
      (fun j => if j=array then (old.length:ℤ) else 0) := by
    funext j; simp [GuidedInputSlice.offsets]
  simpa only [List.length_nil,Nat.add_zero,Int.natCast_zero,neg_zero,List.reverse_nil,List.nil_append,hd] using h

theorem slot_observed (old new guideBits al suffix : List Bool)
    (hnew : new.length=old.length) (hguide : guideBits.length=old.length)
    (initial : Observed k (Option Bool) (Label Λ))
    (hi : initial.core=scanning array guide register others al (old++suffix) [] guideBits [] new) :
    ∃ final, Trace (attach M array guide register) initial (2*old.length+2) final ∧
      final.core=finished M array guide register others (tape (new.reverse++al) suffix) guideBits old ∧
      (∀ j,final.position j=initial.position j+(if j=array then (old.length:ℤ) else 0)) ∧
      visitedCells final≤visitedCells initial+(k+1)*(2*old.length+2) := by
  obtain ⟨last,ht,hf,hp⟩ := (slot_run M array guide register hsep others old new guideBits al suffix hnew hguide).observe initial hi
  exact ⟨last,ht,hf,hp,ht.space_le⟩

end QecReliability.OracleCost.MultiTape.FixedSlotExchange
