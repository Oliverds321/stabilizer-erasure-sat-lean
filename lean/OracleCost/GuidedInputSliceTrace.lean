import OracleCost.GuidedInputSliceMachine

/-! Exact valid-segment execution. Guide and target return to their inherited
origins while the read-only input advances across exactly the requested segment. -/
namespace QecReliability.OracleCost.MultiTape.GuidedInputSlice
open Turing Displacement
variable {k : ℕ} {Λ : Type} [Fintype Λ]
variable (M : Machine k (Option Bool) Λ) (source guide target : Fin (k+1))
variable (hsep : source≠guide ∧ source≠target ∧ guide≠target)
variable (others : Fin (k+1) → Tape (Option Bool))
include hsep

theorem rewind_run (s : Tape (Option Bool)) (gl gr tl tr : List Bool) (hlen : tl.length=gl.length) :
    Run (attach M source guide target) (rewindStart source guide target others s gl gr tl tr)
      (gl.length+1) (offsets source guide target 0 (1-(gl.length:ℤ)))
      (finished M source guide target others s (gl.reverse++gr) (tl.reverse++tr)) := by
  induction gl generalizing gr tl tr with
  | nil =>
    have ht : tl=[] := List.length_eq_zero_iff.mp hlen
    subst tl
    have h := single (rewind_return M source guide target hsep others s gr tr)
    have hd : delta (attach M source guide target) (rewindStart source guide target others s [] gr [] tr)=
        offsets source guide target 0 1 := by
      have hh : ((tape [] gr).move .left).head = none := rfl
      funext j
      by_cases hs : j=source <;> by_cases hg : j=guide <;> by_cases ht : j=target <;>
        simp [offsets,delta,Machine.action,attach,rewindStart,frame,hsep.1,Ne.symm hsep.1,
          hsep.2.1,Ne.symm hsep.2.1,hsep.2.2,Ne.symm hsep.2.2,hs,hg,ht,
          hh,Move.delta]
    rw [hd] at h
    simpa using h
  | cons c gl ih =>
    cases tl with
    | nil => simp at hlen
    | cons b tl =>
      have hl : tl.length=gl.length := by simpa using hlen
      have h := Run.cons (rewind_step M source guide target hsep others s gl gr tl tr b c)
        (ih (c::gr) tl (b::tr) hl)
      have hd : (fun j => delta (attach M source guide target)
          (rewindStart source guide target others s (c::gl) gr (b::tl) tr) j+
          offsets source guide target 0 (1-(gl.length:ℤ)) j)=
          offsets source guide target 0 (1-((c::gl).length:ℤ)) := by
        funext j
        by_cases hs : j=source <;> by_cases hg : j=guide <;> by_cases ht : j=target <;>
          simp [offsets,delta,Machine.action,attach,rewindStart,frame,hsep.1,Ne.symm hsep.1,
            hsep.2.1,Ne.symm hsep.2.1,hsep.2.2,Ne.symm hsep.2.2,hs,hg,ht,
            QueryCopy.tape_move_left,QueryCopy.tape_head,Move.delta] <;> omega
      rw [hd] at h
      simpa [List.reverse_cons,List.append_assoc] using h

theorem copy_run (bits guideBits sl suffix gl out : List Bool)
    (hlen : bits.length=guideBits.length) (hout : out.length=gl.length) :
    Run (attach M source guide target)
      (copying source guide target others sl (bits++suffix) gl guideBits out)
      (2*bits.length+gl.length+2) (offsets source guide target bits.length (-(gl.length:ℤ)))
      (finished M source guide target others (tape (bits.reverse++sl) suffix)
        (gl.reverse++guideBits) (out.reverse++bits)) := by
  induction bits generalizing guideBits sl gl out with
  | nil =>
    have hg : guideBits=[] := List.length_eq_zero_iff.mp hlen.symm
    subst guideBits
    have h := Run.cons (copy_end M source guide target hsep others sl suffix gl out)
      (rewind_run M source guide target hsep others (tape sl suffix) gl [] out [] hout)
    have hd : (fun j => delta (attach M source guide target)
        (copying source guide target others sl suffix gl [] out) j+
        offsets source guide target 0 (1-(gl.length:ℤ)) j)=
        offsets source guide target 0 (-(gl.length:ℤ)) := by
      funext j
      by_cases hs : j=source <;> by_cases hg : j=guide <;> by_cases ht : j=target <;>
        simp [offsets,delta,Machine.action,attach,copying,frame,hsep.1,Ne.symm hsep.1,
          hsep.2.1,Ne.symm hsep.2.1,hsep.2.2,Ne.symm hsep.2.2,hs,hg,ht,
          QueryCopy.tape_empty_head,Move.delta] <;> omega
    rw [hd] at h
    simpa [Nat.add_assoc] using h
  | cons b bits ih =>
    cases guideBits with
    | nil => simp at hlen
    | cons c guideBits =>
      have hl : bits.length=guideBits.length := by simpa using hlen
      have ho : (b::out).length=(c::gl).length := by simpa using hout
      have h := Run.cons (copy_step M source guide target hsep others sl (bits++suffix) gl guideBits out b c)
        (ih guideBits (b::sl) (c::gl) (b::out) hl ho)
      have hd : (fun j => delta (attach M source guide target)
          (copying source guide target others sl (b::(bits++suffix)) gl (c::guideBits) out) j+
          offsets source guide target bits.length (-((c::gl).length:ℤ)) j)=
          offsets source guide target (b::bits).length (-(gl.length:ℤ)) := by
        funext j
        by_cases hs : j=source <;> by_cases hg : j=guide <;> by_cases ht : j=target <;>
          simp [offsets,delta,Machine.action,attach,copying,frame,hsep.1,Ne.symm hsep.1,
            hsep.2.1,Ne.symm hsep.2.1,hsep.2.2,Ne.symm hsep.2.2,hs,hg,ht,
            QueryCopy.tape_head,Move.delta] <;> omega
      rw [hd] at h
      have htime : (2*bits.length+(c::gl).length+2)+1=2*(b::bits).length+gl.length+2 := by
        simp only [List.length_cons]; omega
      rw [htime] at h
      simpa [List.reverse_cons,List.append_assoc] using h

/-- Complete valid slice. The guide may hold ANY bits of the exact width. -/
theorem slice_run (bits guideBits sl suffix : List Bool) (hlen : bits.length=guideBits.length) :
    Run (attach M source guide target)
      (copying source guide target others sl (bits++suffix) [] guideBits [])
      (2*bits.length+2) (fun j => if j=source then (bits.length:ℤ) else 0)
      (finished M source guide target others (tape (bits.reverse++sl) suffix) guideBits bits) := by
  have h := copy_run M source guide target hsep others bits guideBits sl suffix [] [] hlen rfl
  have hd : offsets source guide target bits.length 0=
      (fun j => if j=source then (bits.length:ℤ) else 0) := by
    funext j; simp [offsets]
  simpa only [List.length_nil,Nat.add_zero,Int.natCast_zero,neg_zero,List.reverse_nil,List.nil_append,hd] using h

/-- Actual input cursor advances; target/guide and all other origins restore.
The full source tape is preserved in place, with its relative view shifted. -/
theorem slice_observed (bits guideBits sl suffix : List Bool) (hlen : bits.length=guideBits.length)
    (initial : Observed k (Option Bool) (Label Λ))
    (hi : initial.core=copying source guide target others sl (bits++suffix) [] guideBits []) :
    ∃ final, Trace (attach M source guide target) initial (2*bits.length+2) final ∧
      final.core=finished M source guide target others (tape (bits.reverse++sl) suffix) guideBits bits ∧
      (∀ j,final.position j=initial.position j+(if j=source then (bits.length:ℤ) else 0)) ∧
      visitedCells final≤visitedCells initial+(k+1)*(2*bits.length+2) := by
  obtain ⟨last,ht,hf,hp⟩ := (slice_run M source guide target hsep others bits guideBits sl suffix hlen).observe initial hi
  exact ⟨last,ht,hf,hp,ht.space_le⟩

end QecReliability.OracleCost.MultiTape.GuidedInputSlice
