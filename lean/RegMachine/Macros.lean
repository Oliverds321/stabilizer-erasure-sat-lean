import RegMachine.Struct
import Mathlib.Tactic.Linarith

/-!
# Derived register operations (templates)

Small structured macros over the basic instruction set, with big-step lemmas giving
exact effects and cost/space bounds. They serve as templates for the controller
library (list reversal, scans, counters):

* `copyS dst src`: `dst := src`;
* `moveAll dst src`: `dst := dst ++ src; src := []` by a bit-by-bit loop
  (`while src ≠ []: pushBack dst (head src); popFront src`), cost
  `≤ (|src|+1)·(4 + |dst| + |src|)`, space `|dst| + |src|`.
-/

set_option autoImplicit false

namespace QecReliability.RegMachine
open Function

variable {R : ℕ}

/-- `dst := src`. -/
def copyS (dst src : Fin R) : Stmt (Instr R) :=
  .seq (.prim (.clear dst)) (.prim (.append dst src))

theorem copyS_run {S : ℕ} {dst src : Fin R} (hne : dst ≠ src) {s : Regs R} (hs : Fits S s) :
    Stmt.BigStep (basicSem R) (Fits S) (copyS dst src) s 2
      ((1 + (s dst).length) + (1 + 0 + (s src).length)) (update s dst (s src)) := by
  have hsrc : update s dst [] src = s src := update_of_ne (Ne.symm hne) _ _
  have h1 : Fits S (update s dst []) := by
    intro r; by_cases hr : r = dst
    · subst hr; simp
    · rw [update_of_ne hr]; exact hs r
  have h2 : Fits S (update s dst (s src)) := by
    intro r; by_cases hr : r = dst
    · subst hr; simpa using hs src
    · rw [update_of_ne hr]; exact hs r
  have hA := Stmt.BigStep.prim (σ := basicSem R) (Inv := Fits S) (p := Instr.clear dst) (s := s)
    (s' := update s dst []) (b := true) hs trivial rfl h1
  have hB : Stmt.BigStep (basicSem R) (Fits S) (.prim (.append dst src)) (update s dst []) 1
      (1 + 0 + (s src).length) (update s dst (s src)) := by
    have := Stmt.BigStep.prim (σ := basicSem R) (Inv := Fits S) (p := .append dst src)
      (s := update s dst []) (s' := update s dst (s src)) (b := true) h1 hne
      (by simp [basicSem, Instr.eval, hsrc]) h2
    simpa [basicSem, Instr.cost, hsrc] using this
  exact .seq hA hB

/-- Move all bits of `src` to the end of `dst`, one by one. -/
def moveAll (dst src : Fin R) : Stmt (Instr R) :=
  .loop (.isEmpty src) false
    (.seq (.ite (.headIs src true) (.prim (.pushBack dst true)) (.prim (.pushBack dst false)))
      (.prim (.popFront src)))

theorem moveAll_run {S : ℕ} {dst src : Fin R} (hne : dst ≠ src) :
    ∀ (w : List Bool) (s : Regs R), s src = w → Fits S s →
      (s dst).length + w.length ≤ S →
      ∃ N C, Stmt.BigStep (basicSem R) (Fits S) (moveAll dst src) s N C
          (update (update s dst (s dst ++ w)) src []) ∧
        C ≤ (w.length + 1) * (4 + (s dst).length + w.length) := by
  have hsd : src ≠ dst := Ne.symm hne
  intro w
  induction w with
  | nil =>
    intro s hw hs _
    refine ⟨1, 1, ?_, by nlinarith⟩
    have hfin : update (update s dst (s dst ++ [])) src [] = s := by
      funext r
      by_cases hr : r = src
      · subst hr; simp [hw]
      · by_cases hr' : r = dst
        · subst hr'; simp [hr]
        · simp [hr]
    rw [hfin]
    exact .loopF (b := true) hs trivial (by simp [basicSem, Instr.eval, hw]) (by decide) hs
  | cons b rest ih =>
    intro s hw hs hlen
    simp only [List.length_cons] at hlen
    set s1 := update s dst (s dst ++ [b]) with hs1
    set s2 := update s1 src rest with hs2
    have hs1src : s1 src = b :: rest := by rw [hs1, update_of_ne hsd, hw]
    have hs2dst : s2 dst = s dst ++ [b] := by rw [hs2, update_of_ne hne, hs1, update_self]
    have hs2src : s2 src = rest := by rw [hs2, update_self]
    have hfit1 : Fits S s1 := by
      intro r; by_cases hr : r = dst
      · subst hr; rw [hs1, update_self]; simp; omega
      · rw [hs1, update_of_ne hr]; exact hs r
    have hfit2 : Fits S s2 := by
      intro r; by_cases hr : r = src
      · subst hr; rw [hs2src]; have := hs r; rw [hw] at this; simp at this; omega
      · rw [hs2, update_of_ne hr]; exact hfit1 r
    obtain ⟨N, C, hrun, hC⟩ := ih s2 hs2src hfit2 (by rw [hs2dst]; simp; omega)
    -- the loop body
    have hpush : Stmt.BigStep (basicSem R) (Fits S) (.prim (.pushBack dst b)) s 1
        (1 + (s dst).length) s1 :=
      Stmt.BigStep.prim (p := Instr.pushBack dst b) (s := s) (s' := s1) (b := true) hs trivial rfl
        hfit1
    have hite : Stmt.BigStep (basicSem R) (Fits S)
        (.ite (.headIs src true) (.prim (.pushBack dst true)) (.prim (.pushBack dst false)))
        s 2 (1 + (1 + (s dst).length)) s1 := by
      cases b with
      | true => exact .iteT (s' := s) hs trivial (by simp [basicSem, Instr.eval, hw]) hpush
      | false => exact .iteF (s' := s) hs trivial (by simp [basicSem, Instr.eval, hw]) hpush
    have hpop : Stmt.BigStep (basicSem R) (Fits S) (.prim (.popFront src)) s1 1
        (1 + (b :: rest).length) s2 := by
      have := Stmt.BigStep.prim (σ := basicSem R) (Inv := Fits S) (p := .popFront src)
        (s := s1) (s' := s2) (b := true) hfit1 trivial
        (by simp [basicSem, Instr.eval, hs1src, hs2]) hfit2
      simpa [basicSem, Instr.cost, hs1src] using this
    have hfin : update (update s2 dst (s2 dst ++ rest)) src [] =
        update (update s dst (s dst ++ b :: rest)) src [] := by
      funext r
      by_cases hr : r = src
      · subst hr; simp
      · by_cases hr' : r = dst
        · subst hr'; simp [hr, hs2dst]
        · simp [hr, hr', hs2, hs1]
    rw [hfin] at hrun
    refine ⟨2 + 1 + N + 1, 1 + (1 + (1 + (s dst).length) + (1 + (b :: rest).length)) + C,
      .loopT hs trivial (by simp [basicSem, Instr.eval, hw]) (.seq hite hpop) hrun, ?_⟩
    rw [hs2dst] at hC
    simp only [List.length_append, List.length_cons, List.length_nil] at hC ⊢
    nlinarith

end QecReliability.RegMachine
