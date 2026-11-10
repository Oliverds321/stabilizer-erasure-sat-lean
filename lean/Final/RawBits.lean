import RegMachine.Macros
import FL.Encode

/-!
# Converting between raw bit registers and FL encodings of bit lists

The machine's input and the SAT queries/outputs are raw bit strings, while FL works on
serialized trees. `rawToVal dst src` turns the raw string `w` in `src` into
`(Enc.list Enc.bool w).bits` appended to `dst` (consuming `src`).
-/

set_option autoImplicit false

namespace QecReliability.RegMachine
open Function FL

variable {R : ℕ}

/-- Serialization of the FL encoding of a bit list. -/
def encBits (w : List Bool) : List Bool := (Enc.list Enc.bool w).bits

/-- Bits contributed by one list element. -/
def elemBits (x : Bool) : List Bool := if x then [true, true, false, false] else [true, false]

theorem encBits_nil : encBits [] = [false] := rfl

theorem encBits_cons (x : Bool) (w : List Bool) : encBits (x :: w) = elemBits x ++ encBits w := by
  cases x <;> rfl

theorem encBits_eq (w : List Bool) : encBits w = w.flatMap elemBits ++ [false] := by
  induction w with
  | nil => rfl
  | cons x w ih => rw [encBits_cons, ih]; simp

theorem elemBits_length (x : Bool) : (elemBits x).length ≤ 4 := by cases x <;> simp [elemBits]

theorem flatMap_elemBits_length (w : List Bool) : (w.flatMap elemBits).length ≤ 4 * w.length := by
  induction w with
  | nil => simp
  | cons x w ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := elemBits_length x; omega

/-- Do nothing (a constant test). -/
def skipS : Stmt (Instr R) := .prim (.const true)

theorem skipS_run {S : ℕ} {s : Regs R} (hs : Fits S s) :
    Stmt.BigStep (basicSem R) (Fits S) skipS s 1 1 s :=
  Stmt.BigStep.prim (p := Instr.const true) hs trivial rfl hs

/-- Append the constant list `bs` to `dst`. -/
def pushList (dst : Fin R) : List Bool → Stmt (Instr R)
  | [] => skipS
  | b :: bs => .seq (.prim (.pushBack dst b)) (pushList dst bs)

theorem pushList_run {S : ℕ} (dst : Fin R) :
    ∀ (bs : List Bool) (s : Regs R), Fits S s → (s dst).length + bs.length ≤ S →
      ∃ N C, Stmt.BigStep (basicSem R) (Fits S) (pushList dst bs) s N C
          (update s dst (s dst ++ bs)) ∧ C ≤ (bs.length + 1) * ((s dst).length + bs.length + 1) := by
  intro bs
  induction bs with
  | nil =>
    intro s hs _
    refine ⟨1, 1, ?_, by simp⟩
    simpa [pushList] using skipS_run (R := R) hs
  | cons b bs ih =>
    intro s hs hlen
    simp only [List.length_cons] at hlen
    set s1 := update s dst (s dst ++ [b]) with hs1
    have hfit1 : Fits S s1 := by
      intro r; by_cases hr : r = dst
      · subst hr; rw [hs1, update_self]; simp; omega
      · rw [hs1, update_of_ne hr]; exact hs r
    have hd1 : s1 dst = s dst ++ [b] := by rw [hs1, update_self]
    obtain ⟨N, C, hrun, hC⟩ := ih s1 hfit1 (by rw [hd1]; simp; omega)
    have hpush : Stmt.BigStep (basicSem R) (Fits S) (.prim (.pushBack dst b)) s 1
        (1 + (s dst).length) s1 :=
      Stmt.BigStep.prim (p := Instr.pushBack dst b) (s := s) (s' := s1) (b := true) hs trivial rfl
        hfit1
    have hfin : update s1 dst (s1 dst ++ bs) = update s dst (s dst ++ b :: bs) := by
      rw [hd1, hs1, update_idem]; simp
    rw [hfin] at hrun
    refine ⟨1 + N, (1 + (s dst).length) + C, .seq hpush hrun, ?_⟩
    rw [hd1] at hC
    simp only [List.length_append, List.length_cons, List.length_nil] at hC ⊢
    nlinarith

/-- The conversion loop: for each bit of `src`, append its element encoding to `dst`. -/
def rawLoop (dst src : Fin R) : Stmt (Instr R) :=
  .loop (.isEmpty src) false
    (.seq (.ite (.headIs src true) (pushList dst [true, true, false, false])
      (pushList dst [true, false])) (.prim (.popFront src)))

theorem rawLoop_run {S : ℕ} {dst src : Fin R} (hne : dst ≠ src) :
    ∀ (w : List Bool) (s : Regs R), s src = w → Fits S s →
      (s dst).length + 4 * w.length ≤ S →
      ∃ N C, Stmt.BigStep (basicSem R) (Fits S) (rawLoop dst src) s N C
          (update (update s dst (s dst ++ w.flatMap elemBits)) src []) ∧
        C ≤ (w.length + 1) * (8 * ((s dst).length + 4 * w.length + 5)) := by
  have hsd : src ≠ dst := Ne.symm hne
  intro w
  induction w with
  | nil =>
    intro s hw hs _
    refine ⟨1, 1, ?_, by nlinarith⟩
    have hfin : update (update s dst (s dst ++ [].flatMap elemBits)) src [] = s := by
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
    have hel := elemBits_length b
    obtain ⟨N₁, C₁, hpush, hC₁⟩ := pushList_run (S := S) dst (elemBits b) s hs (by omega)
    set s1 := update s dst (s dst ++ elemBits b) with hs1
    set s2 := update s1 src rest with hs2
    have hfit1 : Fits S s1 := hpush.inv_end
    have hs1src : s1 src = b :: rest := by rw [hs1, update_of_ne hsd, hw]
    have hs2dst : s2 dst = s dst ++ elemBits b := by rw [hs2, update_of_ne hne, hs1, update_self]
    have hs2src : s2 src = rest := by rw [hs2, update_self]
    have hfit2 : Fits S s2 := by
      intro r; by_cases hr : r = src
      · subst hr; rw [hs2src]; have := hs r; rw [hw] at this; simp at this; omega
      · rw [hs2, update_of_ne hr]; exact hfit1 r
    obtain ⟨N, C, hrun, hC⟩ := ih s2 hs2src hfit2 (by rw [hs2dst]; simp; omega)
    have hite : Stmt.BigStep (basicSem R) (Fits S)
        (.ite (.headIs src true) (pushList dst [true, true, false, false])
          (pushList dst [true, false])) s (N₁ + 1) (1 + C₁) s1 := by
      cases b with
      | true => exact .iteT (s' := s) hs trivial (by simp [basicSem, Instr.eval, hw]) hpush
      | false => exact .iteF (s' := s) hs trivial (by simp [basicSem, Instr.eval, hw]) hpush
    have hpop : Stmt.BigStep (basicSem R) (Fits S) (.prim (.popFront src)) s1 1
        (1 + (b :: rest).length) s2 := by
      have := Stmt.BigStep.prim (σ := basicSem R) (Inv := Fits S) (p := .popFront src)
        (s := s1) (s' := s2) (b := true) hfit1 trivial
        (by simp [basicSem, Instr.eval, hs1src, hs2]) hfit2
      simpa [basicSem, Instr.cost, hs1src] using this
    have hfin : update (update s2 dst (s2 dst ++ rest.flatMap elemBits)) src [] =
        update (update s dst (s dst ++ (b :: rest).flatMap elemBits)) src [] := by
      funext r
      by_cases hr : r = src
      · subst hr; simp
      · by_cases hr' : r = dst
        · subst hr'; simp [hr, hs2dst]
        · simp [hr, hr', hs2, hs1]
    rw [hfin] at hrun
    refine ⟨N₁ + 1 + 1 + N + 1, 1 + ((1 + C₁) + (1 + (b :: rest).length)) + C,
      .loopT hs trivial (by simp [basicSem, Instr.eval, hw]) (.seq hite hpop) hrun, ?_⟩
    rw [hs2dst] at hC
    simp only [List.length_append, List.length_cons] at hC hC₁ ⊢
    nlinarith

/-- `dst := dst ++ encBits (src)`, `src := []`. -/
def rawToVal (dst src : Fin R) : Stmt (Instr R) := .seq (rawLoop dst src) (pushList dst [false])

theorem rawToVal_run {S : ℕ} {dst src : Fin R} (hne : dst ≠ src) (w : List Bool) (s : Regs R)
    (hw : s src = w) (hs : Fits S s) (hlen : (s dst).length + 4 * w.length + 1 ≤ S) :
    ∃ N C, Stmt.BigStep (basicSem R) (Fits S) (rawToVal dst src) s N C
        (update (update s dst (s dst ++ encBits w)) src []) ∧
      C ≤ (w.length + 2) * (8 * ((s dst).length + 4 * w.length + 5)) := by
  obtain ⟨N₁, C₁, h₁, hC₁⟩ := rawLoop_run hne w s hw hs (by omega)
  set s1 := update (update s dst (s dst ++ w.flatMap elemBits)) src [] with hs1
  have hfit1 : Fits S s1 := h₁.inv_end
  have hd1 : s1 dst = s dst ++ w.flatMap elemBits := by
    rw [hs1, update_of_ne hne, update_self]
  have hfl := flatMap_elemBits_length w
  obtain ⟨N₂, C₂, h₂, hC₂⟩ := pushList_run (S := S) dst [false] s1 hfit1
    (by rw [hd1]; simp only [List.length_append, List.length_singleton]; omega)
  have hfin : update s1 dst (s1 dst ++ [false]) =
      update (update s dst (s dst ++ encBits w)) src [] := by
    rw [hd1, encBits_eq]
    funext r
    by_cases hr : r = src
    · subst hr; simp [hs1, Ne.symm hne]
    · by_cases hr' : r = dst
      · subst hr'; simp [hr]
      · simp [hr, hr', hs1]
  rw [hfin] at h₂
  refine ⟨N₁ + N₂, C₁ + C₂, .seq h₁ h₂, ?_⟩
  rw [hd1] at hC₂
  simp only [List.length_append, List.length_cons, List.length_nil] at hC₂
  nlinarith

/-- Remove the first `k` bits of `src`. -/
def popN (src : Fin R) : ℕ → Stmt (Instr R)
  | 0 => skipS
  | k + 1 => .seq (.prim (.popFront src)) (popN src k)

theorem popN_run {S : ℕ} (src : Fin R) :
    ∀ (k : ℕ) (pre rest : List Bool) (s : Regs R), pre.length = k → s src = pre ++ rest →
      Fits S s → ∃ N C, Stmt.BigStep (basicSem R) (Fits S) (popN src k) s N C
          (update s src rest) ∧ C ≤ (k + 1) * ((s src).length + 1) := by
  intro k
  induction k with
  | zero =>
    intro pre rest s hpre hs hfit
    have : pre = [] := List.eq_nil_of_length_eq_zero hpre
    subst this
    refine ⟨1, 1, ?_, by nlinarith⟩
    have : update s src rest = s := by
      rw [List.nil_append] at hs; rw [← hs]; exact update_eq_self src s
    rw [this]; exact skipS_run hfit
  | succ k ih =>
    intro pre rest s hpre hs hfit
    cases pre with
    | nil => simp at hpre
    | cons b pre =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hpre
      set s1 := update s src (pre ++ rest) with hs1
      have hfit1 : Fits S s1 := by
        intro r; by_cases hr : r = src
        · subst hr; rw [hs1, update_self]; have := hfit r; rw [hs] at this; simp at this ⊢; omega
        · rw [hs1, update_of_ne hr]; exact hfit r
      have hpop : Stmt.BigStep (basicSem R) (Fits S) (.prim (.popFront src)) s 1
          (1 + (s src).length) s1 :=
        Stmt.BigStep.prim (p := Instr.popFront src) (s := s) (s' := s1) (b := true) hfit trivial
          (by simp [basicSem, Instr.eval, hs, hs1]) hfit1
      obtain ⟨N, C, hrun, hC⟩ := ih pre rest s1 hpre (by rw [hs1, update_self]) hfit1
      have hfin : update s1 src rest = update s src rest := by rw [hs1, update_idem]
      rw [hfin] at hrun
      refine ⟨1 + N, (1 + (s src).length) + C, .seq hpop hrun, ?_⟩
      have h1 : (s1 src).length ≤ (s src).length := by
        rw [hs1, update_self, hs]; simp
      have h2 := Nat.mul_le_mul_left (k + 1) (Nat.add_le_add_right h1 1)
      nlinarith

/-- One element of an encoded bit list: drop the cons marker, read the element. -/
def valBody (dst src : Fin R) : Stmt (Instr R) :=
  .seq (.prim (.popFront src))
    (.ite (.headIs src true) (.seq (.prim (.pushBack dst true)) (popN src 3))
      (.seq (.prim (.pushBack dst false)) (popN src 1)))

def valLoop (dst src : Fin R) : Stmt (Instr R) := .loop (.headIs src true) true (valBody dst src)

theorem valLoop_run {S : ℕ} {dst src : Fin R} (hne : dst ≠ src) :
    ∀ (w : List Bool) (s : Regs R), s src = encBits w → Fits S s →
      (s dst).length + w.length ≤ S →
      ∃ N C, Stmt.BigStep (basicSem R) (Fits S) (valLoop dst src) s N C
          (update (update s dst (s dst ++ w)) src [false]) ∧
        C ≤ (w.length + 1) * (12 * ((s dst).length + (encBits w).length + 3)) := by
  have hsd : src ≠ dst := Ne.symm hne
  intro w
  induction w with
  | nil =>
    intro s hw hs _
    refine ⟨1, 1, ?_, by nlinarith⟩
    have hfin : update (update s dst (s dst ++ [])) src [false] = s := by
      funext r
      by_cases hr : r = src
      · subst hr; simp [hw, encBits_nil]
      · by_cases hr' : r = dst
        · subst hr'; simp [hr]
        · simp [hr]
    rw [hfin]
    exact .loopF (b := false) hs trivial (by simp [basicSem, Instr.eval, hw, encBits_nil])
      (by decide) hs
  | cons x rest ih =>
    intro s hw hs hlen
    simp only [List.length_cons] at hlen
    have hw' : s src = true :: ((if x then [true, false, false] else [false]) ++ encBits rest) := by
      rw [hw, encBits_cons]; cases x <;> rfl
    set s1 := update s src ((if x then [true, false, false] else [false]) ++ encBits rest) with hs1
    have hfit1 : Fits S s1 := by
      intro r; by_cases hr : r = src
      · subst hr; rw [hs1, update_self]; have := hs r; rw [hw'] at this
        simp only [List.length_cons, List.length_append] at this ⊢; omega
      · rw [hs1, update_of_ne hr]; exact hs r
    have hpop : Stmt.BigStep (basicSem R) (Fits S) (.prim (.popFront src)) s 1
        (1 + (s src).length) s1 :=
      Stmt.BigStep.prim (p := Instr.popFront src) (s := s) (s' := s1) (b := true) hs trivial
        (by simp [basicSem, Instr.eval, hw', hs1]) hfit1
    set s2 := update s1 dst (s dst ++ [x]) with hs2
    have hs1dst : s1 dst = s dst := by rw [hs1, update_of_ne hne]
    have hfit2 : Fits S s2 := by
      intro r; by_cases hr : r = dst
      · subst hr; rw [hs2, update_self]; simp; omega
      · rw [hs2, update_of_ne hr]; exact hfit1 r
    have hpush : Stmt.BigStep (basicSem R) (Fits S) (.prim (.pushBack dst x)) s1 1
        (1 + (s dst).length) s2 := by
      have := Stmt.BigStep.prim (σ := basicSem R) (Inv := Fits S) (p := .pushBack dst x)
        (s := s1) (s' := s2) (b := true) hfit1 trivial
        (by simp [basicSem, Instr.eval, hs1dst, hs2]) hfit2
      simpa [basicSem, Instr.cost, hs1dst] using this
    have hs2src : s2 src = (if x then [true, false, false] else [false]) ++ encBits rest := by
      rw [hs2, update_of_ne hsd, hs1, update_self]
    obtain ⟨Np, Cp, hpopN, hCp⟩ := popN_run (S := S) src (if x then 3 else 1)
      (if x then [true, false, false] else [false]) (encBits rest) s2 (by cases x <;> rfl)
      hs2src hfit2
    set s3 := update s2 src (encBits rest) with hs3
    have hfit3 : Fits S s3 := hpopN.inv_end
    have hbranch : Stmt.BigStep (basicSem R) (Fits S)
        (.ite (.headIs src true) (.seq (.prim (.pushBack dst true)) (popN src 3))
          (.seq (.prim (.pushBack dst false)) (popN src 1))) s1 (1 + Np + 1)
        (1 + ((1 + (s dst).length) + Cp)) s3 := by
      cases x with
      | true =>
        exact .iteT (s' := s1) hfit1 trivial (by simp [basicSem, Instr.eval, hs1])
          (.seq hpush hpopN)
      | false =>
        exact .iteF (s' := s1) hfit1 trivial (by simp [basicSem, Instr.eval, hs1])
          (.seq hpush hpopN)
    have hs3src : s3 src = encBits rest := by rw [hs3, update_self]
    have hs3dst : s3 dst = s dst ++ [x] := by rw [hs3, update_of_ne hne, hs2, update_self]
    obtain ⟨N, C, hrun, hC⟩ := ih s3 hs3src hfit3 (by rw [hs3dst]; simp; omega)
    have hfin : update (update s3 dst (s3 dst ++ rest)) src [false] =
        update (update s dst (s dst ++ x :: rest)) src [false] := by
      funext r
      by_cases hr : r = src
      · subst hr; simp
      · by_cases hr' : r = dst
        · subst hr'; simp [hr, hs3dst]
        · simp [hr, hr', hs3, hs2, hs1]
    rw [hfin] at hrun
    refine ⟨1 + (1 + Np + 1) + N + 1,
      1 + ((1 + (s src).length) + (1 + ((1 + (s dst).length) + Cp))) + C,
      .loopT hs trivial (by simp [basicSem, Instr.eval, hw']) (.seq hpop hbranch) hrun, ?_⟩
    have hsrc_len : (s src).length = (encBits (x :: rest)).length := by rw [hw]
    have hs2len : (s2 src).length ≤ (encBits (x :: rest)).length := by
      rw [hs2src, encBits_cons]; cases x <;> simp [elemBits]
    have hrestlen : (encBits rest).length + 2 ≤ (encBits (x :: rest)).length := by
      rw [encBits_cons]; cases x <;> simp [elemBits]
    have hxn : (if x then 3 else 1) + 1 ≤ 4 := by cases x <;> simp
    have hCp' : Cp ≤ 4 * ((encBits (x :: rest)).length + 1) :=
      hCp.trans (Nat.mul_le_mul hxn (by omega))
    rw [hs3dst] at hC
    simp only [List.length_append, List.length_cons, List.length_nil] at hC ⊢
    nlinarith

/-- `dst := dst ++ w` where `src = encBits w`; `src := []`. -/
def valToRaw (dst src : Fin R) : Stmt (Instr R) := .seq (valLoop dst src) (popN src 1)

theorem valToRaw_run {S : ℕ} {dst src : Fin R} (hne : dst ≠ src) (w : List Bool) (s : Regs R)
    (hw : s src = encBits w) (hs : Fits S s) (hlen : (s dst).length + w.length ≤ S) :
    ∃ N C, Stmt.BigStep (basicSem R) (Fits S) (valToRaw dst src) s N C
        (update (update s dst (s dst ++ w)) src []) ∧
      C ≤ (w.length + 2) * (12 * ((s dst).length + (encBits w).length + 3)) := by
  obtain ⟨N₁, C₁, h₁, hC₁⟩ := valLoop_run hne w s hw hs hlen
  set s1 := update (update s dst (s dst ++ w)) src [false] with hs1
  have hfit1 : Fits S s1 := h₁.inv_end
  obtain ⟨N₂, C₂, h₂, hC₂⟩ := popN_run (S := S) src 1 [false] [] s1 rfl
    (by rw [hs1, update_self]; rfl) hfit1
  have hfin : update s1 src [] = update (update s dst (s dst ++ w)) src [] := by
    rw [hs1, update_idem]
  rw [hfin] at h₂
  refine ⟨N₁ + N₂, C₁ + C₂, .seq h₁ h₂, ?_⟩
  have : (s1 src).length = 1 := by rw [hs1, update_self]; rfl
  rw [this] at hC₂
  nlinarith

end QecReliability.RegMachine
