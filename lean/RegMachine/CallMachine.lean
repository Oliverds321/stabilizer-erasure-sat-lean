import RegMachine.Engine
import RegMachine.Gadgets

/-!
# The oracle-call gadget: machine and local lemmas

`callM E e q` runs the engine `E` (over alphabet `ΓE`, `kE+1` tapes embedded into the
arena by `e`) on the contents of register `q`:

1. `init`: write an origin marker `eng default true` at cell 0 of every engine tape;
2. `copy`: copy the query bits to engine tape `e 0` as `eng (E.inputSymbol b) _`
   (keeping the origin flag), moving both heads right;
3. `rewind`: move both heads back to cell 0 (in lockstep with the query register);
4. `sim l`: simulate `E` step by step on the decoded engine tapes (`Cell.val`); every
   written engine cell becomes an `eng` cell, so the touched region is marked;
   when `E` halts with answer `b`, mark the current cells and start cleanup;
5. `clean b j`: for each engine tape `j`: go right to the end of the marked region,
   erase it right-to-left except the origin cell, come back right to the origin
   and erase it — the head ends on cell 0 of an all-blank tape;
6. `done b`: halt with `b`.

This file contains the machine, its transition lemmas, a lockstep rewind loop and
the generic single-tape cleanup lemma `run_cleanTape`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.RegMachine
open QecReliability.OracleCost.MultiTape QecReliability.OracleCost.MultiTape.InjectiveTapeLift
open Turing Function RegSyms

set_option backward.isDefEq.respectTransparency false in
/-- Cleanup phases of one engine tape. -/
inductive CleanPh where
  | right | erase | find
  deriving DecidableEq, Fintype

/-- Control labels of the call gadget. -/
inductive CallL (kE : ℕ) (ΛE : Type) where
  | init
  | copy
  | rewind
  | sim (l : ΛE)
  | clean (b : Bool) (j : Fin (kE + 1)) (ph : CleanPh)
  | done (b : Bool)
  deriving Fintype

namespace Cell
variable {ΓE : Type}

/-- Blank test. -/
def isBlank : Cell ΓE → Bool
  | .blank => true
  | _ => false

theorem isBlank_iff (x : Cell ΓE) : isBlank x = true ↔ x = .blank := by
  cases x <;> simp [isBlank]

/-- Erase a cell unless it carries the origin flag. -/
def keepO (x : Cell ΓE) : Cell ΓE := if org x then x else .blank

end Cell

/-- Next engine tape index. -/
def nextEng {kE : ℕ} (j : Fin (kE + 1)) : Option (Fin (kE + 1)) :=
  if h : j.val + 1 < kE + 1 then some ⟨j.val + 1, h⟩ else none

section Machine
variable {k kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]

/-- Copy function: a query bit becomes the engine input symbol, keeping the origin flag. -/
def gCopy (E : Machine kE ΓE ΛE) (x y : Cell ΓE) : Cell ΓE :=
  match dec x with
  | some b => .eng (E.inputSymbol b) (Cell.org y)
  | none => y

/-- Label after finishing the cleanup of engine tape `j`. -/
def afterClean (b : Bool) (j : Fin (kE + 1)) : CallL kE ΛE :=
  match nextEng j with
  | some j' => .clean b j' .right
  | none => .done b

/-- The oracle-call gadget. -/
def callM (E : Machine kE ΓE ΛE) (e : Embedding kE k) (q : Fin (k + 1)) :
    Machine k (Cell ΓE) (CallL kE ΛE) :=
  mkMachine .init fun lab heads =>
    match lab with
    | .init => .advance .copy (engWrite e heads (fun _ _ => .eng default true))
        (engMove e (fun _ => .stay))
    | .copy => match dec (heads q) with
      | some _ => .advance .copy (update heads (e 0) (gCopy E (heads q) (heads (e 0))))
          (moves2 (e 0) .right q .right)
      | none => .advance .rewind heads (moves2 (e 0) .left q .left)
    | .rewind => match dec (heads q) with
      | some _ => .advance .rewind heads (moves2 (e 0) .left q .left)
      | none => .advance (.sim E.start) heads (moves2 (e 0) .right q .right)
    | .sim l => match E.transition l (fun j => Cell.val (heads (e j))) with
      | .advance l' w mv => .advance (.sim l') (engWrite e heads (fun j x => .eng (w j) (Cell.org x)))
          (engMove e mv)
      | .halt b => .advance (.clean b 0 .right)
          (engWrite e heads (fun _ x => .eng (Cell.val x) (Cell.org x)))
          (engMove e (fun _ => .stay))
    | .clean b j .right => if Cell.isBlank (heads (e j))
        then .advance (.clean b j .erase) heads (moves1 (e j) .left)
        else .advance (.clean b j .right) heads (moves1 (e j) .right)
    | .clean b j .erase => if Cell.isBlank (heads (e j))
        then .advance (.clean b j .find) heads (moves1 (e j) .right)
        else .advance (.clean b j .erase) (update heads (e j) (Cell.keepO (heads (e j))))
          (moves1 (e j) .left)
    | .clean b j .find => if Cell.isBlank (heads (e j))
        then .advance (.clean b j .find) heads (moves1 (e j) .right)
        else .advance (afterClean b j) (update heads (e j) .blank) (moves1 (e j) .stay)
    | .done b => .halt b

section Tr
variable (E : Machine kE ΓE ΛE) (e : Embedding kE k) (q : Fin (k + 1))
  {heads : Fin (k + 1) → Cell ΓE}

theorem callM_init : (callM E e q).transition .init heads =
    .advance .copy (engWrite e heads (fun _ _ => .eng default true)) (engMove e (fun _ => .stay)) := by
  simp [callM, mkMachine]

theorem callM_copy_some (h : dec (heads q) ≠ none) : (callM E e q).transition .copy heads =
    .advance .copy (update heads (e 0) (gCopy E (heads q) (heads (e 0))))
      (moves2 (e 0) .right q .right) := by
  cases hd : dec (heads q) with
  | none => exact absurd hd h
  | some x => simp [callM, mkMachine, hd]

theorem callM_copy_none (h : dec (heads q) = none) : (callM E e q).transition .copy heads =
    .advance .rewind heads (moves2 (e 0) .left q .left) := by
  simp [callM, mkMachine, h]

theorem callM_rewind_some (h : dec (heads q) ≠ none) : (callM E e q).transition .rewind heads =
    .advance .rewind heads (moves2 (e 0) .left q .left) := by
  cases hd : dec (heads q) with
  | none => exact absurd hd h
  | some x => simp [callM, mkMachine, hd]

theorem callM_rewind_none (h : dec (heads q) = none) : (callM E e q).transition .rewind heads =
    .advance (.sim E.start) heads (moves2 (e 0) .right q .right) := by
  simp [callM, mkMachine, h]

theorem callM_sim_advance {l l' : ΛE} {w : Fin (kE + 1) → ΓE} {mv : Fin (kE + 1) → Move}
    (h : E.transition l (fun j => Cell.val (heads (e j))) = .advance l' w mv) :
    (callM E e q).transition (.sim l) heads =
      .advance (.sim l') (engWrite e heads (fun j x => .eng (w j) (Cell.org x))) (engMove e mv) := by
  simp [callM, mkMachine, h]

theorem callM_sim_halt {l : ΛE} {b : Bool}
    (h : E.transition l (fun j => Cell.val (heads (e j))) = .halt b) :
    (callM E e q).transition (.sim l) heads =
      .advance (.clean b 0 .right) (engWrite e heads (fun _ x => .eng (Cell.val x) (Cell.org x)))
        (engMove e (fun _ => .stay)) := by
  simp [callM, mkMachine, h]

variable (b : Bool) (j : Fin (kE + 1))

theorem callM_right_nb (h : heads (e j) ≠ .blank) : (callM E e q).transition (.clean b j .right) heads =
    .advance (.clean b j .right) heads (moves1 (e j) .right) := by
  have : Cell.isBlank (heads (e j)) = false := by
    cases hb : Cell.isBlank (heads (e j))
    · rfl
    · exact absurd ((Cell.isBlank_iff _).mp hb) h
  simp [callM, mkMachine, this]

theorem callM_right_b (h : heads (e j) = .blank) : (callM E e q).transition (.clean b j .right) heads =
    .advance (.clean b j .erase) heads (moves1 (e j) .left) := by
  have : Cell.isBlank (heads (e j)) = true := (Cell.isBlank_iff _).mpr h
  simp [callM, mkMachine, this]

theorem callM_erase_nb (h : heads (e j) ≠ .blank) : (callM E e q).transition (.clean b j .erase) heads =
    .advance (.clean b j .erase) (update heads (e j) (Cell.keepO (heads (e j)))) (moves1 (e j) .left) := by
  have : Cell.isBlank (heads (e j)) = false := by
    cases hb : Cell.isBlank (heads (e j))
    · rfl
    · exact absurd ((Cell.isBlank_iff _).mp hb) h
  simp [callM, mkMachine, this]

theorem callM_erase_b (h : heads (e j) = .blank) : (callM E e q).transition (.clean b j .erase) heads =
    .advance (.clean b j .find) heads (moves1 (e j) .right) := by
  have : Cell.isBlank (heads (e j)) = true := (Cell.isBlank_iff _).mpr h
  simp [callM, mkMachine, this]

theorem callM_find_b (h : heads (e j) = .blank) : (callM E e q).transition (.clean b j .find) heads =
    .advance (.clean b j .find) heads (moves1 (e j) .right) := by
  have : Cell.isBlank (heads (e j)) = true := (Cell.isBlank_iff _).mpr h
  simp [callM, mkMachine, this]

theorem callM_find_nb (h : heads (e j) ≠ .blank) : (callM E e q).transition (.clean b j .find) heads =
    .advance (afterClean b j) (update heads (e j) .blank) (moves1 (e j) .stay) := by
  have : Cell.isBlank (heads (e j)) = false := by
    cases hb : Cell.isBlank (heads (e j))
    · rfl
    · exact absurd ((Cell.isBlank_iff _).mp hb) h
  simp [callM, mkMachine, this]

theorem callM_done : (callM E e q).transition (.done b) heads = .halt b := by
  simp [callM, mkMachine]

end Tr
end Machine

/-! ## Lockstep left scan -/

section Scan2
variable {k : ℕ} {Γ Λ : Type} [Fintype Γ] [Inhabited Γ] [Fintype Λ]
variable {M : Machine k Γ Λ} {W : Fin (k + 1) → Set ℤ}

/-- Move tapes `i` and `j` left together while tape `j` satisfies `cont`. -/
theorem run_scan2L {q : Λ} {i j : Fin (k + 1)} (hij : i ≠ j) (cont : Γ → Prop)
    (htr : ∀ heads : Fin (k + 1) → Γ, cont (heads j) →
      M.transition q heads = .advance q heads (moves2 i .left j .left)) :
    ∀ (n : ℕ) (C : Fin (k + 1) → ℤ → Γ) (P : Fin (k + 1) → ℤ),
      (∀ t : ℕ, t < n → cont (C j (P j - t))) → InW W P →
      (∀ t : ℕ, t ≤ n → P i - t ∈ W i) → (∀ t : ℕ, t ≤ n → P j - t ∈ W j) →
      ARun M W ⟨q, C, P⟩ n ⟨q, C, update (update P i (P i - n)) j (P j - n)⟩ := by
  intro n
  induction n with
  | zero =>
    intro C P _ hP _ _
    have e1 : update (update P i (P i - ((0 : ℕ) : ℤ))) j (P j - ((0 : ℕ) : ℤ)) = P := by simp
    rw [e1]; exact .nil hP
  | succ n ih =>
    intro C P hc hP hri hrj
    have hc0 : cont ((⟨q, C, P⟩ : ACfg k Γ Λ).heads j) := by
      simpa using hc 0 (by omega)
    have hs : astep M ⟨q, C, P⟩ = some ⟨q, C, update (update P i (P i - 1)) j (P j - 1)⟩ := by
      simpa [Move.delta, sub_eq_add_neg] using
        astep_move2 (M := M) (a := ⟨q, C, P⟩) hij (htr _ hc0)
    have hPi : update (update P i (P i - 1)) j (P j - 1) i = P i - 1 := by
      rw [update_of_ne hij, update_self]
    have hPj : update (update P i (P i - 1)) j (P j - 1) j = P j - 1 := by
      rw [update_self]
    have hrun := ih C (update (update P i (P i - 1)) j (P j - 1))
      (fun t ht => by
        rw [hPj]
        have e : P j - 1 - (t : ℤ) = P j - ((t + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [e]; exact hc (t + 1) (by omega))
      ((hP.update (by simpa using hri 1 (by omega))).update
        (by simpa using hrj 1 (by omega)))
      (fun t ht => by
        rw [hPi]
        have e : P i - 1 - (t : ℤ) = P i - ((t + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [e]; exact hri (t + 1) (by omega))
      (fun t ht => by
        rw [hPj]
        have e : P j - 1 - (t : ℤ) = P j - ((t + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [e]; exact hrj (t + 1) (by omega))
    refine ARun.cons hs hP (hrun.of_eq (ACfg.ext rfl rfl ?_))
    dsimp only
    rw [hPi, hPj]
    funext t
    by_cases htj : t = j
    · subst htj
      simp only [update_self]
      push_cast; ring
    · by_cases hti : t = i
      · subst hti
        simp only [update_self, update_of_ne htj]
        push_cast; ring
      · simp only [update_of_ne htj, update_of_ne hti]

end Scan2

/-! ## Cleanup of one engine tape -/

section Clean
variable {k : ℕ} {ΓE Λ : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype Λ]
variable {M : Machine k (Cell ΓE) Λ} {W : Fin (k + 1) → Set ℤ}

/-- Cleanup of a marked interval `[l, r] ∋ 0` (origin flag exactly at `0`) on tape `t`:
afterwards the tape is blank and its head is on cell `0`. -/
theorem run_cleanTape {qR qE qF qN : Λ} {t : Fin (k + 1)}
    (hR1 : ∀ heads : Fin (k + 1) → Cell ΓE, heads t ≠ .blank →
      M.transition qR heads = .advance qR heads (moves1 t .right))
    (hR2 : ∀ heads : Fin (k + 1) → Cell ΓE, heads t = .blank →
      M.transition qR heads = .advance qE heads (moves1 t .left))
    (hE1 : ∀ heads : Fin (k + 1) → Cell ΓE, heads t ≠ .blank →
      M.transition qE heads = .advance qE (update heads t (Cell.keepO (heads t))) (moves1 t .left))
    (hE2 : ∀ heads : Fin (k + 1) → Cell ΓE, heads t = .blank →
      M.transition qE heads = .advance qF heads (moves1 t .right))
    (hF1 : ∀ heads : Fin (k + 1) → Cell ΓE, heads t = .blank →
      M.transition qF heads = .advance qF heads (moves1 t .right))
    (hF2 : ∀ heads : Fin (k + 1) → Cell ΓE, heads t ≠ .blank →
      M.transition qF heads = .advance qN (update heads t .blank) (moves1 t .stay))
    (C : Fin (k + 1) → ℤ → Cell ΓE) (P : Fin (k + 1) → ℤ) (l r : ℤ) (hl : l ≤ 0) (hr : 0 ≤ r)
    (hpl : l ≤ P t) (hpr : P t ≤ r)
    (hin : ∀ z, l ≤ z → z ≤ r → C t z ≠ .blank ∧ Cell.org (C t z) = decide (z = 0))
    (hout : ∀ z, z < l ∨ r < z → C t z = .blank)
    (hP : InW W P) (hWt : ∀ z, l - 1 ≤ z → z ≤ r + 1 → z ∈ W t) :
    ∃ m : ℕ, (m : ℤ) ≤ 3 * (r - l + 1) + 2 ∧
      ARun M W ⟨qR, C, P⟩ m ⟨qN, update C t (fun _ => .blank), update P t 0⟩ := by
  obtain ⟨m1, hm1⟩ : ∃ m1 : ℕ, (m1 : ℤ) = r - P t + 1 := ⟨(r - P t + 1).toNat, by omega⟩
  obtain ⟨m2, hm2⟩ : ∃ m2 : ℕ, (m2 : ℤ) = r - l + 1 := ⟨(r - l + 1).toNat, by omega⟩
  obtain ⟨m3, hm3⟩ : ∃ m3 : ℕ, (m3 : ℤ) = -l := ⟨(-l).toNat, by omega⟩
  -- 1. go right to `r + 1`
  have h1 : ARun M W ⟨qR, C, P⟩ m1 ⟨qR, C, update P t (r + 1)⟩ := by
    have := run_scanR (M := M) (W := W) (q := qR) (i := t) (fun x => x ≠ .blank) hR1 m1 C P
      (fun i hi => (hin _ (by omega) (by omega)).1) hP
      (fun i hi => hWt _ (by omega) (by omega))
    refine this.of_eq (ACfg.ext rfl rfl ?_)
    refine congrArg (update P t) ?_
    omega
  have hP1 : InW W (update P t (r + 1)) := hP.update (hWt _ (by omega) (by omega))
  have h2 : astep M ⟨qR, C, update P t (r + 1)⟩ = some ⟨qE, C, update P t r⟩ := by
    have := astep_move1 (M := M) (a := ⟨qR, C, update P t (r + 1)⟩)
      (hR2 _ (by simpa using hout (r + 1) (Or.inr (by omega))))
    simp only [Move.delta] at this
    rw [this]
    congr 2
    simp only [update_self, update_idem]
    congr 1; ring
  -- 2. erase right to left, keeping the origin
  set C2 : Fin (k + 1) → ℤ → Cell ΓE :=
    update C t (fun z => if r - m2 < z ∧ z ≤ r then Cell.keepO (C t z) else C t z) with hC2
  have h3 : ARun M W ⟨qE, C, update P t r⟩ m2 ⟨qE, C2, update P t (l - 1)⟩ := by
    have := run_mapL (M := M) (W := W) (q := qE) (i := t) (fun x => x ≠ .blank) Cell.keepO hE1
      m2 C (update P t r)
      (fun i hi => by simpa using (hin (r - i) (by omega) (by omega)).1)
      (hP.update (hWt _ (by omega) (by omega)))
      (fun i hi => by simpa using hWt (r - i) (by omega) (by omega))
    refine this.of_eq (ACfg.ext rfl ?_ ?_)
    · simp only [update_self, hC2]
    · simp only [update_self, update_idem]
      congr 1; omega
  have hC2t : ∀ z, C2 t z = if l ≤ z ∧ z ≤ r then Cell.keepO (C t z) else C t z := by
    intro z
    simp only [hC2, update_self]
    by_cases h : l ≤ z ∧ z ≤ r
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  have hP3 : InW W (update P t (l - 1)) := hP.update (hWt _ (by omega) (by omega))
  have h4 : astep M ⟨qE, C2, update P t (l - 1)⟩ = some ⟨qF, C2, update P t l⟩ := by
    have hb : C2 t (l - 1) = .blank := by
      rw [hC2t, if_neg (by omega)]; exact hout _ (Or.inl (by omega))
    have := astep_move1 (M := M) (a := ⟨qE, C2, update P t (l - 1)⟩) (hE2 _ (by simpa using hb))
    simp only [Move.delta] at this
    rw [this]
    congr 2
    simp only [update_self, update_idem]
    congr 1; ring
  -- 3. come back to the origin over erased cells
  have hblank : ∀ z, z ≠ 0 → C2 t z = .blank := by
    intro z hz
    rw [hC2t]
    split_ifs with h
    · have := (hin z h.1 h.2).2
      simp only [Cell.keepO, this, hz, decide_false, Bool.false_eq_true, if_false]
    · exact hout z (by omega)
  have h5 : ARun M W ⟨qF, C2, update P t l⟩ m3 ⟨qF, C2, update P t 0⟩ := by
    have := run_scanR (M := M) (W := W) (q := qF) (i := t) (fun x => x = .blank) hF1 m3 C2
      (update P t l)
      (fun i hi => by simpa using hblank (l + i) (by omega))
      (hP.update (hWt _ (by omega) (by omega)))
      (fun i hi => by simpa using hWt (l + i) (by omega) (by omega))
    refine this.of_eq (ACfg.ext rfl rfl ?_)
    simp only [update_self, update_idem]
    congr 1; omega
  have hP5 : InW W (update P t 0) := hP.update (hWt _ (by omega) (by omega))
  have horg : C2 t 0 ≠ .blank := by
    rw [hC2t, if_pos ⟨hl, hr⟩]
    have := hin 0 hl hr
    simp only [decide_true] at this
    simp only [Cell.keepO, this.2, if_true]
    exact this.1
  have h6 : astep M ⟨qF, C2, update P t 0⟩ =
      some ⟨qN, update C t (fun _ => .blank), update P t 0⟩ := by
    have := astep_write1 (M := M) (a := ⟨qF, C2, update P t 0⟩) (hF2 _ (by simpa using horg))
    simp only [Move.delta] at this
    rw [this]
    have hfin : update (C2 t) 0 Cell.blank = fun _ => Cell.blank := by
      funext z
      by_cases hz : z = 0
      · subst hz; simp
      · rw [update_of_ne hz]; exact hblank z hz
    congr 2
    · rw [update_self, hfin, hC2, update_idem]
    · simp only [update_self, update_idem, add_zero]
  refine ⟨m1 + (m2 + 1 + (m3 + 1)) + 1, ?_, ?_⟩
  · push_cast; omega
  · have := h1.trans (ARun.step h2 (h3.trans (ARun.step h4 (h5.trans (ARun.single h6 hP5 hP5))
      hP3)) hP1)
    exact this.of_eq rfl |>.of_eq rfl |> fun h => by
      have e : m1 + (m2 + 1 + (m3 + 1)) + 1 = m1 + (m2 + (m3 + 1) + 1) + 1 := by ring
      rw [e]; exact h

end Clean

end QecReliability.RegMachine
