import RegMachine.GadgetsAppend

/-!
# Gadget: `pushFront`

`pushFrontM i b`: `reg i := b :: reg i` by a left-to-right shift with a carry, in
`2|r| + 2` steps inside `[-1, |r|]`. Together with `popFront` and `headIs` this gives
registers stack semantics.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.RegMachine
open QecReliability.OracleCost.MultiTape Turing Function RegSyms

section ShiftR
variable {k : ℕ} {Γ Λ : Type} [Fintype Γ] [Inhabited Γ] [Fintype Λ] [RegSyms Γ]
variable {M : Machine k Γ Λ} {W : Fin (k + 1) → Set ℤ}

/-- Left-to-right shift with a carry: the head cell receives the carried bit and the
old head bit becomes the new carry. The final carry is the last bit read. -/
theorem run_shiftR {q : Option Bool → Λ} {i : Fin (k + 1)} (cont : Γ → Prop)
    (htr : ∀ (c : Option Bool) (heads : Fin (k + 1) → Γ), cont (heads i) →
      M.transition (q c) heads =
        .advance (q (dec (heads i))) (update heads i (optSym c)) (moves1 i .right)) :
    ∀ (n : ℕ) (c : Option Bool) (C : Fin (k + 1) → ℤ → Γ) (P : Fin (k + 1) → ℤ),
      (∀ t : ℕ, t < n → cont (C i (P i + t))) → InW W P → (∀ t : ℕ, t ≤ n → P i + t ∈ W i) →
      ARun M W ⟨q c, C, P⟩ n
        ⟨q (if n = 0 then c else dec (C i (P i + n - 1))),
          update C i (fun z => if P i ≤ z ∧ z < P i + n then
            (if z = P i then optSym c else optSym (dec (C i (z - 1)))) else C i z),
          update P i (P i + n)⟩ := by
  intro n
  induction n with
  | zero =>
    intro c C P _ hP _
    have e1 : update P i (P i + ((0 : ℕ) : ℤ)) = P := by simp
    have e2 : update C i (fun z => if P i ≤ z ∧ z < P i + ((0 : ℕ) : ℤ) then
        (if z = P i then optSym c else optSym (dec (C i (z - 1)))) else C i z) = C := by
      have : (fun z => if P i ≤ z ∧ z < P i + ((0 : ℕ) : ℤ) then
          (if z = P i then optSym c else optSym (dec (C i (z - 1)))) else C i z) = C i := by
        funext z; rw [if_neg (by omega)]
      rw [this]; simp
    rw [e1, e2]; exact .nil hP
  | succ n ih =>
    intro c C P hc hP hr
    have hc0 : cont ((⟨q c, C, P⟩ : ACfg k Γ Λ).heads i) := by
      simpa using hc 0 (by omega)
    have hs : astep M ⟨q c, C, P⟩ =
        some ⟨q (dec (C i (P i))), update C i (update (C i) (P i) (optSym c)),
          update P i (P i + 1)⟩ := by
      simpa [Move.delta] using astep_write1 (M := M) (a := ⟨q c, C, P⟩) (htr _ _ hc0)
    have hrun := ih (dec (C i (P i))) (update C i (update (C i) (P i) (optSym c)))
      (update P i (P i + 1))
      (fun t ht => by
        have e : update P i (P i + 1) i + (t : ℤ) = P i + ((t + 1 : ℕ) : ℤ) := by
          simp only [update_self]; push_cast; ring
        rw [e, update_self, update_of_ne (by omega)]; exact hc (t + 1) (by omega))
      (hP.update (by simpa using hr 1 (by omega)))
      (fun t ht => by
        have e : update P i (P i + 1) i + (t : ℤ) = P i + ((t + 1 : ℕ) : ℤ) := by
          simp only [update_self]; push_cast; ring
        rw [e]; exact hr (t + 1) (by omega))
    refine ARun.cons hs hP (hrun.of_eq (ACfg.ext ?_ ?_ ?_))
    · simp only [update_self]
      by_cases hn : n = 0
      · subst hn; simp
      · rw [if_neg hn, if_neg (by omega),
          update_of_ne (show P i + 1 + (n : ℤ) - 1 ≠ P i by omega)]
        congr 3; push_cast; ring
    · simp only [update_self, update_idem]
      refine congrArg (update C i) (funext fun z => ?_)
      by_cases hz : z = P i
      · subst hz
        rw [if_neg (by omega), if_pos (by push_cast; omega), if_pos rfl, update_self]
      · rw [update_of_ne hz]
        by_cases hin : P i + 1 ≤ z ∧ z < P i + 1 + n
        · rw [if_pos hin, if_pos (show P i ≤ z ∧ z < P i + ((n + 1 : ℕ) : ℤ) by push_cast; omega),
            if_neg hz]
          by_cases hz1 : z = P i + 1
          · rw [if_pos hz1]
            subst hz1
            rw [add_sub_cancel_right]
          · rw [if_neg hz1, update_of_ne (show z - 1 ≠ P i by omega)]
        · rw [if_neg hin,
            if_neg (show ¬ (P i ≤ z ∧ z < P i + ((n + 1 : ℕ) : ℤ)) by push_cast; omega)]
    · simp only [update_self, update_idem]
      refine congrArg (update P i) ?_
      push_cast; ring

end ShiftR

variable {k : ℕ} {Γ : Type} [Fintype Γ] [Inhabited Γ] [RegSyms Γ]

inductive PushFL where
  | shift (c : Option Bool) | back | done
  deriving DecidableEq, Fintype

/-- `r := b :: r`. -/
def pushFrontM (i : Fin (k + 1)) (b : Bool) : Machine k Γ PushFL :=
  mkMachine (.shift (some b)) fun q heads =>
    match q, dec (heads i) with
    | .shift c, some x => .advance (.shift (some x)) (update heads i (optSym c)) (moves1 i .right)
    | .shift c, none => .advance .back (update heads i (optSym c)) (moves1 i .left)
    | .back, some _ => .advance .back heads (moves1 i .left)
    | .back, none => .advance .done heads (moves1 i .right)
    | .done, _ => .halt true

section PushFT
variable (i : Fin (k + 1)) (b : Bool) {heads : Fin (k + 1) → Γ}
theorem pushFrontM_shift_some (c : Option Bool) (h : dec (heads i) ≠ none) :
    (pushFrontM i b).transition (.shift c) heads =
      .advance (.shift (dec (heads i))) (update heads i (optSym c)) (moves1 i .right) := by
  cases hd : dec (heads i) with
  | none => exact absurd hd h
  | some x => simp [pushFrontM, mkMachine, hd]
theorem pushFrontM_shift_none (c : Option Bool) (h : dec (heads i) = none) :
    (pushFrontM i b).transition (.shift c) heads =
      .advance .back (update heads i (optSym c)) (moves1 i .left) := by
  simp [pushFrontM, mkMachine, h]
theorem pushFrontM_back_some (h : dec (heads i) ≠ none) :
    (pushFrontM i b).transition .back heads = .advance .back heads (moves1 i .left) := by
  cases hd : dec (heads i) with
  | none => exact absurd hd h
  | some x => simp [pushFrontM, mkMachine, hd]
theorem pushFrontM_back_none (h : dec (heads i) = none) :
    (pushFrontM i b).transition .back heads = .advance .done heads (moves1 i .right) := by
  simp [pushFrontM, mkMachine, h]
theorem pushFrontM_done : (pushFrontM i b).transition .done heads = .halt true := by
  simp [pushFrontM, mkMachine]
end PushFT

theorem cellOf_cons_shift (w : List Bool) (b : Bool) :
    update (fun z : ℤ => if 0 ≤ z ∧ z < (w.length : ℤ) then
        (if z = 0 then (optSym (some b) : Γ) else optSym (dec (cellOf w (z - 1) : Γ)))
      else cellOf w z) (w.length : ℤ)
      (optSym (if w.length = 0 then some b else dec (cellOf w ((w.length : ℤ) - 1) : Γ))) =
      cellOf (b :: w) := by
  funext z
  by_cases hz : z = w.length
  · subst hz
    rw [update_self]
    by_cases hw : w.length = 0
    · rw [if_pos hw]
      have : w = [] := List.eq_nil_of_length_eq_zero hw
      subst this
      simp [cellOf, bitAt]
    · rw [if_neg hw, optSym_dec_cellOf]
      simp only [cellOf]
      rw [show bitAt (b :: w) (w.length : ℤ) = bitAt w ((w.length : ℤ) - 1) by
        simp only [bitAt]
        rw [if_pos (by omega), if_pos (by omega)]
        rw [show ((w.length : ℤ)).toNat = (((w.length : ℤ) - 1).toNat) + 1 by omega]
        simp]
  · rw [update_of_ne hz]
    split_ifs with h hz0
    · subst hz0; simp [cellOf, bitAt]
    · rw [optSym_dec_cellOf]
      simp only [cellOf]
      congr 1
      simp only [bitAt]
      rw [if_pos (by omega), if_pos (by omega)]
      rw [show z.toNat = (z - 1).toNat + 1 by omega]
      simp
    · by_cases hneg : z < 0
      · rw [cellOf_neg hneg, cellOf_neg hneg]
      · rw [cellOf_ge (by omega), cellOf_ge (by simp; omega)]

theorem pushFront_spec (i : Fin (k + 1)) (b : Bool) (s : Fin (k + 1) → List Bool)
    {W : Fin (k + 1) → Set ℤ}
    (hW : ∀ t, (0 : ℤ) ∈ W t) (hWi : ∀ z : ℤ, -1 ≤ z → z ≤ (s i).length → z ∈ W i) :
    ARun (pushFrontM (Γ := Γ) i b) W (nf (.shift (some b)) s) (2 * (s i).length + 2)
        (nf .done (update s i (b :: s i))) ∧
      aanswer (pushFrontM (Γ := Γ) i b) (nf .done (update s i (b :: s i))) = some true := by
  have hP0 : InW W (fun _ => (0 : ℤ)) := hW
  obtain ⟨w, hw⟩ : ∃ w, w = s i := ⟨_, rfl⟩
  rw [← hw] at hWi ⊢
  have hregi : regC s i = (cellOf w : ℤ → Γ) := by simp [regC, hw]
  set C1 : Fin (k + 1) → ℤ → Γ := update (regC s) i (fun z => if 0 ≤ z ∧ z < (w.length : ℤ) then
      (if z = 0 then (optSym (some b) : Γ) else optSym (dec (cellOf w (z - 1) : Γ)))
    else cellOf w z) with hC1
  set c' : Option Bool := if w.length = 0 then some b else dec (cellOf w ((w.length : ℤ) - 1) : Γ)
    with hc'
  have h1 : ARun (pushFrontM (Γ := Γ) i b) W ⟨.shift (some b), regC s, fun _ => 0⟩ w.length
      ⟨.shift c', C1, pos1 i w.length⟩ := by
    have := run_shiftR (M := pushFrontM (Γ := Γ) i b) (W := W) (q := PushFL.shift) (i := i)
      (fun x => dec x ≠ none) (fun c _ h => pushFrontM_shift_some i b c h)
      w.length (some b) (regC s) (fun _ => 0)
      (fun t ht => by
        rw [hregi]
        have := cont_cellOf (Γ := Γ) (w := w) (z := t) (by omega) (by omega)
        simpa using this) hP0
      (fun t ht => by simpa using hWi t (by omega) (by omega))
    refine this.of_eq (ACfg.ext ?_ ?_ ?_)
    · simp only [hc', hregi, zero_add]
    · rw [hC1, hregi]
      simp only [zero_add]
    · simp [pos1]
  have h2 : astep (pushFrontM (Γ := Γ) i b) ⟨.shift c', C1, pos1 i w.length⟩ =
      some ⟨.back, update (regC s) i (cellOf (b :: w)), pos1 i (w.length - 1)⟩ := by
    have hd : dec ((⟨.shift c', C1, pos1 i w.length⟩ : ACfg k Γ PushFL).heads i) = none := by
      simp [hC1, bitAt_ge]
    have := astep_write1 (M := pushFrontM (Γ := Γ) i b) (a := ⟨.shift c', C1, pos1 i w.length⟩)
      (pushFrontM_shift_none i b c' hd)
    simp only [Move.delta] at this
    rw [this]
    congr 2
    · simp only [update_self, hC1, update_idem]
      rw [← cellOf_cons_shift w b]
    · simp only [update_self, update_idem]
      congr 1
  have h3 : ARun (pushFrontM (Γ := Γ) i b) W
      ⟨.back, update (regC s) i (cellOf (b :: w)), pos1 i (w.length - 1)⟩ w.length
      ⟨.back, update (regC s) i (cellOf (b :: w)), pos1 i (-1)⟩ := by
    have := run_scanL (M := pushFrontM (Γ := Γ) i b) (W := W) (q := .back) (i := i)
      (fun x => dec x ≠ none) (fun _ h => pushFrontM_back_some i b h)
      w.length (update (regC s) i (cellOf (b :: w))) (pos1 i (w.length - 1))
      (fun t ht => by
        have := cont_cellOf (Γ := Γ) (w := b :: w) (z := w.length - 1 - t) (by omega)
          (by simp; omega)
        simpa using this)
      (inW_pos1 hW (hWi _ (by omega) (by omega)))
      (fun t ht => by simpa using hWi (w.length - 1 - t) (by omega) (by omega))
    refine this.of_eq (ACfg.ext rfl rfl ?_)
    simp only [update_self, update_idem]
    congr 1; ring
  have h4 : astep (pushFrontM (Γ := Γ) i b)
      ⟨.back, update (regC s) i (cellOf (b :: w)), pos1 i (-1)⟩ =
      some ⟨.done, update (regC s) i (cellOf (b :: w)), pos1 i 0⟩ := by
    have := astep_move1 (M := pushFrontM (Γ := Γ) i b)
      (a := ⟨.back, update (regC s) i (cellOf (b :: w)), pos1 i (-1)⟩)
      (pushFrontM_back_none i b (by simp [bitAt_neg]))
    simpa [Move.delta] using this
  have hend : (⟨.done, update (regC s) i (cellOf (b :: w)), pos1 i 0⟩ : ACfg k Γ PushFL) =
      nf .done (update s i (b :: w)) := by
    refine ACfg.ext rfl ?_ (pos1_zero i)
    show _ = regC (update s i (b :: w))
    rw [regC_update]
  refine ⟨?_, aanswer_of_halt (pushFrontM_done i b)⟩
  have hrun := h1.trans (ARun.step h2 (h3.trans (ARun.single h4
      (inW_pos1 hW (hWi _ (by omega) (by omega))) (inW_pos1 hW (hW i)))) h1.end_mem)
  have e : w.length + (w.length + 1 + 1) = 2 * w.length + 2 := by ring
  rw [e] at hrun
  exact hrun.of_eq hend

end QecReliability.RegMachine
