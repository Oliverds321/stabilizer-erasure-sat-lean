import RegMachine.Loops
import Mathlib.Tactic.DeriveFintype

/-!
# Primitive gadgets

Each gadget is a small `MultiTape.Machine k Γ L`, generic in the tape indices it
touches. Register `t` lives on tape `t` in normal form `nf` (contents `cellOf`,
every head on absolute cell `0`). Each `*_spec` theorem: from the normal form of `s`
the gadget runs, in an explicit number of steps, to the normal form of the
updated registers, with all heads inside any window `W` that contains `0` on every
tape and `[-1, ℓ]` on the touched tapes (`ℓ` = length bound), and then halts.
Untouched tapes are literally unchanged (generic `ARun` statement).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.RegMachine
open QecReliability.OracleCost.MultiTape Turing Function RegSyms

variable {k : ℕ} {Γ : Type} [Fintype Γ] [Inhabited Γ] [RegSyms Γ]

/-- A machine over a register alphabet whose input symbols are the register bits. -/
def mkMachine {L : Type} [Fintype L] (start : L) (tr : L → (Fin (k + 1) → Γ) → Action k Γ L) :
    Machine k Γ L :=
  ⟨start, sym, sym_injective, sym_ne_default, tr⟩

/-- Abstract normal form: register `t` on tape `t`, every head on cell `0`. -/
def nf {L : Type} (q : L) (s : Fin (k + 1) → List Bool) : ACfg k Γ L :=
  ⟨q, fun t => cellOf (s t), fun _ => 0⟩

/-- Contents of the normal form of `s`. -/
abbrev regC (s : Fin (k + 1) → List Bool) : Fin (k + 1) → ℤ → Γ := fun t => cellOf (s t)

/-- Head positions: tape `i` at `v`, others at `0`. -/
abbrev pos1 (i : Fin (k + 1)) (v : ℤ) : Fin (k + 1) → ℤ := update (fun _ => 0) i v

theorem regC_update (s : Fin (k + 1) → List Bool) (i : Fin (k + 1)) (w : List Bool) :
    (regC (update s i w) : Fin (k + 1) → ℤ → Γ) = update (regC s) i (cellOf w) := by
  funext t
  by_cases h : t = i
  · subst h; simp [regC]
  · simp [regC, h]

theorem pos1_zero (i : Fin (k + 1)) : pos1 i 0 = fun _ => 0 := by
  funext t; by_cases h : t = i <;> simp [h]

theorem inW_pos1 {W : Fin (k + 1) → Set ℤ} (hW : ∀ t, (0 : ℤ) ∈ W t) {i : Fin (k + 1)} {v : ℤ}
    (hv : v ∈ W i) : InW W (pos1 i v) :=
  InW.update (fun t => hW t) hv

theorem cont_cellOf {w : List Bool} {z : ℤ} (h0 : 0 ≤ z) (hz : z < w.length) :
    dec (cellOf w z : Γ) ≠ none := by
  rw [dec_cellOf]; exact bitAt_lt h0 hz

/-! ## `clear` -/

set_option backward.isDefEq.respectTransparency false in
inductive ClearL where
  | scan | erase | done
  deriving DecidableEq, Fintype

/-- `r := []`: scan right to the end, erase leftwards, step back onto cell 0. -/
def clearM (i : Fin (k + 1)) : Machine k Γ ClearL :=
  mkMachine .scan fun q heads =>
    match q, dec (heads i) with
    | .scan, some _ => .advance .scan heads (moves1 i .right)
    | .scan, none => .advance .erase heads (moves1 i .left)
    | .erase, some _ => .advance .erase (update heads i default) (moves1 i .left)
    | .erase, none => .advance .done heads (moves1 i .right)
    | .done, _ => .halt true

section ClearT
variable (i : Fin (k + 1)) {heads : Fin (k + 1) → Γ}
theorem clearM_scan_some (h : dec (heads i) ≠ none) :
    (clearM i).transition .scan heads = .advance .scan heads (moves1 i .right) := by
  cases hd : dec (heads i) with
  | none => exact absurd hd h
  | some b => simp [clearM, mkMachine, hd]
theorem clearM_scan_none (h : dec (heads i) = none) :
    (clearM i).transition .scan heads = .advance .erase heads (moves1 i .left) := by
  simp [clearM, mkMachine, h]
theorem clearM_erase_some (h : dec (heads i) ≠ none) :
    (clearM i).transition .erase heads =
      .advance .erase (update heads i default) (moves1 i .left) := by
  cases hd : dec (heads i) with
  | none => exact absurd hd h
  | some b => simp [clearM, mkMachine, hd]
theorem clearM_erase_none (h : dec (heads i) = none) :
    (clearM i).transition .erase heads = .advance .done heads (moves1 i .right) := by
  simp [clearM, mkMachine, h]
theorem clearM_done : (clearM i).transition .done heads = .halt true := by
  simp [clearM, mkMachine]
end ClearT

theorem clear_spec (i : Fin (k + 1)) (s : Fin (k + 1) → List Bool) {W : Fin (k + 1) → Set ℤ}
    (hW : ∀ t, (0 : ℤ) ∈ W t) (hWi : ∀ z : ℤ, -1 ≤ z → z ≤ (s i).length → z ∈ W i) :
    ARun (clearM (Γ := Γ) i) W (nf .scan s) (2 * (s i).length + 2) (nf .done (update s i [])) ∧
      aanswer (clearM (Γ := Γ) i) (nf .done (update s i [])) = some true := by
  have hP0 : InW W (fun _ => (0 : ℤ)) := hW
  -- scan right
  have h1 : ARun (clearM (Γ := Γ) i) W ⟨.scan, regC s, fun _ => 0⟩ (s i).length
      ⟨.scan, regC s, pos1 i (s i).length⟩ := by
    have := run_scanR (M := clearM (Γ := Γ) i) (W := W) (q := .scan) (i := i)
      (fun x => dec x ≠ none) (fun _ h => clearM_scan_some i h)
      (s i).length (regC s) (fun _ => 0)
      (fun t ht => by
        have := cont_cellOf (Γ := Γ) (w := s i) (z := t) (by omega) (by omega)
        simpa using this) hP0
      (fun t ht => by simpa using hWi t (by omega) (by omega))
    simpa using this
  -- turn around
  have h2 : astep (clearM (Γ := Γ) i) ⟨.scan, regC s, pos1 i (s i).length⟩ =
      some ⟨.erase, regC s, pos1 i ((s i).length - 1)⟩ := by
    have := astep_move1 (M := clearM (Γ := Γ) i) (a := ⟨.scan, regC s, pos1 i (s i).length⟩)
      (clearM_scan_none i (by simp [bitAt_ge]))
    simpa [Move.delta, sub_eq_add_neg] using this
  -- erase leftwards
  have h3 : ARun (clearM (Γ := Γ) i) W ⟨.erase, regC s, pos1 i ((s i).length - 1)⟩ (s i).length
      ⟨.erase, update (regC s) i (fun _ => default), pos1 i (-1)⟩ := by
    have := run_mapL (M := clearM (Γ := Γ) i) (W := W) (q := .erase) (i := i)
      (fun x => dec x ≠ none) (fun _ => default) (fun _ h => clearM_erase_some i h)
      (s i).length (regC s) (pos1 i ((s i).length - 1))
      (fun t ht => by
        have := cont_cellOf (Γ := Γ) (w := s i) (z := (s i).length - 1 - t) (by omega) (by omega)
        simpa using this)
      (inW_pos1 hW (hWi _ (by omega) (by omega)))
      (fun t ht => by simpa using hWi ((s i).length - 1 - t) (by omega) (by omega))
    refine this.of_eq (ACfg.ext rfl ?_ ?_)
    · simp only [update_self]
      refine congrArg (update (regC s) i) (funext fun z => ?_)
      split_ifs with hz
      · rfl
      · simp only [regC]
        by_cases hz0 : z < 0
        · exact cellOf_neg hz0
        · exact cellOf_ge (by omega)
    · simp only [update_self, update_idem]
      congr 1; ring
  -- step back onto cell 0
  have h4 : astep (clearM (Γ := Γ) i) ⟨.erase, update (regC s) i (fun _ => default), pos1 i (-1)⟩ =
      some ⟨.done, update (regC s) i (fun _ => default), pos1 i 0⟩ := by
    have := astep_move1 (M := clearM (Γ := Γ) i)
      (a := ⟨.erase, update (regC s) i (fun _ => default), pos1 i (-1)⟩)
      (clearM_erase_none i (by simp))
    simpa [Move.delta] using this
  have hend : (⟨.done, update (regC s) i (fun _ => default), pos1 i 0⟩ : ACfg k Γ ClearL) =
      nf .done (update s i []) := by
    refine ACfg.ext rfl ?_ (pos1_zero i)
    show _ = regC (update s i [])
    rw [regC_update, cellOf_nil]
  refine ⟨?_, aanswer_of_halt (clearM_done i)⟩
  have hrun := h1.trans (ARun.step h2 (h3.trans (ARun.single h4
      (inW_pos1 hW (hWi _ (by omega) (by omega))) (inW_pos1 hW (hW i)))) h1.end_mem)
  have e : (s i).length + ((s i).length + 1 + 1) = 2 * (s i).length + 2 := by ring
  rw [e] at hrun
  exact hrun.of_eq hend

/-! ## Word lemmas -/

theorem cellOf_snoc (w : List Bool) (b : Bool) :
    update (cellOf w : ℤ → Γ) (w.length : ℤ) (sym b) = cellOf (w ++ [b]) := by
  funext z
  by_cases hz : z = w.length
  · subst hz
    simp only [update_self]
    simp [cellOf, bitAt]
  · rw [update_of_ne hz]
    by_cases hlt : z < w.length
    · simp [cellOf, bitAt_append_lt hlt]
    · rw [cellOf_ge (by omega), cellOf_ge (by simp; omega)]

theorem cellOf_append (u v : List Bool) :
    (fun z : ℤ => if (u.length : ℤ) ≤ z ∧ z < u.length + v.length then
        (optSym (dec (cellOf v (z - u.length) : Γ)) : Γ) else cellOf u z) = cellOf (u ++ v) := by
  funext z
  split_ifs with h
  · simp only [optSym_dec_cellOf]
    simp [cellOf, bitAt_append_ge h.1]
  · by_cases hlt : z < u.length
    · simp [cellOf, bitAt_append_lt hlt]
    · rw [cellOf_ge (by omega), cellOf_ge (by simp; omega)]

theorem cellOf_tail (w : List Bool) :
    (fun z : ℤ => if (w.length : ℤ) - 1 - w.length < z ∧ z ≤ w.length - 1 then
        (if z = w.length - 1 then optSym none else optSym (dec (cellOf w (z + 1) : Γ)))
      else (cellOf w z : Γ)) = cellOf w.tail := by
  funext z
  split_ifs with h hz
  · rw [optSym_none, cellOf_ge (by simp; omega)]
  · rw [optSym_dec_cellOf]
    simp only [cellOf]
    rw [bitAt_tail (by omega)]
  · by_cases hz0 : z < 0
    · rw [cellOf_neg hz0, cellOf_neg hz0]
    · rw [cellOf_ge (by omega), cellOf_ge (by simp; omega)]

/-! ## `pushBack` -/

set_option backward.isDefEq.respectTransparency false in
inductive PushL where
  | scan | back | done
  deriving DecidableEq, Fintype

/-- `r := r ++ [b]`: scan right, write `b`, scan back left, step onto cell 0. -/
def pushBackM (i : Fin (k + 1)) (b : Bool) : Machine k Γ PushL :=
  mkMachine .scan fun q heads =>
    match q, dec (heads i) with
    | .scan, some _ => .advance .scan heads (moves1 i .right)
    | .scan, none => .advance .back (update heads i (sym b)) (moves1 i .left)
    | .back, some _ => .advance .back heads (moves1 i .left)
    | .back, none => .advance .done heads (moves1 i .right)
    | .done, _ => .halt true

section PushT
variable (i : Fin (k + 1)) (b : Bool) {heads : Fin (k + 1) → Γ}
theorem pushBackM_scan_some (h : dec (heads i) ≠ none) :
    (pushBackM i b).transition .scan heads = .advance .scan heads (moves1 i .right) := by
  cases hd : dec (heads i) with
  | none => exact absurd hd h
  | some x => simp [pushBackM, mkMachine, hd]
theorem pushBackM_scan_none (h : dec (heads i) = none) :
    (pushBackM i b).transition .scan heads =
      .advance .back (update heads i (sym b)) (moves1 i .left) := by
  simp [pushBackM, mkMachine, h]
theorem pushBackM_back_some (h : dec (heads i) ≠ none) :
    (pushBackM i b).transition .back heads = .advance .back heads (moves1 i .left) := by
  cases hd : dec (heads i) with
  | none => exact absurd hd h
  | some x => simp [pushBackM, mkMachine, hd]
theorem pushBackM_back_none (h : dec (heads i) = none) :
    (pushBackM i b).transition .back heads = .advance .done heads (moves1 i .right) := by
  simp [pushBackM, mkMachine, h]
theorem pushBackM_done : (pushBackM i b).transition .done heads = .halt true := by
  simp [pushBackM, mkMachine]
end PushT

theorem pushBack_spec (i : Fin (k + 1)) (b : Bool) (s : Fin (k + 1) → List Bool)
    {W : Fin (k + 1) → Set ℤ}
    (hW : ∀ t, (0 : ℤ) ∈ W t) (hWi : ∀ z : ℤ, -1 ≤ z → z ≤ (s i).length → z ∈ W i) :
    ARun (pushBackM (Γ := Γ) i b) W (nf .scan s) (2 * (s i).length + 2)
        (nf .done (update s i (s i ++ [b]))) ∧
      aanswer (pushBackM (Γ := Γ) i b) (nf .done (update s i (s i ++ [b]))) = some true := by
  have hP0 : InW W (fun _ => (0 : ℤ)) := hW
  have h1 : ARun (pushBackM (Γ := Γ) i b) W ⟨.scan, regC s, fun _ => 0⟩ (s i).length
      ⟨.scan, regC s, pos1 i (s i).length⟩ := by
    have := run_scanR (M := pushBackM (Γ := Γ) i b) (W := W) (q := .scan) (i := i)
      (fun x => dec x ≠ none) (fun _ h => pushBackM_scan_some i b h)
      (s i).length (regC s) (fun _ => 0)
      (fun t ht => by
        have := cont_cellOf (Γ := Γ) (w := s i) (z := t) (by omega) (by omega)
        simpa using this) hP0
      (fun t ht => by simpa using hWi t (by omega) (by omega))
    simpa using this
  have h2 : astep (pushBackM (Γ := Γ) i b) ⟨.scan, regC s, pos1 i (s i).length⟩ =
      some ⟨.back, update (regC s) i (cellOf (s i ++ [b])), pos1 i ((s i).length - 1)⟩ := by
    have := astep_write1 (M := pushBackM (Γ := Γ) i b)
      (a := ⟨.scan, regC s, pos1 i (s i).length⟩)
      (pushBackM_scan_none i b (by simp [bitAt_ge]))
    simp only [Move.delta] at this
    rw [this]
    congr 2
    · simp only [update_self]
      rw [cellOf_snoc]
    · simp only [update_self, update_idem]
      congr 1
  have h3 : ARun (pushBackM (Γ := Γ) i b) W
      ⟨.back, update (regC s) i (cellOf (s i ++ [b])), pos1 i ((s i).length - 1)⟩ (s i).length
      ⟨.back, update (regC s) i (cellOf (s i ++ [b])), pos1 i (-1)⟩ := by
    have := run_scanL (M := pushBackM (Γ := Γ) i b) (W := W) (q := .back) (i := i)
      (fun x => dec x ≠ none) (fun _ h => pushBackM_back_some i b h)
      (s i).length (update (regC s) i (cellOf (s i ++ [b]))) (pos1 i ((s i).length - 1))
      (fun t ht => by
        have := cont_cellOf (Γ := Γ) (w := s i ++ [b]) (z := (s i).length - 1 - t) (by omega)
          (by simp; omega)
        simpa using this)
      (inW_pos1 hW (hWi _ (by omega) (by omega)))
      (fun t ht => by simpa using hWi ((s i).length - 1 - t) (by omega) (by omega))
    refine this.of_eq (ACfg.ext rfl rfl ?_)
    simp only [update_self, update_idem]
    congr 1; ring
  have h4 : astep (pushBackM (Γ := Γ) i b)
      ⟨.back, update (regC s) i (cellOf (s i ++ [b])), pos1 i (-1)⟩ =
      some ⟨.done, update (regC s) i (cellOf (s i ++ [b])), pos1 i 0⟩ := by
    have := astep_move1 (M := pushBackM (Γ := Γ) i b)
      (a := ⟨.back, update (regC s) i (cellOf (s i ++ [b])), pos1 i (-1)⟩)
      (pushBackM_back_none i b (by simp [bitAt_neg]))
    simpa [Move.delta] using this
  have hend : (⟨.done, update (regC s) i (cellOf (s i ++ [b])), pos1 i 0⟩ : ACfg k Γ PushL) =
      nf .done (update s i (s i ++ [b])) := by
    refine ACfg.ext rfl ?_ (pos1_zero i)
    show _ = regC (update s i (s i ++ [b]))
    rw [regC_update]
  refine ⟨?_, aanswer_of_halt (pushBackM_done i b)⟩
  have hrun := h1.trans (ARun.step h2 (h3.trans (ARun.single h4
      (inW_pos1 hW (hWi _ (by omega) (by omega))) (inW_pos1 hW (hW i)))) h1.end_mem)
  have e : (s i).length + ((s i).length + 1 + 1) = 2 * (s i).length + 2 := by ring
  rw [e] at hrun
  exact hrun.of_eq hend

/-! ## `popFront` -/

inductive PopL where
  | scan | shift (c : Option Bool) | done
  deriving DecidableEq, Fintype

/-- `r := r.tail`: scan right, shift every cell one to the left (right to left,
carrying the bit), step onto cell 0. -/
def popFrontM (i : Fin (k + 1)) : Machine k Γ PopL :=
  mkMachine .scan fun q heads =>
    match q, dec (heads i) with
    | .scan, some _ => .advance .scan heads (moves1 i .right)
    | .scan, none => .advance (.shift none) heads (moves1 i .left)
    | .shift c, some x => .advance (.shift (some x)) (update heads i (optSym c)) (moves1 i .left)
    | .shift _, none => .advance .done heads (moves1 i .right)
    | .done, _ => .halt true

section PopT
variable (i : Fin (k + 1)) {heads : Fin (k + 1) → Γ}
theorem popFrontM_scan_some (h : dec (heads i) ≠ none) :
    (popFrontM i).transition .scan heads = .advance .scan heads (moves1 i .right) := by
  cases hd : dec (heads i) with
  | none => exact absurd hd h
  | some x => simp [popFrontM, mkMachine, hd]
theorem popFrontM_scan_none (h : dec (heads i) = none) :
    (popFrontM i).transition .scan heads = .advance (.shift none) heads (moves1 i .left) := by
  simp [popFrontM, mkMachine, h]
theorem popFrontM_shift_some (c : Option Bool) (h : dec (heads i) ≠ none) :
    (popFrontM i).transition (.shift c) heads =
      .advance (.shift (dec (heads i))) (update heads i (optSym c)) (moves1 i .left) := by
  cases hd : dec (heads i) with
  | none => exact absurd hd h
  | some x => simp [popFrontM, mkMachine, hd]
theorem popFrontM_shift_none (c : Option Bool) (h : dec (heads i) = none) :
    (popFrontM i).transition (.shift c) heads = .advance .done heads (moves1 i .right) := by
  simp [popFrontM, mkMachine, h]
theorem popFrontM_done : (popFrontM i).transition .done heads = .halt true := by
  simp [popFrontM, mkMachine]
end PopT

theorem popFront_spec (i : Fin (k + 1)) (s : Fin (k + 1) → List Bool) {W : Fin (k + 1) → Set ℤ}
    (hW : ∀ t, (0 : ℤ) ∈ W t) (hWi : ∀ z : ℤ, -1 ≤ z → z ≤ (s i).length → z ∈ W i) :
    ARun (popFrontM (Γ := Γ) i) W (nf .scan s) (2 * (s i).length + 2)
        (nf .done (update s i (s i).tail)) ∧
      aanswer (popFrontM (Γ := Γ) i) (nf .done (update s i (s i).tail)) = some true := by
  have hP0 : InW W (fun _ => (0 : ℤ)) := hW
  have h1 : ARun (popFrontM (Γ := Γ) i) W ⟨.scan, regC s, fun _ => 0⟩ (s i).length
      ⟨.scan, regC s, pos1 i (s i).length⟩ := by
    have := run_scanR (M := popFrontM (Γ := Γ) i) (W := W) (q := .scan) (i := i)
      (fun x => dec x ≠ none) (fun _ h => popFrontM_scan_some i h)
      (s i).length (regC s) (fun _ => 0)
      (fun t ht => by
        have := cont_cellOf (Γ := Γ) (w := s i) (z := t) (by omega) (by omega)
        simpa using this) hP0
      (fun t ht => by simpa using hWi t (by omega) (by omega))
    simpa using this
  have h2 : astep (popFrontM (Γ := Γ) i) ⟨.scan, regC s, pos1 i (s i).length⟩ =
      some ⟨.shift none, regC s, pos1 i ((s i).length - 1)⟩ := by
    have := astep_move1 (M := popFrontM (Γ := Γ) i) (a := ⟨.scan, regC s, pos1 i (s i).length⟩)
      (popFrontM_scan_none i (by simp [bitAt_ge]))
    simpa [Move.delta, sub_eq_add_neg] using this
  obtain ⟨c', h3⟩ := run_shiftL (M := popFrontM (Γ := Γ) i) (W := W) (q := PopL.shift) (i := i)
      (fun x => dec x ≠ none) (fun c _ h => popFrontM_shift_some i c h)
      (s i).length none (regC s) (pos1 i ((s i).length - 1))
      (fun t ht => by
        have := cont_cellOf (Γ := Γ) (w := s i) (z := (s i).length - 1 - t) (by omega) (by omega)
        simpa using this)
      (inW_pos1 hW (hWi _ (by omega) (by omega)))
      (fun t ht => by simpa using hWi ((s i).length - 1 - t) (by omega) (by omega))
  have h3' : ARun (popFrontM (Γ := Γ) i) W ⟨.shift none, regC s, pos1 i ((s i).length - 1)⟩
      (s i).length ⟨.shift c', update (regC s) i (cellOf (s i).tail), pos1 i (-1)⟩ := by
    refine h3.of_eq (ACfg.ext rfl ?_ ?_)
    · simp only [update_self]
      refine congrArg (update (regC s) i) ?_
      exact cellOf_tail (s i)
    · simp only [update_self, update_idem]
      congr 1; ring
  have h4 : astep (popFrontM (Γ := Γ) i)
      ⟨.shift c', update (regC s) i (cellOf (s i).tail), pos1 i (-1)⟩ =
      some ⟨.done, update (regC s) i (cellOf (s i).tail), pos1 i 0⟩ := by
    have := astep_move1 (M := popFrontM (Γ := Γ) i)
      (a := ⟨.shift c', update (regC s) i (cellOf (s i).tail), pos1 i (-1)⟩)
      (popFrontM_shift_none i c' (by simp [bitAt_neg]))
    simpa [Move.delta] using this
  have hend : (⟨.done, update (regC s) i (cellOf (s i).tail), pos1 i 0⟩ : ACfg k Γ PopL) =
      nf .done (update s i (s i).tail) := by
    refine ACfg.ext rfl ?_ (pos1_zero i)
    show _ = regC (update s i (s i).tail)
    rw [regC_update]
  refine ⟨?_, aanswer_of_halt (popFrontM_done i)⟩
  have hrun := h1.trans (ARun.step h2 (h3'.trans (ARun.single h4
      (inW_pos1 hW (hWi _ (by omega) (by omega))) (inW_pos1 hW (hW i)))) h1.end_mem)
  have e : (s i).length + ((s i).length + 1 + 1) = 2 * (s i).length + 2 := by ring
  rw [e] at hrun
  exact hrun.of_eq hend

end QecReliability.RegMachine
