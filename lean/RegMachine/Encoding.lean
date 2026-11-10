import Mathlib.Computability.TuringMachine.Tape
import Mathlib.Data.List.GetD

/-!
# Register encoding on tapes

An alphabet `Γ` (with blank `default`) is a *register alphabet* when it contains two
non-blank bit symbols `sym b`, decoded by `dec`. A register word `w` is laid out on
its own tape as `cellOf w`: absolute cell `z ∈ [0, |w|)` holds `sym w[z]`, every
other cell is blank. `Tape.mk₁ (w.map sym)` (head on cell `0`) has exactly this
content (`nth_mk₁_map`). Tapes are determined by their `nth` function (`tape_ext`).
-/

set_option autoImplicit false

namespace QecReliability.RegMachine
open Turing

/-- Register symbols inside a tape alphabet. -/
class RegSyms (Γ : Type) [Inhabited Γ] where
  sym : Bool → Γ
  dec : Γ → Option Bool
  dec_sym : ∀ b, dec (sym b) = some b
  dec_default : dec default = none

variable {Γ : Type} [Inhabited Γ] [RegSyms Γ]
open RegSyms

attribute [simp] RegSyms.dec_sym RegSyms.dec_default

theorem sym_injective : Function.Injective (sym : Bool → Γ) := fun a b h => by
  have h' := congrArg (dec (Γ := Γ)) h
  simpa using h'

theorem sym_ne_default (b : Bool) : (sym b : Γ) ≠ default := fun h => by
  have h' := congrArg (dec (Γ := Γ)) h
  simp at h'

/-- Encode an optional bit (`none` = blank). -/
def optSym : Option Bool → Γ
  | some b => sym b
  | none => default

@[simp] theorem dec_optSym (o : Option Bool) : dec (optSym o : Γ) = o := by
  cases o <;> simp [optSym]

@[simp] theorem optSym_none : (optSym none : Γ) = default := rfl
@[simp] theorem optSym_some (b : Bool) : (optSym (some b) : Γ) = sym b := rfl

/-- Bit of word `w` at absolute cell `z` (`none` outside `[0, |w|)`). -/
def bitAt (w : List Bool) (z : ℤ) : Option Bool := if 0 ≤ z then w[z.toNat]? else none

/-- Tape content of a register holding `w`. -/
def cellOf (w : List Bool) (z : ℤ) : Γ := optSym (bitAt w z)

@[simp] theorem dec_cellOf (w : List Bool) (z : ℤ) : dec (cellOf w z : Γ) = bitAt w z := by
  simp [cellOf]

@[simp] theorem optSym_dec_cellOf (w : List Bool) (z : ℤ) :
    (optSym (dec (cellOf w z : Γ)) : Γ) = cellOf w z := by
  simp [cellOf]

theorem bitAt_neg {w : List Bool} {z : ℤ} (hz : z < 0) : bitAt w z = none := by
  simp [bitAt, show ¬ (0 ≤ z) by omega]

theorem bitAt_ge {w : List Bool} {z : ℤ} (hz : (w.length : ℤ) ≤ z) : bitAt w z = none := by
  have h0 : 0 ≤ z := le_trans (Int.natCast_nonneg _) hz
  simp only [bitAt, h0, if_true]
  apply List.getElem?_eq_none
  omega

theorem bitAt_lt {w : List Bool} {z : ℤ} (h0 : 0 ≤ z) (hz : z < (w.length : ℤ)) :
    bitAt w z ≠ none := by
  simp only [bitAt, h0, if_true, ne_eq, List.getElem?_eq_none_iff, not_le]
  omega

@[simp] theorem bitAt_nil (z : ℤ) : bitAt [] z = none := by
  simp [bitAt]

theorem bitAt_natCast (w : List Bool) (n : ℕ) : bitAt w (n : ℤ) = w[n]? := by
  simp [bitAt]

theorem bitAt_append_lt {u v : List Bool} {z : ℤ} (hz : z < (u.length : ℤ)) :
    bitAt (u ++ v) z = bitAt u z := by
  unfold bitAt
  split_ifs with h0
  · rw [List.getElem?_append_left (by omega)]
  · rfl

theorem bitAt_append_ge {u v : List Bool} {z : ℤ} (hz : (u.length : ℤ) ≤ z) :
    bitAt (u ++ v) z = bitAt v (z - u.length) := by
  have h0 : 0 ≤ z := le_trans (Int.natCast_nonneg _) hz
  have h1 : 0 ≤ z - u.length := by omega
  simp only [bitAt, h0, h1, if_true]
  rw [List.getElem?_append_right (by omega)]
  congr 1
  omega

theorem bitAt_tail {w : List Bool} {z : ℤ} (hz : 0 ≤ z) : bitAt w.tail z = bitAt w (z + 1) := by
  have h1 : 0 ≤ z + 1 := by omega
  simp only [bitAt, hz, h1, if_true, List.getElem?_tail]
  congr 1
  omega

theorem cellOf_eq_default {w : List Bool} {z : ℤ} (h : bitAt w z = none) :
    (cellOf w z : Γ) = default := by
  simp [cellOf, h]

@[simp] theorem cellOf_nil : (cellOf [] : ℤ → Γ) = fun _ => default := by
  funext z
  simp [cellOf]

theorem cellOf_neg {w : List Bool} {z : ℤ} (hz : z < 0) : (cellOf w z : Γ) = default :=
  cellOf_eq_default (bitAt_neg hz)

theorem cellOf_ge {w : List Bool} {z : ℤ} (hz : (w.length : ℤ) ≤ z) : (cellOf w z : Γ) = default :=
  cellOf_eq_default (bitAt_ge hz)

/-! ## Tapes -/

omit [RegSyms Γ] in
/-- Tapes are determined by their `nth` contents. -/
theorem tape_ext {T₁ T₂ : Tape Γ} (h : ∀ z, T₁.nth z = T₂.nth z) : T₁ = T₂ := by
  rcases T₁ with ⟨a, L, R⟩
  rcases T₂ with ⟨a', L', R'⟩
  have h0 : a = a' := h 0
  have hR : R = R' := ListBlank.ext fun n => h ((n + 1 : ℕ) : ℤ)
  have hL : L = L' := ListBlank.ext fun n => h (Int.negSucc n)
  subst h0 hR hL
  rfl

omit [RegSyms Γ] in
theorem nth_mk₁ (l : List Γ) (z : ℤ) :
    (Tape.mk₁ l).nth z = if 0 ≤ z then l.getI z.toNat else default := by
  rcases z with n | n
  · simp only [Int.ofNat_eq_coe, Int.natCast_nonneg, if_true, Int.toNat_natCast]
    simp [Tape.mk₁, Tape.mk₂, ListBlank.nth_mk]
  · have hneg : ¬ (0 ≤ Int.negSucc n) := by omega
    simp only [hneg, if_false]
    change (ListBlank.mk ([] : List Γ)).nth n = default
    simp [ListBlank.nth_mk, List.getI]

/-- `Tape.mk₁ (w.map sym)` is the register encoding of `w` with head on cell `0`. -/
theorem nth_mk₁_map (w : List Bool) (z : ℤ) :
    (Tape.mk₁ (w.map (sym : Bool → Γ))).nth z = cellOf w z := by
  rw [nth_mk₁]
  unfold cellOf bitAt
  split_ifs with h0
  · rw [List.getI_eq_getElem?_getD, List.getElem?_map]
    cases w[z.toNat]? <;> rfl
  · rfl

omit [RegSyms Γ] in
@[simp] theorem nth_default (z : ℤ) : (default : Tape Γ).nth z = default := by
  rcases z with n | n
  · rcases n with _ | n
    · rfl
    · change (default : ListBlank Γ).nth n = default
      exact ListBlank.nth_mk [] n |>.trans (by simp [List.getI])
  · change (default : ListBlank Γ).nth n = default
    exact ListBlank.nth_mk [] n |>.trans (by simp [List.getI])

end QecReliability.RegMachine
