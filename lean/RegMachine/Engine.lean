import RegMachine.Loops
import OracleCost.InjectiveTapeLiftCandidate
import Mathlib.Tactic.DeriveFintype

/-!
# Engine infrastructure for the oracle call

* `Cell ΓE`: the tape alphabet of machines embedding an engine `E` over `ΓE`:
  `blank`, register bits `bit b`, and engine cells `eng a origin` (`origin` marks
  absolute cell `0` of an engine tape, so cleanup can find its way home).
* `assemble e eC rC`: tape-indexed data built from engine-tape data `eC` (on the image of
  the tape embedding `e`) and register-tape data `rC` (elsewhere).
* `engWrite` / `engMove`: actions acting on all engine tapes at once; `astep_eng`.
* `IntervalObs`: in every observed run from `initialObserved`, each tape's visited set
  is an integer interval `[l, r]` with `l ≤ 0 ≤ r` containing the head.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.RegMachine
open QecReliability.OracleCost.MultiTape QecReliability.OracleCost.MultiTape.InjectiveTapeLift
open Turing Function

/-! ## The alphabet -/

/-- Cells of a register machine with an embedded engine over `ΓE`. -/
inductive Cell (ΓE : Type) where
  | blank
  | bit (b : Bool)
  | eng (a : ΓE) (origin : Bool)
  deriving DecidableEq, Fintype

namespace Cell
variable {ΓE : Type}

instance : Inhabited (Cell ΓE) := ⟨.blank⟩

@[simp] theorem default_eq : (default : Cell ΓE) = .blank := rfl

/-- Register-bit decoding. -/
def decBit : Cell ΓE → Option Bool
  | .bit b => some b
  | _ => none

instance : RegSyms (Cell ΓE) := ⟨.bit, decBit, fun _ => rfl, rfl⟩

@[simp] theorem sym_eq (b : Bool) : (RegSyms.sym b : Cell ΓE) = .bit b := rfl
@[simp] theorem dec_blank : RegSyms.dec (Cell.blank : Cell ΓE) = none := rfl
@[simp] theorem dec_bit (b : Bool) : RegSyms.dec (Cell.bit b : Cell ΓE) = some b := rfl
@[simp] theorem dec_eng (a : ΓE) (o : Bool) : RegSyms.dec (Cell.eng a o) = none := rfl

/-- The engine symbol stored in a cell (`default` for non-engine cells). -/
def val [Inhabited ΓE] : Cell ΓE → ΓE
  | .eng a _ => a
  | _ => default

/-- The origin flag of a cell. -/
def org : Cell ΓE → Bool
  | .eng _ o => o
  | _ => false

@[simp] theorem val_eng [Inhabited ΓE] (a : ΓE) (o : Bool) : val (Cell.eng a o) = a := rfl
@[simp] theorem val_blank [Inhabited ΓE] : val (Cell.blank : Cell ΓE) = default := rfl
@[simp] theorem org_eng (a : ΓE) (o : Bool) : org (Cell.eng a o) = o := rfl
@[simp] theorem org_blank : org (Cell.blank : Cell ΓE) = false := rfl

end Cell

/-! ## Assembling engine and register data -/

section Assemble
variable {k kE : ℕ} {α : Type}

/-- Tape-indexed data: engine data on the image of `e`, register data elsewhere. -/
def assemble (e : Embedding kE k) (eD : Fin (kE + 1) → α) (rD : Fin (k + 1) → α) :
    Fin (k + 1) → α :=
  fun t => match inverse e t with
    | some j => eD j
    | none => rD t

variable (e : Embedding kE k)

@[simp] theorem assemble_image (eD : Fin (kE + 1) → α) (rD : Fin (k + 1) → α) (j : Fin (kE + 1)) :
    assemble e eD rD (e j) = eD j := by
  simp [assemble]

theorem assemble_outside (eD : Fin (kE + 1) → α) (rD : Fin (k + 1) → α) {t : Fin (k + 1)}
    (ht : ∀ j, e j ≠ t) : assemble e eD rD t = rD t := by
  simp [assemble, inverse_outside e t ht]

theorem assemble_restrict (F : Fin (k + 1) → α) : assemble e (fun j => F (e j)) F = F := by
  funext t
  unfold assemble
  cases h : inverse e t with
  | none => rfl
  | some j => simp [← inverse_spec e t j h]

theorem assemble_update_eng (eD : Fin (kE + 1) → α) (rD : Fin (k + 1) → α) (j : Fin (kE + 1))
    (x : α) : update (assemble e eD rD) (e j) x = assemble e (update eD j x) rD := by
  funext t
  by_cases ht : ∃ j', e j' = t
  · obtain ⟨j', rfl⟩ := ht
    by_cases hjj : j' = j
    · subst hjj; simp
    · rw [update_of_ne (fun hh => hjj (e.injective hh)), assemble_image, assemble_image,
        update_of_ne hjj]
  · push_neg at ht
    rw [update_of_ne (fun hh => ht j hh.symm), assemble_outside e _ _ ht,
      assemble_outside e _ _ ht]

theorem assemble_update_reg (eD : Fin (kE + 1) → α) (rD : Fin (k + 1) → α) {t : Fin (k + 1)}
    (ht : ∀ j, e j ≠ t) (x : α) :
    update (assemble e eD rD) t x = assemble e eD (update rD t x) := by
  funext u
  by_cases hu : ∃ j, e j = u
  · obtain ⟨j, rfl⟩ := hu
    rw [update_of_ne (ht j), assemble_image, assemble_image]
  · push_neg at hu
    by_cases hut : u = t
    · subst hut
      rw [update_self, assemble_outside e _ _ hu, update_self]
    · rw [update_of_ne hut, assemble_outside e _ _ hu, assemble_outside e _ _ hu,
        update_of_ne hut]

theorem assemble_eq_iff (eD eD' : Fin (kE + 1) → α) (rD : Fin (k + 1) → α)
    (h : eD = eD') : assemble e eD rD = assemble e eD' rD := by rw [h]

end Assemble

/-! ## Acting on all engine tapes at once -/

section EngAct
variable {k kE : ℕ} {ΓE : Type} (e : Embedding kE k)

/-- Write `f j x` on engine tape `e j` (whose head reads `x`); register tapes rewrite their head. -/
def engWrite (heads : Fin (k + 1) → Cell ΓE) (f : Fin (kE + 1) → Cell ΓE → Cell ΓE) :
    Fin (k + 1) → Cell ΓE :=
  assemble e (fun j => f j (heads (e j))) heads

/-- Move engine tape `e j` by `mv j`; register tapes stay. -/
def engMove (mv : Fin (kE + 1) → Move) : Fin (k + 1) → Move :=
  assemble e mv (fun _ => .stay)

variable [Fintype ΓE] {Λ : Type} [Fintype Λ]

theorem astep_eng {M : Machine k (Cell ΓE) Λ} {a : ACfg k (Cell ΓE) Λ} {q : Λ}
    {f : Fin (kE + 1) → Cell ΓE → Cell ΓE} {mv : Fin (kE + 1) → Move}
    (h : M.transition a.label a.heads = .advance q (engWrite e a.heads f) (engMove e mv)) :
    astep M a = some ⟨q,
      assemble e (fun j => update (a.C (e j)) (a.P (e j)) (f j (a.C (e j) (a.P (e j))))) a.C,
      assemble e (fun j => a.P (e j) + (mv j).delta) a.P⟩ := by
  rw [astep_of_advance h]
  congr 1
  refine ACfg.ext rfl ?_ ?_
  · funext t
    by_cases ht : ∃ j, e j = t
    · obtain ⟨j, rfl⟩ := ht
      simp [engWrite]
    · push_neg at ht
      simp [engWrite, assemble_outside e _ _ ht]
  · funext t
    by_cases ht : ∃ j, e j = t
    · obtain ⟨j, rfl⟩ := ht
      simp [engMove]
    · push_neg at ht
      simp [engMove, assemble_outside e _ _ ht, Move.delta]

end EngAct

/-! ## Visited sets of engine runs are intervals around the origin -/

section Interval
variable {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]

/-- Every tape's visited set is an interval `[l, r]` with `l ≤ 0 ≤ r` holding the head. -/
def IntervalObs (o : Observed kE ΓE ΛE) : Prop :=
  ∀ j, ∃ l r : ℤ, l ≤ 0 ∧ 0 ≤ r ∧ (↑(o.visited j) : Set ℤ) = Set.Icc l r ∧
    o.position j ∈ Set.Icc l r

theorem move_delta_bounds (m : Move) : -1 ≤ m.delta ∧ m.delta ≤ 1 := by
  cases m <;> simp [Move.delta]

theorem IntervalObs.initial (E : Machine kE ΓE ΛE) (bits : List Bool) :
    IntervalObs (initialObserved E bits) := by
  intro j
  by_cases hj : j = 0
  · subst hj
    refine ⟨0, max 0 ((bits.length : ℤ) - 1), le_refl _, le_max_left _ _, ?_, ?_⟩
    · ext x
      simp only [initialObserved, if_true, Finset.coe_insert, Finset.coe_image, Finset.coe_range,
        Set.mem_insert_iff, Set.mem_image, Set.mem_Iio, Set.mem_Icc]
      constructor
      · rintro (rfl | ⟨n, hn, rfl⟩)
        · exact ⟨le_refl _, le_max_left _ _⟩
        · exact ⟨by omega, le_max_of_le_right (by omega)⟩
      · rintro ⟨h0, h1⟩
        by_cases hx : x = 0
        · exact Or.inl hx
        · right
          refine ⟨x.toNat, ?_, by omega⟩
          rcases le_max_iff.mp h1 with h | h <;> omega
    · simp [initialObserved]
  · refine ⟨0, 0, le_refl _, le_refl _, ?_, ?_⟩
    · simp [initialObserved, hj]
    · simp [initialObserved]

theorem IntervalObs.step {E : Machine kE ΓE ΛE} {o o' : Observed kE ΓE ΛE}
    (h : IntervalObs o) (hs : observedStep E o = some o') : IntervalObs o' := by
  unfold observedStep at hs
  cases ha : E.action o.core with
  | halt b => rw [ha] at hs; cases hs
  | advance l w mv =>
    rw [ha] at hs
    cases hs
    intro j
    obtain ⟨lo, hi, hlo, hhi, hV, hp⟩ := h j
    have hd := move_delta_bounds (mv j)
    have hp' := hp
    simp only [Set.mem_Icc] at hp'
    refine ⟨min lo (o.position j + (mv j).delta), max hi (o.position j + (mv j).delta),
      min_le_of_left_le hlo, le_max_of_le_left hhi, ?_, ?_⟩
    · simp only [Finset.coe_insert, hV]
      ext x
      simp only [Set.mem_insert_iff, Set.mem_Icc, min_le_iff, le_max_iff]
      omega
    · simp only [Set.mem_Icc, min_le_iff, le_max_iff]
      omega

theorem IntervalObs.trace {E : Machine kE ΓE ΛE} {o o' : Observed kE ΓE ΛE} {n : ℕ}
    (h : IntervalObs o) (ht : Trace E o n o') : IntervalObs o' := by
  induction ht with
  | nil => exact h
  | cons hs _ ih => exact ih (h.step hs)

theorem card_of_coe_Icc {V : Finset ℤ} {l r : ℤ} (h : (↑V : Set ℤ) = Set.Icc l r) :
    (V.card : ℤ) = max 0 (r + 1 - l) := by
  have hV : V = Finset.Icc l r := by
    apply Finset.coe_injective
    rw [h, Finset.coe_Icc]
  subst hV
  rw [Int.card_Icc]
  omega

end Interval

end QecReliability.RegMachine
