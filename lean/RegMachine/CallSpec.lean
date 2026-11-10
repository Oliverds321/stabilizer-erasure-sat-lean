import RegMachine.CallSim
import RegMachine.GadgetsAppend

/-!
# The oracle-call gadget: specification

`call_spec`: let `E` have a completed run `run` on the contents `w` of register `q`.
From the normal form of the registers `s` (engine registers empty, i.e. blank engine
tapes), `callM E e q` runs to the normal form of the *same* registers and halts with
`run.output`, in at most `2|w| + 3 + run.time + (kE+1)·(3·run.cells + 2)` steps; the
query tape stays in `[-1, |w|]` and every engine tape in `[-(Cb+1), Cb+1]` for any
`Cb ≥ run.cells`. Engine tapes are blank again with heads on cell 0 afterwards, so
calls can be repeated and their space does not accumulate.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.RegMachine
open QecReliability.OracleCost.MultiTape QecReliability.OracleCost.MultiTape.InjectiveTapeLift
open Turing Function RegSyms

variable {k kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]

/-- Engine tape right after `init`: only the origin marker. -/
def originOnly : ℤ → Cell ΓE := update (fun _ => .blank) 0 (.eng default true)

/-- Engine tape `0` after copying the query `w`. -/
def inputTape (E : Machine kE ΓE ΛE) (w : List Bool) : ℤ → Cell ΓE :=
  fun z => if 0 ≤ z ∧ z < w.length then gCopy E (cellOf w z) (originOnly z) else originOnly z

/-- All engine tapes after the prelude. -/
def initEng (E : Machine kE ΓE ΛE) (w : List Bool) : Fin (kE + 1) → ℤ → Cell ΓE :=
  update (fun _ => originOnly) 0 (inputTape E w)

variable {E : Machine kE ΓE ΛE} {e : Embedding kE k} {q : Fin (k + 1)}

theorem regC_eng {s : Fin (k + 1) → List Bool} (hs : ∀ j, s (e j) = []) (j : Fin (kE + 1)) :
    (regC s (e j) : ℤ → Cell ΓE) = fun _ => .blank := by
  simp [regC, hs j]

theorem assemble_const_zero : assemble e (fun _ => (0 : ℤ)) (fun _ => 0) = fun _ => 0 := by
  funext t
  by_cases ht : ∃ j, e j = t
  · obtain ⟨j, rfl⟩ := ht; simp
  · push_neg at ht; rw [assemble_outside e _ _ ht]

/-! ## Prelude: init, copy, rewind -/

theorem call_prelude (hq : ∀ j, e j ≠ q) (s : Fin (k + 1) → List Bool) (hs : ∀ j, s (e j) = [])
    {W : Fin (k + 1) → Set ℤ} (hW0 : ∀ t, (0 : ℤ) ∈ W t)
    (hWq : ∀ z : ℤ, -1 ≤ z → z ≤ (s q).length → z ∈ W q)
    (hWe0 : ∀ z : ℤ, -1 ≤ z → z ≤ (s q).length → z ∈ W (e 0)) :
    ARun (callM E e q) W (nf .init s) (2 * (s q).length + 3)
      ⟨.sim E.start, assemble e (initEng E (s q)) (regC s), fun _ => 0⟩ := by
  have hq0 : e 0 ≠ q := hq 0
  have hP0 : InW W (fun _ => (0 : ℤ)) := hW0
  obtain ⟨w, hw⟩ : ∃ w, w = s q := ⟨_, rfl⟩
  rw [← hw] at hWq hWe0 ⊢
  obtain ⟨C1, hC1⟩ : ∃ C1 : Fin (k + 1) → ℤ → Cell ΓE,
      C1 = assemble e (fun _ => originOnly) (regC s) := ⟨_, rfl⟩
  obtain ⟨C2, hC2⟩ : ∃ C2 : Fin (k + 1) → ℤ → Cell ΓE,
      C2 = assemble e (initEng E w) (regC s) := ⟨_, rfl⟩
  rw [← hC2]
  have hC1q : C1 q = cellOf w := by rw [hC1, assemble_outside e _ _ hq, hw]
  have hC1e : C1 (e 0) = originOnly := by rw [hC1, assemble_image]
  have hC2q : C2 q = cellOf w := by rw [hC2, assemble_outside e _ _ hq, hw]
  -- init
  have h1 : astep (callM E e q) (nf .init s) = some ⟨.copy, C1, fun _ => 0⟩ := by
    have := astep_eng e (M := callM E e q) (a := nf .init s) (callM_init E e q)
    rw [this]
    congr 1
    refine ACfg.ext rfl ?_ ?_
    · simp only [nf, hC1]
      congr 1
      funext j
      simp only [hs j, cellOf_nil]
      rfl
    · simp only [nf, Move.delta, add_zero]
      exact assemble_const_zero
  -- copy
  have h2 : ARun (callM E e q) W ⟨.copy, C1, fun _ => 0⟩ w.length
      ⟨.copy, C2, pos2 (e 0) w.length q w.length⟩ := by
    have := run_copyR (M := callM E e q) (W := W) (q := .copy) hq0 (fun x => dec x ≠ none)
      (gCopy E) (fun _ h => callM_copy_some E e q h) w.length C1 (fun _ => 0)
      (fun t ht => by
        simp only [hC1q, zero_add]
        exact cont_cellOf (by omega) (by omega)) hP0
      (fun t ht => by simpa using hWe0 t (by omega) (by omega))
      (fun t ht => by simpa using hWq t (by omega) (by omega))
    refine this.of_eq (ACfg.ext rfl ?_ ?_)
    · rw [hC2, initEng, ← assemble_update_eng, ← hC1]
      refine congrArg (update C1 (e 0)) (funext fun z => ?_)
      simp only [hC1q, hC1e, inputTape, zero_add, sub_zero, add_zero]
    · simp [pos2]
  -- turn
  have h3 : astep (callM E e q) ⟨.copy, C2, pos2 (e 0) w.length q w.length⟩ =
      some ⟨.rewind, C2, pos2 (e 0) (w.length - 1) q (w.length - 1)⟩ := by
    have := astep_move2 (M := callM E e q) (a := ⟨.copy, C2, pos2 (e 0) w.length q w.length⟩) hq0
      (callM_copy_none E e q (by simp [hC2q, bitAt_ge]))
    dsimp only at this
    rw [this, pos2_i hq0, pos2_j, pos2_upd_i hq0, pos2_upd_j]
    simp [Move.delta, sub_eq_add_neg]
  -- rewind
  have h4 : ARun (callM E e q) W ⟨.rewind, C2, pos2 (e 0) (w.length - 1) q (w.length - 1)⟩
      w.length ⟨.rewind, C2, pos2 (e 0) (-1) q (-1)⟩ := by
    have := run_scan2L (M := callM E e q) (W := W) (q := .rewind) hq0 (fun x => dec x ≠ none)
      (fun _ h => callM_rewind_some E e q h) w.length C2 (pos2 (e 0) (w.length - 1) q (w.length - 1))
      (fun t ht => by
        rw [hC2q, pos2_j]
        exact cont_cellOf (by omega) (by omega))
      (inW_pos2 hq0 hW0 (hWe0 _ (by omega) (by omega)) (hWq _ (by omega) (by omega)))
      (fun t ht => by rw [pos2_i hq0]; exact hWe0 _ (by omega) (by omega))
      (fun t ht => by rw [pos2_j]; exact hWq _ (by omega) (by omega))
    refine this.of_eq (ACfg.ext rfl rfl ?_)
    rw [pos2_i hq0, pos2_j, pos2_upd_i hq0, pos2_upd_j]
    have e1 : (w.length : ℤ) - 1 - (w.length : ℤ) = -1 := by omega
    rw [e1]
  -- turn into the simulation
  have h5 : astep (callM E e q) ⟨.rewind, C2, pos2 (e 0) (-1) q (-1)⟩ =
      some ⟨.sim E.start, C2, pos2 (e 0) 0 q 0⟩ := by
    have := astep_move2 (M := callM E e q) (a := ⟨.rewind, C2, pos2 (e 0) (-1) q (-1)⟩) hq0
      (callM_rewind_none E e q (by simp [hC2q, bitAt_neg]))
    dsimp only at this
    rw [this, pos2_i hq0, pos2_j, pos2_upd_i hq0, pos2_upd_j]
    simp [Move.delta]
  have hz : pos2 (e 0) 0 q 0 = fun _ => (0 : ℤ) := by
    rw [pos2_zero_j _ _ _ hq0, pos1_zero]
  rw [hz] at h5
  have hrun := ARun.step h1 (h2.trans (ARun.step h3 (h4.trans (ARun.single h5 h4.end_mem hP0))
    h2.end_mem)) hP0
  have e : w.length + (w.length + 1 + 1) + 1 = 2 * w.length + 3 := by ring
  rw [e] at hrun
  exact hrun

/-! ## The prelude result is the simulation of the engine's initial observation -/

theorem simInv_initial (w : List Bool) :
    SimInv (initialObserved E w) (initialObserved E w).visited := by
  have h0 : ∀ j, (0 : ℤ) ∈ (initialObserved E w).visited j := by
    intro j
    by_cases hj : j = 0
    · subst hj; simp [initialObserved]
    · simp [initialObserved, hj]
  refine ⟨h0, fun j z hz => ?_, fun j => ?_⟩
  · simp only [initialObserved, sub_zero] at hz ⊢
    by_cases hj : j = 0
    · subst hj
      simp only [if_true, Finset.mem_insert, Finset.mem_image, Finset.mem_range, not_or,
        not_exists, not_and] at hz
      simp only [Machine.initial, if_true, nth_mk₁]
      split_ifs with hz0
      · apply List.getI_eq_default
        simp only [List.length_map]
        by_contra hlt
        exact hz.2 z.toNat (by omega) (by omega)
      · rfl
    · simp [Machine.initial, hj]
  · rw [show (initialObserved E w).position j = 0 from rfl, Finset.insert_eq_of_mem (h0 j)]

theorem prelude_eq_simA (s : Fin (k + 1) → List Bool) :
    (⟨.sim E.start, assemble e (initEng E (s q)) (regC s), fun _ => 0⟩ :
      ACfg k (Cell ΓE) (CallL kE ΛE)) =
      simA e (initialObserved E (s q)) (initialObserved E (s q)).visited s := by
  refine ACfg.ext rfl ?_ ?_
  · simp only [simA]
    congr 1
    funext j z
    simp only [initialObserved, sub_zero, engC]
    by_cases hj : j = 0
    · subst hj
      simp only [initEng, update_self, inputTape, Machine.initial, if_true, nth_mk₁,
        Finset.mem_insert, Finset.mem_image, Finset.mem_range]
      by_cases hz : 0 ≤ z ∧ z < (s q).length
      · rw [if_pos hz, if_pos (Or.inr ⟨z.toNat, by omega, by omega⟩), if_pos hz.1]
        have hb : bitAt (s q) z = some ((s q)[z.toNat]'(by omega)) := by
          simp only [bitAt, hz.1, if_true]
          exact List.getElem?_eq_getElem _
        simp only [gCopy, dec_cellOf, hb, originOnly]
        rw [List.getI_eq_getElem _ (by simp; omega)]
        simp only [List.getElem_map]
        by_cases hz0 : z = 0
        · subst hz0; simp
        · simp [hz0]
      · rw [if_neg hz]
        by_cases hz0 : z = 0
        · subst hz0
          have hlen : (s q).length = 0 := by omega
          simp [originOnly, List.eq_nil_of_length_eq_zero hlen]
        · rw [if_neg]
          · simp [originOnly, update_of_ne hz0]
          · rintro (h | ⟨n, hn, rfl⟩)
            · exact hz0 h
            · exact hz ⟨by omega, by omega⟩
    · simp only [initEng, update_of_ne hj, Machine.initial, hj, if_false, Finset.mem_singleton,
        nth_default, originOnly]
      by_cases hz0 : z = 0
      · subst hz0; simp
      · simp [hz0]
  · simp only [simA, initialObserved]
    exact assemble_const_zero.symm

end QecReliability.RegMachine
