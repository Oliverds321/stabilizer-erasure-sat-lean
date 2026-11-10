import ExternalSATEngineLocated

/-! Additive physical interval accounting for the linked run. The shared input
is counted through a translated hull. The fresh slot allocated for the engine
input is unused and contributes one cell; no visited-space bound is inferred
from the final word's length. -/
namespace QecReliability.ExternalSATBridge.PrimitiveLink

open OAI.Algorithms.SubexponentialSAT
open Computation SqrtLogSpace
open scoped BigOperators

variable (F M : PrimitiveMachine) (out : Fin F.tapeCount)

theorem front_other_outside (j : Fin F.tapeCount) (hj : j ≠ out) :
    ∀ i, frontSlot F M j ≠ engineSlot F M out i := by
  intro i
  by_cases hi : i = M.inputTape
  · simp [engineSlot, hi, front_inj, hj]
  · simpa only [engineSlot, if_neg hi] using front_ne_fresh F M j i

theorem fresh_input_outside :
    ∀ i, freshSlot F M M.inputTape ≠ engineSlot F M out i := by
  intro i
  by_cases hi : i = M.inputTape
  · simpa only [engineSlot, if_pos hi] using (front_ne_fresh F M out M.inputTape).symm
  · simp only [engineSlot, if_neg hi, ne_eq, fresh_inj]
    exact Ne.symm hi

theorem locatedTrace_contains_origin {N : PrimitiveMachine} {bits : List Bool}
    {e : LocatedCfg N} {n : ℕ}
    (h : Trace (locatedStep N) n (locatedInit N bits) e) :
    ∀ i, e.lower i ≤ 0 ∧ 0 ≤ e.upper i := by
  intro i
  have hex := locatedTrace_expands h i
  have hu : 0 ≤ (locatedInit N bits).upper i := by
    simp only [locatedInit, Int.ofNat_eq_natCast]
    split_ifs <;> omega
  exact ⟨hex.1, hu.trans hex.2⟩

theorem engine_located_space {f : LocatedCfg F} {c : LocatedCfg (machine F M out)}
    {e : LocatedCfg M}
    (h : EngineLocatedRelated F M out (frontLocated F M out f) c e)
    (hf : ∀ i, f.lower i ≤ f.position i ∧ f.position i ≤ f.upper i)
    (he : ∀ i, e.lower i ≤ 0 ∧ 0 ≤ e.upper i) :
    visitedSpace c ≤ visitedSpace f + visitedSpace e + 1 := by
  let fw := fun j : Fin F.tapeCount => (f.upper j - f.lower j + 1).toNat
  let ew := fun i : Fin M.tapeCount => (e.upper i - e.lower i + 1).toNat
  let cw := fun j : Fin (F.tapeCount + M.tapeCount) => (c.upper j - c.lower j + 1).toNat
  have hfront : ∀ j : Fin F.tapeCount,
      cw (frontSlot F M j) ≤ fw j + (if j = out then ew M.inputTape else 0) := by
    intro j
    by_cases hj : j = out
    · subst j
      have hl := h.lower M.inputTape
      have hu := h.upper M.inputTape
      simp only [engineSlot, if_pos rfl, ↓reduceIte, frontLocated, frontInts_front] at hl hu
      have hw : cw (frontSlot F M out) ≤
          (max (f.upper out) (f.position out + e.upper M.inputTape) -
            min (f.lower out) (f.position out + e.lower M.inputTape) + 1).toNat := by
        apply Int.toNat_le_toNat
        omega
      have hh := shifted_hull_width_le_sum (hf out).1 (hf out).2
        (he M.inputTape).1 (he M.inputTape).2
      simp only [if_pos rfl, ↓reduceIte, fw, ew]
      exact hw.trans hh
    · have ho := h.outside (frontSlot F M j) (front_other_outside F M out j hj)
      simp only [frontLocated, frontInts_front] at ho
      simp only [cw, fw, if_neg hj, add_zero, ho.1, ho.2, le_refl]
  have hfresh : ∀ i : Fin M.tapeCount,
      cw (freshSlot F M i) + (if i = M.inputTape then ew M.inputTape else 0) ≤
        ew i + (if i = M.inputTape then 1 else 0) := by
    intro i
    by_cases hi : i = M.inputTape
    · subst i
      have ho := h.outside (freshSlot F M M.inputTape) (fresh_input_outside F M out)
      simp only [frontLocated, frontInts_fresh] at ho
      simp only [cw, ho.1, ho.2, if_pos rfl, ↓reduceIte]
      omega
    · have hl := h.lower i
      have hu := h.upper i
      simp only [engineSlot, if_neg hi, frontLocated, frontInts_fresh, zero_add,
        min_eq_right (he i).1, max_eq_right (he i).2] at hl hu
      simp only [if_neg hi, add_zero, cw, ew]
      apply Int.toNat_le_toNat
      omega
  have hfsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hfront j)
  have hesum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hfresh i)
  have hfsum' : (∑ j, cw (frontSlot F M j)) ≤ visitedSpace f + ew M.inputTape := by
    simpa [Finset.sum_add_distrib, fw, visitedSpace] using hfsum
  have hesum' : (∑ i, cw (freshSlot F M i)) + ew M.inputTape ≤ visitedSpace e + 1 := by
    simpa [Finset.sum_add_distrib, ew, visitedSpace] using hesum
  have hsum : visitedSpace c =
      (∑ j : Fin F.tapeCount, cw (frontSlot F M j)) +
      (∑ i : Fin M.tapeCount, cw (freshSlot F M i)) := by
    change (∑ j : Fin (F.tapeCount + M.tapeCount), cw j) = _
    rw [Fin.sum_univ_add] <;> rfl
  omega

end QecReliability.ExternalSATBridge.PrimitiveLink
