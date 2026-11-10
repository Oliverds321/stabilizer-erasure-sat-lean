import QecReliability.BadWeightEncoder
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Sparse generator coefficients and the exact cleaning-witness semantics. -/
namespace QecReliability.SharedCircuit
open scoped BigOperators

def trimRows {n : ℕ} (rows : List (List (PauliCoord n))) : List (List (PauliCoord n)) :=
  rows.filter (fun row => !row.isEmpty)

theorem trimRows_bounds {n : ℕ} (rows : List (List (PauliCoord n))) :
    (trimRows rows).length ≤ rowIncidences rows ∧ rowIncidences (trimRows rows) = rowIncidences rows := by
  induction rows with
  | nil => simp [trimRows, rowIncidences]
  | cons row rows ih =>
    cases row with
    | nil => simpa [trimRows, rowIncidences] using ih
    | cons c cs => simp only [trimRows, List.filter_cons, List.isEmpty_cons, Bool.not_false,
        ↓reduceIte, List.length_cons, rowIncidences, List.map_cons, List.sum_cons] at *; omega

theorem rowSpace_trim {n : ℕ} (rows : List (List (PauliCoord n))) : rowSpace (trimRows rows) = rowSpace rows := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro y hy
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hy
    exact Submodule.subset_span (List.mem_map.mpr ⟨row, (List.mem_filter.mp hr).1, rfl⟩)
  · apply Submodule.span_le.mpr
    intro y hy
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hy
    cases row with
    | nil => exact Submodule.zero_mem _
    | cons c cs => exact Submodule.subset_span (List.mem_map.mpr
        ⟨c :: cs, by simp [trimRows, hr], rfl⟩)

def combination {n : ℕ} (rows : List (List (PauliCoord n))) (c : Fin rows.length → Binary.Bit) : Binary.Pauli n :=
  ∑ i, c i • decodeRow (rows.get i)

theorem combination_cons {n : ℕ} (row : List (PauliCoord n)) (rows : List (List (PauliCoord n)))
    (c : Fin (row :: rows).length → Binary.Bit) :
    combination (row :: rows) c = c ⟨0, by simp⟩ • decodeRow row + combination rows (Fin.tail c) := by
  simp [combination, Fin.sum_univ_succ, Fin.tail]

theorem mem_rowSpace_iff_combination {n : ℕ} (rows : List (List (PauliCoord n))) (s : Binary.Pauli n) :
    s ∈ rowSpace rows ↔ ∃ c, combination rows c = s := by
  have he : {x | x ∈ rows.map decodeRow} = Set.range (fun i : Fin rows.length => decodeRow (rows.get i)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hx
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hr
      exact ⟨i, congrArg decodeRow hi⟩
    · rintro ⟨i, rfl⟩
      exact List.mem_map.mpr ⟨rows.get i, List.get_mem _ _, rfl⟩
  rw [rowSpace, he, Submodule.mem_span_range_iff_exists_fun]
  rfl

theorem good_iff_generator_agreement {n : ℕ} (rows : List (List (PauliCoord n)))
    (E : Finset (Fin n)) (z : Binary.Pauli n) :
    Good (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) (Binary.supported E) z ↔
      ∃ c : Fin (trimRows rows).length → Binary.Bit, ∀ i ∈ E,
        (combination (trimRows rows) c).1 i = z.1 i ∧
        (combination (trimRows rows) c).2 i = z.2 i := by
  rw [Binary.good_iff_cleaning, Submodule.mem_sup]
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    rw [← rowSpace_trim rows, mem_rowSpace_iff_combination] at hs
    obtain ⟨c, rfl⟩ := hs
    refine ⟨c, fun i hi => ?_⟩
    have hti := ht i (by simpa using hi)
    simp [hti.1, hti.2]
  · rintro ⟨c, hc⟩
    let s := combination (trimRows rows) c
    refine ⟨s, ?_, z - s, ?_, by simp⟩
    · rw [← rowSpace_trim rows, mem_rowSpace_iff_combination]
      exact ⟨c, rfl⟩
    · intro i hi
      have he : i ∈ E := by simpa using hi
      simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply]
      exact ⟨sub_eq_zero.mpr (hc i he).1.symm, sub_eq_zero.mpr (hc i he).2.symm⟩

end QecReliability.SharedCircuit
