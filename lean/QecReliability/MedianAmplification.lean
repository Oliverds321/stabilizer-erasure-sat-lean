import QecReliability.ProductProbability
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Powerset

/-! Odd medians retain repeated values: sorting is a permutation of trial indices.
Amplification is proved from finite product masses, not supplied as an interface. -/

noncomputable section
namespace QecReliability
open scoped BigOperators

def oddMedian {m : ℕ} (X : Fin (2 * m + 1) → ℝ) : ℝ :=
  X (Tuple.sort X ⟨m, by omega⟩)

/-- A bad median supplies `m+1` DISTINCT trial indices, even if their values coincide. -/
theorem median_bad_subset {m : ℕ} (X : Fin (2 * m + 1) → ℝ) (M t : ℝ)
    (hbad : t < |oddMedian X - M|) :
    ∃ J : Finset (Fin (2 * m + 1)), J.card = m + 1 ∧ ∀ i ∈ J, t < |X i - M| := by
  classical
  rcases lt_abs.mp hbad with hhi | hlo
  · let f : Fin (m + 1) → Fin (2 * m + 1) := fun i => ⟨m + i.val, by omega⟩
    let e := fun i => Tuple.sort X (f i)
    have he : Function.Injective e := by
      intro i j hij
      have hh := (Tuple.sort X).injective hij
      apply Fin.ext
      have := congrArg Fin.val hh
      change m + i.val = m + j.val at this
      omega
    refine ⟨Finset.univ.image e, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ he]; simp
    · intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      have hle : oddMedian X ≤ X (e j) :=
        Tuple.monotone_sort X (show (⟨m, by omega⟩ : Fin (2 * m + 1)) ≤ f j by
          change m ≤ m + j.val; omega)
      exact lt_of_lt_of_le (by linarith) (le_abs_self (X (e j) - M))
  · let f : Fin (m + 1) → Fin (2 * m + 1) := fun i => ⟨i.val, by omega⟩
    let e := fun i => Tuple.sort X (f i)
    have he : Function.Injective e := by
      intro i j hij
      have hh := (Tuple.sort X).injective hij
      apply Fin.ext
      exact congrArg (fun a : Fin (2 * m + 1) => a.val) hh
    refine ⟨Finset.univ.image e, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ he]; simp
    · intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      have hle : X (e j) ≤ oddMedian X :=
        Tuple.monotone_sort X (show f j ≤ (⟨m, by omega⟩ : Fin (2 * m + 1)) by
          change j.val ≤ m; omega)
      exact lt_of_lt_of_le (by linarith) (neg_le_abs (X (e j) - M))

theorem amplification_power (m : ℕ) :
    (2 : ℝ) ^ (2 * m + 1) * (1 / 8 : ℝ) ^ (m + 1) = (1 / 2 : ℝ) ^ (m + 2) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have he : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
    rw [he, pow_add, pow_succ (1 / 8 : ℝ) (m + 1), pow_succ (1 / 2 : ℝ) (m + 2)]
    calc
      _ = ((2 : ℝ) ^ (2 * m + 1) * (1 / 8 : ℝ) ^ (m + 1)) * (1 / 2) := by ring
      _ = _ := by rw [ih]

/-- Independent, potentially non-identical trials with bad probability at most `1/8`. -/
theorem median_failure_bound {Ω : Type*} [Fintype Ω] (m : ℕ)
    (π : Fin (2 * m + 1) → FiniteProbability Ω)
    (X : Fin (2 * m + 1) → Ω → ℝ) (M t : ℝ)
    (htrial : ∀ i, (π i).prob (fun ω => t < |X i ω - M|) ≤ 1 / 8) :
    (FiniteProbability.product π).prob
      (fun ω => t < |oddMedian (fun i => X i (ω i)) - M|) ≤ (1 / 2 : ℝ) ^ (m + 2) := by
  classical
  let Jset := (Finset.univ : Finset (Fin (2 * m + 1))).powerset
  let P := fun (J : Finset (Fin (2 * m + 1))) (ω : Fin (2 * m + 1) → Ω) =>
    J.card = m + 1 ∧ ∀ i ∈ J, t < |X i (ω i) - M|
  have hJ : ∀ J ∈ Jset, (FiniteProbability.product π).prob (P J) ≤ (1 / 8 : ℝ) ^ (m + 1) := by
    intro J _
    by_cases hj : J.card = m + 1
    · have hp : P J = (fun ω => ∀ i ∈ J, t < |X i (ω i) - M|) := by
        funext ω; simp [P, hj]
      rw [hp, ← hj]
      exact FiniteProbability.product_prob_subset_le π J _ (fun i _ => htrial i)
    · have hp : P J = (fun _ => False) := by funext ω; simp [P, hj]
      rw [hp, FiniteProbability.prob_false]
      positivity
  calc
    _ ≤ (FiniteProbability.product π).prob (fun ω => ∃ J ∈ Jset, P J ω) := by
      apply FiniteProbability.prob_mono
      intro ω h
      obtain ⟨J, hc, hJ⟩ := median_bad_subset (fun i => X i (ω i)) M t h
      exact ⟨J, Finset.mem_powerset.mpr (Finset.subset_univ J), hc, hJ⟩
    _ ≤ ∑ J ∈ Jset, (FiniteProbability.product π).prob (P J) :=
      FiniteProbability.prob_union_bound _ Jset P
    _ ≤ ∑ _J ∈ Jset, (1 / 8 : ℝ) ^ (m + 1) := Finset.sum_le_sum hJ
    _ = (2 : ℝ) ^ (2 * m + 1) * (1 / 8 : ℝ) ^ (m + 1) := by
      simp [Jset]
    _ = _ := amplification_power m

end QecReliability
