import QecReliability.Averaging
import Mathlib.Algebra.BigOperators.Field

/-! Elementary finite probability, sufficient for the projected-counter confidence bound. -/

noncomputable section

namespace QecReliability

open scoped BigOperators

def indicator {Ω : Type*} (P : Ω → Prop) (ω : Ω) : ℝ := by
  classical
  exact if P ω then 1 else 0

structure FiniteProbability (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

namespace FiniteProbability

variable {Ω : Type*} [Fintype Ω]

def expect (π : FiniteProbability Ω) (X : Ω → ℝ) : ℝ := average π.mass X
def prob (π : FiniteProbability Ω) (P : Ω → Prop) : ℝ := π.expect (indicator P)
def variance (π : FiniteProbability Ω) (X : Ω → ℝ) : ℝ :=
  π.expect (fun ω => (X ω - π.expect X) ^ 2)

theorem expect_mono (π : FiniteProbability Ω) {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) :
    π.expect X ≤ π.expect Y := average_mono π.nonneg h

@[simp] theorem expect_const (π : FiniteProbability Ω) (a : ℝ) :
    π.expect (fun _ => a) = a := average_const _ π.total a

theorem expect_add (π : FiniteProbability Ω) (X Y : Ω → ℝ) :
    π.expect (fun ω => X ω + Y ω) = π.expect X + π.expect Y := by
  simp [expect, average, mul_add, Finset.sum_add_distrib]

theorem expect_sub (π : FiniteProbability Ω) (X Y : Ω → ℝ) :
    π.expect (fun ω => X ω - Y ω) = π.expect X - π.expect Y := by
  simp [expect, average, mul_sub, Finset.sum_sub_distrib]

theorem expect_mul_const (π : FiniteProbability Ω) (X : Ω → ℝ) (a : ℝ) :
    π.expect (fun ω => X ω * a) = π.expect X * a := by
  unfold expect average
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem expect_const_mul (π : FiniteProbability Ω) (a : ℝ) (X : Ω → ℝ) :
    π.expect (fun ω => a * X ω) = a * π.expect X := by
  simpa [mul_comm] using expect_mul_const π X a

theorem expect_sum (π : FiniteProbability Ω) {I : Type*} (s : Finset I) (X : I → Ω → ℝ) :
    π.expect (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, π.expect (X i) := by
  simp only [expect, average, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem expect_nonneg (π : FiniteProbability Ω) {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) :
    0 ≤ π.expect X := by
  simpa using π.expect_mono h

theorem prob_mono (π : FiniteProbability Ω) {P Q : Ω → Prop} (h : ∀ ω, P ω → Q ω) :
    π.prob P ≤ π.prob Q := by
  classical
  apply π.expect_mono
  intro ω
  by_cases hp : P ω
  · simp [indicator, hp, h ω hp]
  · unfold indicator
    rw [if_neg hp]
    split_ifs <;> norm_num

theorem prob_nonneg (π : FiniteProbability Ω) (P : Ω → Prop) : 0 ≤ π.prob P := by
  apply π.expect_nonneg
  intro ω
  unfold indicator
  split_ifs <;> norm_num

theorem prob_complement (π : FiniteProbability Ω) (P : Ω → Prop) :
    π.prob (fun ω => ¬ P ω) = 1 - π.prob P := by
  classical
  have he : indicator (fun ω => ¬ P ω) = (fun ω => 1 - indicator P ω) := by
    funext ω
    by_cases h : P ω <;> simp [indicator, h]
  unfold prob
  rw [he, π.expect_sub, π.expect_const]

theorem prob_union_bound (π : FiniteProbability Ω) {I : Type*} (s : Finset I)
    (P : I → Ω → Prop) :
    π.prob (fun ω => ∃ i ∈ s, P i ω) ≤ ∑ i ∈ s, π.prob (P i) := by
  classical
  unfold prob
  rw [← π.expect_sum s (fun i => indicator (P i))]
  apply π.expect_mono
  intro ω
  by_cases h : ∃ i ∈ s, P i ω
  · obtain ⟨i, hi, hPi⟩ := h
    have hterm : indicator (P i) ω ≤ ∑ j ∈ s, indicator (P j) ω :=
      Finset.single_le_sum (f := fun j => indicator (P j) ω)
        (fun j _ => by dsimp [indicator]; split_ifs <;> norm_num) hi
    simpa [indicator, hPi, show ∃ i ∈ s, P i ω from ⟨i, hi, hPi⟩] using hterm
  · simp only [indicator, if_neg h]
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> norm_num

/-- Finite Chebyshev/second-moment bound, valid for any specified center. -/
theorem chebyshev_centered (π : FiniteProbability Ω) (X : Ω → ℝ) (μ t : ℝ) (ht : 0 < t) :
    π.prob (fun ω => t ≤ |X ω - μ|) ≤ π.expect (fun ω => (X ω - μ) ^ 2) / t ^ 2 := by
  have hpoint : ∀ ω, t ^ 2 * indicator (fun ω => t ≤ |X ω - μ|) ω ≤ (X ω - μ) ^ 2 := by
    intro ω
    by_cases h : t ≤ |X ω - μ|
    · simp only [indicator, if_pos h, mul_one]
      nlinarith [sq_abs (X ω - μ)]
    · simp only [indicator, if_neg h, mul_zero]
      exact sq_nonneg _
  have h := π.expect_mono hpoint
  rw [π.expect_const_mul] at h
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  change π.expect (indicator (fun ω => t ≤ |X ω - μ|)) * t ^ 2 ≤ _
  rw [mul_comm]
  exact h

theorem variance_expansion (π : FiniteProbability Ω) (X : Ω → ℝ) :
    π.variance X = π.expect (fun ω => X ω ^ 2) - (π.expect X) ^ 2 := by
  unfold variance
  have he : (fun ω => (X ω - π.expect X) ^ 2) =
      (fun ω => X ω ^ 2 - (2 * π.expect X) * X ω + (π.expect X) ^ 2) := by
    funext ω
    ring
  rw [he, π.expect_add, π.expect_sub, π.expect_const_mul, π.expect_const]
  ring

end FiniteProbability
end QecReliability
