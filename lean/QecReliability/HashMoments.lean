import QecReliability.FiniteProbability
import Mathlib.Data.Fintype.Card

/-!
An explicit finite pairwise-independent hash interface and its cell moments.
No existence, uniform construction, or circuit-size theorem is asserted.
-/

noncomputable section

namespace QecReliability

open scoped BigOperators

structure PairwiseHashFamily (Ω A C : Type*) [Fintype Ω] [Fintype C] where
  law : FiniteProbability Ω
  hash : Ω → A → C
  uniform : ∀ a c, law.prob (fun ω => hash ω a = c) = 1 / (Fintype.card C : ℝ)
  pairwise : ∀ a b, a ≠ b → ∀ c d,
    law.prob (fun ω => hash ω a = c ∧ hash ω b = d) = (1 / (Fintype.card C : ℝ)) ^ 2

namespace PairwiseHashFamily

variable {Ω A C : Type*} [Fintype Ω] [Fintype C]

def cellProbability (_H : PairwiseHashFamily Ω A C) : ℝ := 1 / (Fintype.card C : ℝ)
def cellIndicator (H : PairwiseHashFamily Ω A C) (a : A) (c : C) : Ω → ℝ :=
  indicator (fun ω => H.hash ω a = c)
def cellCount (H : PairwiseHashFamily Ω A C) (S : Finset A) (c : C) (ω : Ω) : ℝ :=
  ∑ a ∈ S, H.cellIndicator a c ω
def cellMean (H : PairwiseHashFamily Ω A C) (S : Finset A) : ℝ :=
  (S.card : ℝ) * H.cellProbability

theorem cellProbability_nonneg (H : PairwiseHashFamily Ω A C) : 0 ≤ H.cellProbability := by
  unfold cellProbability
  positivity

theorem cellMean_pos [Nonempty C] (H : PairwiseHashFamily Ω A C) {S : Finset A}
    (hS : S.Nonempty) : 0 < H.cellMean S := by
  have hc : 0 < (Fintype.card C : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  exact mul_pos hs (one_div_pos.mpr hc)

theorem expect_cellIndicator (H : PairwiseHashFamily Ω A C) (a : A) (c : C) :
    H.law.expect (H.cellIndicator a c) = H.cellProbability := H.uniform a c

theorem expect_indicator_product [DecidableEq A] (H : PairwiseHashFamily Ω A C) (a b : A) (c : C) :
    H.law.expect (fun ω => H.cellIndicator a c ω * H.cellIndicator b c ω) =
      if a = b then H.cellProbability else H.cellProbability ^ 2 := by
  classical
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    have he : (fun ω => H.cellIndicator a c ω * H.cellIndicator a c ω) = H.cellIndicator a c := by
      funext ω
      unfold cellIndicator indicator
      split_ifs <;> norm_num
    rw [he, expect_cellIndicator]
  · rw [if_neg hab]
    have he : (fun ω => H.cellIndicator a c ω * H.cellIndicator b c ω) =
        indicator (fun ω => H.hash ω a = c ∧ H.hash ω b = c) := by
      funext ω
      by_cases ha : H.hash ω a = c <;> by_cases hb : H.hash ω b = c <;>
        simp [cellIndicator, indicator, ha, hb]
    rw [he]
    exact H.pairwise a b hab c c

/-- The expectation counts distinct keys; existential-witness multiplicities never enter. -/
theorem cell_expectation (H : PairwiseHashFamily Ω A C) (S : Finset A) (c : C) :
    H.law.expect (H.cellCount S c) = H.cellMean S := by
  unfold cellCount cellMean
  rw [H.law.expect_sum]
  simp only [expect_cellIndicator, Finset.sum_const, nsmul_eq_mul]

theorem cell_second_moment (H : PairwiseHashFamily Ω A C) (S : Finset A) (c : C) :
    H.law.expect (fun ω => (H.cellCount S c ω) ^ 2) =
      (S.card : ℝ) * (H.cellProbability + ((S.card : ℝ) - 1) * H.cellProbability ^ 2) := by
  classical
  have he : (fun ω => (H.cellCount S c ω) ^ 2) =
      (fun ω => ∑ a ∈ S, ∑ b ∈ S, H.cellIndicator a c ω * H.cellIndicator b c ω) := by
    funext ω
    simp only [cellCount, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [he, H.law.expect_sum]
  simp_rw [H.law.expect_sum, expect_indicator_product]
  have hinner : ∀ a ∈ S, (∑ b ∈ S, if a = b then H.cellProbability else H.cellProbability ^ 2) =
      H.cellProbability + ((S.card : ℝ) - 1) * H.cellProbability ^ 2 := by
    intro a ha
    have hpoint : (fun b => if a = b then H.cellProbability else H.cellProbability ^ 2) =
        (fun b => H.cellProbability ^ 2 + if b = a then H.cellProbability - H.cellProbability ^ 2 else 0) := by
      funext b
      by_cases hab : a = b
      · subst b
        simp
      · simp [hab, Ne.symm hab]
    rw [hpoint, Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_ite_eq', ha, if_true]
    ring
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]

/-- Exact fixed-cell variance from only uniform marginals and pairwise independence. -/
theorem cell_variance (H : PairwiseHashFamily Ω A C) (S : Finset A) (c : C) :
    H.law.variance (H.cellCount S c) = H.cellMean S * (1 - H.cellProbability) := by
  rw [H.law.variance_expansion, cell_second_moment, cell_expectation]
  unfold cellMean
  ring

theorem cell_variance_le_mean (H : PairwiseHashFamily Ω A C) (S : Finset A) (c : C) :
    H.law.variance (H.cellCount S c) ≤ H.cellMean S := by
  rw [cell_variance]
  unfold cellMean
  nlinarith [mul_nonneg (Nat.cast_nonneg S.card) (sq_nonneg H.cellProbability)]

theorem cell_relative_deviation [Nonempty C] (H : PairwiseHashFamily Ω A C)
    {S : Finset A} (hS : S.Nonempty) (c : C) {ε : ℝ} (hε : 0 < ε) :
    H.law.prob (fun ω => ε * H.cellMean S < |H.cellCount S c ω - H.cellMean S|) ≤
      1 / (ε ^ 2 * H.cellMean S) := by
  have hμ := H.cellMean_pos hS
  have hvar := H.cell_variance_le_mean S c
  have hcheb := H.law.chebyshev_centered (H.cellCount S c) (H.cellMean S)
    (ε * H.cellMean S) (mul_pos hε hμ)
  have he : H.law.expect (fun ω => (H.cellCount S c ω - H.cellMean S) ^ 2) =
      H.law.variance (H.cellCount S c) := by rw [FiniteProbability.variance, cell_expectation]
  rw [he] at hcheb
  calc
    _ ≤ H.law.prob (fun ω => ε * H.cellMean S ≤ |H.cellCount S c ω - H.cellMean S|) :=
      H.law.prob_mono (fun _ h => h.le)
    _ ≤ H.law.variance (H.cellCount S c) / (ε * H.cellMean S) ^ 2 := hcheb
    _ ≤ H.cellMean S / (ε * H.cellMean S) ^ 2 :=
      div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ = 1 / (ε ^ 2 * H.cellMean S) := by field_simp

end PairwiseHashFamily
end QecReliability
