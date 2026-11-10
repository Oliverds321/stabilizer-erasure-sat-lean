import QecReliability.FiniteProbability
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Finite product laws and exact independence of coordinate events. -/

noncomputable section
namespace QecReliability
open scoped BigOperators
namespace FiniteProbability

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

def product (π : I → FiniteProbability Ω) : FiniteProbability (I → Ω) where
  mass ω := ∏ i, (π i).mass (ω i)
  nonneg ω := Finset.prod_nonneg (fun i _ => (π i).nonneg (ω i))
  total := by
    classical
    rw [← Fintype.prod_sum]
    simp only [(π _).total, Finset.prod_const_one]

theorem product_expect_product (π : I → FiniteProbability Ω) (X : I → Ω → ℝ) :
    (product π).expect (fun ω => ∏ i, X i (ω i)) = ∏ i, (π i).expect (X i) := by
  classical
  unfold expect average product
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i ω => (π i).mass ω * X i ω)).symm

omit [Fintype Ω] [DecidableEq I] in
theorem indicator_forall (P : I → Ω → Prop) (ω : I → Ω) :
    indicator (fun ω => ∀ i, P i (ω i)) ω = ∏ i, indicator (P i) (ω i) := by
  classical
  by_cases h : ∀ i, P i (ω i)
  · simp [indicator, h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    rw [show indicator (fun ω => ∀ i, P i (ω i)) ω = 0 by simp [indicator, h]]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [indicator, hi])

theorem product_prob_forall (π : I → FiniteProbability Ω) (P : I → Ω → Prop) :
    (product π).prob (fun ω => ∀ i, P i (ω i)) = ∏ i, (π i).prob (P i) := by
  unfold prob
  have he : indicator (fun ω : I → Ω => ∀ i, P i (ω i)) = (fun ω : I → Ω => ∏ i, indicator (P i) (ω i)) := by
    funext ω
    exact indicator_forall P ω
  rw [he, product_expect_product]

@[simp] theorem prob_true (π : FiniteProbability Ω) : π.prob (fun _ => True) = 1 := by
  unfold prob indicator
  simp only [if_pos True.intro]
  exact π.expect_const _

@[simp] theorem prob_false (π : FiniteProbability Ω) : π.prob (fun _ => False) = 0 := by
  unfold prob indicator
  simp only [if_neg not_false]
  exact π.expect_const _

theorem product_prob_subset (π : I → FiniteProbability Ω) (J : Finset I)
    (P : I → Ω → Prop) :
    (product π).prob (fun ω => ∀ i ∈ J, P i (ω i)) = ∏ i ∈ J, (π i).prob (P i) := by
  classical
  rw [product_prob_forall π (fun i ω => i ∈ J → P i ω)]
  have he : (fun i => (π i).prob (fun ω => i ∈ J → P i ω)) =
      (fun i => if i ∈ J then (π i).prob (P i) else 1) := by
    funext i
    by_cases hi : i ∈ J <;> simp [hi]
  rw [he]
  simp

theorem product_prob_subset_le (π : I → FiniteProbability Ω) (J : Finset I)
    (P : I → Ω → Prop) {a : ℝ}
    (hP : ∀ i ∈ J, (π i).prob (P i) ≤ a) :
    (product π).prob (fun ω => ∀ i ∈ J, P i (ω i)) ≤ a ^ J.card := by
  rw [product_prob_subset, ← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun i _ => (π i).prob_nonneg (P i)) hP

end FiniteProbability
end QecReliability
