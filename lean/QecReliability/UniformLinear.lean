import QecReliability.FiniteProbability
import Mathlib.GroupTheory.Index

/-! Uniform finite seeds and the exact law of a surjective additive map. -/
noncomputable section
namespace QecReliability
open scoped BigOperators

def uniformLaw (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteProbability Ω where
  mass _ := 1 / (Fintype.card Ω : ℝ)
  nonneg _ := by positivity
  total := by simp [ne_of_gt (show 0 < (Fintype.card Ω : ℝ) by exact_mod_cast Fintype.card_pos)]

theorem uniformLaw_prob {Ω : Type*} [Fintype Ω] [Nonempty Ω] (P : Ω → Prop) [DecidablePred P] :
    (uniformLaw Ω).prob P = ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω := by
  classical
  simp only [FiniteProbability.prob, FiniteProbability.expect, average, uniformLaw, indicator]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

theorem uniformLaw_addHom {G K : Type*} [AddGroup G] [AddGroup K]
    [Fintype G] [Fintype K] (f : G →+ K) (hf : Function.Surjective f) (y : K) :
    (uniformLaw G).prob (fun x => f x = y) = 1 / (Fintype.card K : ℝ) := by
  classical
  have he : ∀ z : K, (Finset.univ.filter (fun x => f x = z)).card =
      (Finset.univ.filter (fun x => f x = y)).card := by
    intro z
    exact AddMonoidHom.card_fiber_eq_of_mem_range f (hf z) (hf y)
  have hc : Fintype.card G = Fintype.card K * (Finset.univ.filter (fun x => f x = y)).card := by
    calc
      _ = ∑ z : K, (Finset.univ.filter (fun x => f x = z)).card :=
        Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
      _ = _ := by simp_rw [he]; simp
  have hp : 0 < ((Finset.univ.filter (fun x => f x = y)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (by obtain ⟨x, hx⟩ := hf y; exact ⟨x, by simp [hx]⟩)
  rw [uniformLaw_prob, hc, Nat.cast_mul]
  field_simp

end QecReliability
