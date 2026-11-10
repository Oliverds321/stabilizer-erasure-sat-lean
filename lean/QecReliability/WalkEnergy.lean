import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Finite real energy estimates for a symmetric killed walk operator.
The proof uses finite Cauchy--Schwarz and polarization, without a spectral postulate. -/
noncomputable section
namespace QecReliability.ExpanderWalk
open scoped BigOperators

abbrev RVec (m : ℕ) := Fin m → ℝ

def dot {m : ℕ} (f h : RVec m) : ℝ := ∑ i, f i * h i
def energy {m : ℕ} (f : RVec m) : ℝ := dot f f

theorem dot_comm {m : ℕ} (f h : RVec m) : dot f h = dot h f := by
  simp [dot, mul_comm]

theorem energy_nonneg {m : ℕ} (f : RVec m) : 0 ≤ energy f := by
  unfold energy dot
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (f i))

theorem dot_add_left {m : ℕ} (f h u : RVec m) :
    dot (f + h) u = dot f u + dot h u := by simp [dot, add_mul, Finset.sum_add_distrib]
theorem dot_add_right {m : ℕ} (f h u : RVec m) :
    dot f (h + u) = dot f h + dot f u := by simp [dot, mul_add, Finset.sum_add_distrib]
theorem dot_sub_left {m : ℕ} (f h u : RVec m) :
    dot (f - h) u = dot f u - dot h u := by simp [dot, sub_mul, Finset.sum_sub_distrib]
theorem dot_sub_right {m : ℕ} (f h u : RVec m) :
    dot f (h - u) = dot f h - dot f u := by simp [dot, mul_sub, Finset.sum_sub_distrib]
theorem dot_smul_left {m : ℕ} (c : ℝ) (f h : RVec m) :
    dot (c • f) h = c * dot f h := by simp [dot, mul_assoc, Finset.mul_sum]
theorem dot_smul_right {m : ℕ} (c : ℝ) (f h : RVec m) :
    dot f (c • h) = c * dot f h := by simp [dot, mul_left_comm, Finset.mul_sum]

theorem energy_add_sub {m : ℕ} (f h : RVec m) (c : ℝ) :
    energy (c • f + h) + energy (c • f - h) = 2 * c ^ 2 * energy f + 2 * energy h := by
  simp only [energy, dot_add_left, dot_add_right, dot_sub_left, dot_sub_right,
    dot_smul_left, dot_smul_right]
  ring

/-- Two-sided Rayleigh control of a symmetric linear map implies squared-norm
control. Positivity supplies the lower side; the argument is finite polarization. -/
theorem energy_bound_of_rayleigh {m : ℕ} (T : RVec m →ₗ[ℝ] RVec m)
    (hsym : ∀ f h, dot f (T h) = dot (T f) h) {β : ℝ} (hβ : 0 < β)
    (hpos : ∀ f, 0 ≤ dot f (T f))
    (hbound : ∀ f, dot f (T f) ≤ β * energy f) (f : RVec m) :
    energy (T f) ≤ β ^ 2 * energy f := by
  have hdiff : dot (β • f + T f) (T (β • f + T f)) -
      dot (β • f - T f) (T (β • f - T f)) = 4 * β * energy (T f) := by
    simp only [map_add, map_sub, map_smul, dot_add_left, dot_add_right,
      dot_sub_left, dot_sub_right, dot_smul_left, dot_smul_right]
    rw [hsym f (T f)]
    change _ = 4 * β * dot (T f) (T f)
    ring
  have hlower : -(β * energy (β • f - T f)) ≤ dot (β • f - T f) (T (β • f - T f)) :=
    (neg_nonpos.mpr (mul_nonneg hβ.le (energy_nonneg _))).trans (hpos _)
  have h := sub_le_sub (hbound (β • f + T f)) hlower
  rw [hdiff] at h
  have he := energy_add_sub f (T f) β
  have he' : β * energy (β • f + T f) - -(β * energy (β • f - T f)) =
      β * (2 * β ^ 2 * energy f + 2 * energy (T f)) := by
    rw [← he]
    ring
  rw [he'] at h
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * β by positivity)).mp
  nlinarith

def mask {m : ℕ} (A : Finset (Fin m)) : RVec m →ₗ[ℝ] RVec m where
  toFun f i := if i ∈ A then f i else 0
  map_add' f h := by ext i; by_cases hi : i ∈ A <;> simp [hi]
  map_smul' c f := by ext i; by_cases hi : i ∈ A <;> simp [hi]

theorem mask_idem {m : ℕ} (A : Finset (Fin m)) (f : RVec m) : mask A (mask A f) = mask A f := by
  ext i; by_cases hi : i ∈ A <;> simp [mask, hi]

theorem dot_mask {m : ℕ} (A : Finset (Fin m)) (f h : RVec m) :
    dot f (mask A h) = dot (mask A f) h := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ A <;> simp [mask, hi]

theorem energy_mask_le {m : ℕ} (A : Finset (Fin m)) (f : RVec m) :
    energy (mask A f) ≤ energy f := by
  unfold energy dot
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ A
  · simp [mask, hi]
  · simp only [mask, LinearMap.coe_mk, AddHom.coe_mk, if_neg hi, zero_mul]
    exact mul_self_nonneg _

theorem sum_mask_sq_le {m : ℕ} (A : Finset (Fin m)) (f : RVec m) :
    (∑ i, mask A f i) ^ 2 ≤ (A.card : ℝ) * energy (mask A f) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq A (fun _ => (1 : ℝ)) f
  simpa [mask, energy, dot, Finset.sum_ite_mem, sq, mul_comm] using h

theorem sum_sq_le {m : ℕ} (f : RVec m) :
    (∑ i, f i) ^ 2 ≤ (m : ℝ) * energy f := by
  simpa [energy, dot, sq] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin m => (1 : ℝ)) f)

end QecReliability.ExpanderWalk
