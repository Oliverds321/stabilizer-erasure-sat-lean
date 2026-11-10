import QecReliability.Normalization
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Positive averaging preserves simultaneous relative control of both tails. -/

namespace QecReliability

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def average (w f : ι → ℝ) : ℝ := ∑ i, w i * f i

theorem average_mono {w f g : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hfg : ∀ i, f i ≤ g i) :
    average w f ≤ average w g :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hfg i) (hw i)

theorem average_affine (w f : ι → ℝ) (hw : ∑ i, w i = 1) (a b : ℝ) :
    average w (fun i => a * f i + b) = a * average w f + b := by
  simp only [average, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem average_const (w : ι → ℝ) (hw : ∑ i, w i = 1) (a : ℝ) :
    average w (fun _ => a) = a := by
  simp [average, ← Finset.sum_mul, hw]

theorem average_range {w f : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) : 0 ≤ average w f ∧ average w f ≤ 1 := by
  constructor
  · simpa only [average_const w hs] using average_mono hw (fun i => (hf i).1)
  · simpa only [average_const w hs] using average_mono hw (fun i => (hf i).2)

theorem average_complement (w f : ι → ℝ) (hw : ∑ i, w i = 1) :
    average w (fun i => 1 - f i) = 1 - average w f := by
  simpa only [neg_one_mul, sub_eq_add_neg, add_comm] using average_affine w f hw (-1) 1

theorem relPair_average {ε : ℝ} {w f g : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (hfg : ∀ i, RelPair ε (f i) (g i)) :
    RelPair ε (average w f) (average w g) := by
  have h1 : ∀ i, (1 - ε) * f i + 0 ≤ g i := by
    intro i
    have h := (abs_le.mp (hfg i).1).1
    linarith
  have h2 : ∀ i, g i ≤ (1 + ε) * f i + 0 := by
    intro i
    have h := (abs_le.mp (hfg i).1).2
    linarith
  have h3 : ∀ i, (1 + ε) * f i + (-ε) ≤ g i := by
    intro i
    have h := (abs_le.mp (hfg i).2).1
    linarith
  have h4 : ∀ i, g i ≤ (1 - ε) * f i + ε := by
    intro i
    have h := (abs_le.mp (hfg i).2).2
    linarith
  have H1 := average_mono hw h1
  have H2 := average_mono hw h2
  have H3 := average_mono hw h3
  have H4 := average_mono hw h4
  rw [average_affine w f hs] at H1 H2 H3 H4
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

/-- A finite coupling proves comparison of two averages without identifying their sample spaces. -/
theorem average_le_of_coupling {κ : Type*} [Fintype κ]
    (w : ι → ℝ) (v : κ → ℝ) (μ : ι → κ → ℝ) (f : ι → ℝ) (g : κ → ℝ)
    (hμ : ∀ i k, 0 ≤ μ i k)
    (hrow : ∀ i, ∑ k, μ i k = w i) (hcol : ∀ k, ∑ i, μ i k = v k)
    (hfg : ∀ i k, 0 < μ i k → f i ≤ g k) : average w f ≤ average v g := by
  have hpoint : ∀ i k, μ i k * f i ≤ μ i k * g k := by
    intro i k
    by_cases h : μ i k = 0
    · simp [h]
    · exact mul_le_mul_of_nonneg_left (hfg i k (lt_of_le_of_ne (hμ i k) (Ne.symm h)))
        (hμ i k)
  calc
    average w f = ∑ i, ∑ k, μ i k * f i := by simp [average, ← Finset.sum_mul, hrow]
    _ ≤ ∑ i, ∑ k, μ i k * g k :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hpoint i k
    _ = average v g := by rw [Finset.sum_comm]; simp [average, ← Finset.sum_mul, hcol]

end QecReliability
