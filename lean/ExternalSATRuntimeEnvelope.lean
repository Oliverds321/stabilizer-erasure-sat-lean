import ExternalSATRateMajorant
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Range

/-! A natural-valued monotone hull of the genuine formal loglog-squared rate.
Uses the accepted local exact scale expression, not an assumption that the
raw scale is monotone. Source-only until the independent runner checks it.
No external-engine or measured-preprocessing premise is introduced.
-/
namespace QecReliability.ExternalSATBridge.RateMajorant
noncomputable section

def rateSample (A : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil ((2 : ℝ) ^ (A * runtimeScale n)) + 1

def runtimeEnvelope (A : ℝ) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sup (rateSample A)

theorem runtimeEnvelope_monotone (A : ℝ) : Monotone (runtimeEnvelope A) := by
  intro m n hmn
  apply Finset.sup_le_iff.mpr
  intro s hs
  apply Finset.le_sup
  exact Finset.mem_range.mpr
    ((Finset.mem_range.mp hs).trans_le (Nat.add_le_add_right hmn 1))

theorem rateSample_le_envelope (A : ℝ) {s n : ℕ} (hsn : s ≤ n) :
    rateSample A s ≤ runtimeEnvelope A n :=
  Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_of_le hsn))

theorem runtimeEnvelope_pos (A : ℝ) (n : ℕ) : 0 < runtimeEnvelope A n := by
  have h := rateSample_le_envelope A (s := n) le_rfl
  unfold rateSample at h
  omega

theorem runtimeEnvelope_dominates (A : ℝ) {s n : ℕ} (hsn : s ≤ n) :
    (2 : ℝ) ^ (A * runtimeScale s) ≤ (runtimeEnvelope A n : ℝ) := by
  have hround := Nat.le_ceil ((2 : ℝ) ^ (A * runtimeScale s))
  have hsamp : Nat.ceil ((2 : ℝ) ^ (A * runtimeScale s)) ≤ runtimeEnvelope A n :=
    (Nat.le_succ _).trans (rateSample_le_envelope A hsn)
  exact hround.trans ((Nat.cast_le (α := ℝ)).2 hsamp)

theorem runtimeScale_nonneg_local (n : ℕ) : 0 ≤ runtimeScale n := by
  unfold runtimeScale
  positivity

/-- Uniform factor-three bound for the finite natural ceiling hull.
The exponent constant doubles; the formal loglog-squared scale is unchanged. -/
theorem runtimeEnvelope_rate {A : ℝ} (hA : 0 ≤ A) {n : ℕ} (hn : 16 ≤ n) :
    (runtimeEnvelope A n : ℝ) ≤ 3 * (2 : ℝ) ^ (2 * A * runtimeScale n) := by
  let R : ℝ := (2 : ℝ) ^ (2 * A * runtimeScale n)
  have hR : 1 ≤ R := Real.one_le_rpow (by norm_num)
    (mul_nonneg (mul_nonneg (by norm_num) hA) (runtimeScale_nonneg_local n))
  have hmax : runtimeEnvelope A n ≤ Nat.ceil R + 1 := by
    apply Finset.sup_le_iff.mpr
    intro s hs
    have hsn : s ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
    have hscale := runtimeScale_le_twice hsn hn
    have hexp : A * runtimeScale s ≤ 2 * A * runtimeScale n := by
      have hh := mul_le_mul_of_nonneg_left hscale hA
      nlinarith only [hh]
    have hp : (2 : ℝ) ^ (A * runtimeScale s) ≤ R :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    exact Nat.add_le_add_right (Nat.ceil_mono hp) 1
  have hmaxR : (runtimeEnvelope A n : ℝ) ≤ (Nat.ceil R : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using (Nat.cast_le (α := ℝ)).2 hmax
  have hceil := Nat.ceil_lt_add_one (by linarith : 0 ≤ R)
  change (runtimeEnvelope A n : ℝ) ≤ 3 * R
  linarith

/-- A fixed explicit constant also covers all small inputs. -/
theorem runtimeEnvelope_rate_all {A : ℝ} (hA : 0 ≤ A) (n : ℕ) :
    (runtimeEnvelope A n : ℝ) ≤
      ((runtimeEnvelope A 16 : ℝ) + 3) * (2 : ℝ) ^ (2 * A * runtimeScale n) := by
  let R : ℝ := (2 : ℝ) ^ (2 * A * runtimeScale n)
  have hR : 1 ≤ R := Real.one_le_rpow (by norm_num)
    (mul_nonneg (mul_nonneg (by norm_num) hA) (runtimeScale_nonneg_local n))
  have hC : (0 : ℝ) ≤ runtimeEnvelope A 16 := Nat.cast_nonneg _
  by_cases hn : 16 ≤ n
  · have h := runtimeEnvelope_rate hA hn
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith : 0 ≤ R))
  · have hsmall : n ≤ 16 := by omega
    have h := (Nat.cast_le (α := ℝ)).2 (runtimeEnvelope_monotone A hsmall)
    have hh := mul_le_mul_of_nonneg_left hR hC
    dsimp only [R] at hh
    nlinarith

end
end QecReliability.ExternalSATBridge.RateMajorant

#print axioms QecReliability.ExternalSATBridge.RateMajorant.runtimeEnvelope_monotone
#print axioms QecReliability.ExternalSATBridge.RateMajorant.runtimeEnvelope_dominates
#print axioms QecReliability.ExternalSATBridge.RateMajorant.runtimeEnvelope_rate
#print axioms QecReliability.ExternalSATBridge.RateMajorant.runtimeEnvelope_rate_all
