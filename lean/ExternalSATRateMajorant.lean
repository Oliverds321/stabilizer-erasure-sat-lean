import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Source-only numerical bridge, independent of the SAT-engine closure.
`runtimeScale` is the identical expression from pinned external
SqrtLog/StatementScale.lean. No imported equality to that declaration is
claimed here. The factor-two comparison does not assume monotonicity of it.
-/
namespace QecReliability.ExternalSATBridge.RateMajorant
noncomputable section

def runtimeScale (n : ℕ) : ℝ :=
  (n : ℝ) * (Real.log (Real.log ((n : ℝ) + 16))) ^ 2 /
    Real.sqrt (Real.log ((n : ℝ) + 16))

/-- Same elementary lower bound as the external numerical module. -/
theorem two_le_log_shift (n : ℕ) : 2 ≤ Real.log ((n : ℝ) + 16) := by
  have htwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hpow := Real.log_pow (2 : ℝ) 4
  norm_num at hpow
  have hmon : Real.log 16 ≤ Real.log ((n : ℝ) + 16) :=
    Real.log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  linarith

theorem runtimeScale_le_twice {s n : ℕ} (hsn : s ≤ n) (hn : 16 ≤ n) :
    runtimeScale s ≤ 2 * runtimeScale n := by
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hn16 : (16 : ℝ) ≤ n := by simpa using (Nat.cast_le (α := ℝ)).2 hn
  have hsnR : (s : ℝ) ≤ n := (Nat.cast_le (α := ℝ)).2 hsn
  have hspos : (0 : ℝ) < s + 16 := by positivity
  have hnpos : (0 : ℝ) < n + 16 := by positivity
  let Ls := Real.log ((s : ℝ) + 16)
  let Ln := Real.log ((n : ℝ) + 16)
  have hLs : 2 ≤ Ls := two_le_log_shift s
  have hLn : 2 ≤ Ln := two_le_log_shift n
  have hLspos : 0 < Ls := by linarith
  have hLnpos : 0 < Ln := by linarith
  have hlog : Ls ≤ Ln := Real.log_le_log hspos (by linarith)
  have hjs : 0 ≤ Real.log Ls := Real.log_nonneg (by linarith)
  have hjn : 0 ≤ Real.log Ln := Real.log_nonneg (by linarith)
  have hj : Real.log Ls ≤ Real.log Ln := Real.log_le_log hLspos hlog
  have hj2 : (Real.log Ls)^2 ≤ (Real.log Ln)^2 :=
    (sq_le_sq₀ hjs hjn).2 hj
  let u := Real.sqrt Ls
  let v := Real.sqrt Ln
  have hu : 0 < u := Real.sqrt_pos.2 hLspos
  have hv : 0 < v := Real.sqrt_pos.2 hLnpos
  have husq : u^2 = Ls := Real.sq_sqrt hLspos.le
  have hvsq : v^2 = Ln := Real.sq_sqrt hLnpos.le
  have hu1 : 1 ≤ u := by
    have hh : (1 : ℝ)^2 ≤ u^2 := by nlinarith
    exact (sq_le_sq₀ (by norm_num) hu.le).1 hh
  have hcross : (s : ℝ) * v ≤ (2 * n) * u := by
    by_cases hlarge : (n : ℝ) + 16 ≤ ((s : ℝ) + 16)^2
    · have hlogs : Ln ≤ 2 * Ls := by
        have hh := Real.log_le_log hnpos hlarge
        simpa only [Real.log_pow, Nat.cast_ofNat] using hh
      have huv : v ≤ 2 * u := by
        have hh : v^2 ≤ (2*u)^2 := by nlinarith
        exact (sq_le_sq₀ hv.le (by positivity)).1 hh
      calc
        (s : ℝ) * v ≤ (n : ℝ) * v := mul_le_mul_of_nonneg_right hsnR hv.le
        _ ≤ (n : ℝ) * (2 * u) := mul_le_mul_of_nonneg_left huv (by positivity)
        _ = (2 * n) * u := by ring
    · have hss : (s : ℝ)^2 ≤ (n : ℝ) + 16 := by nlinarith
      have hLnN : Ln ≤ (n : ℝ) + 16 := by
        have hh := Real.log_le_sub_one_of_pos hnpos
        dsimp [Ln]
        linarith
      have hN : (n : ℝ) + 16 ≤ 2 * n := by linarith
      have hprod := mul_le_mul hss hLnN hLnpos.le (by positivity : (0 : ℝ) ≤ n + 16)
      have hprodN := mul_le_mul hN hN (by positivity : (0 : ℝ) ≤ n + 16)
        (by positivity : (0 : ℝ) ≤ 2 * n)
      have hsq : ((s : ℝ)*v)^2 ≤ (2*(n : ℝ))^2 := by
        rw [mul_pow, hvsq]
        nlinarith only [hprod, hprodN]
      have hsv : (s : ℝ) * v ≤ 2 * n :=
        (sq_le_sq₀ (mul_nonneg hs0 hv.le) (by positivity)).1 hsq
      exact hsv.trans (by nlinarith [mul_le_mul_of_nonneg_left hu1 (by positivity : (0 : ℝ) ≤ 2*n)])
  have hcoef : (s : ℝ) / u ≤ (2 * n) / v :=
    (div_le_div_iff₀ hu hv).2 hcross
  change (s : ℝ) * (Real.log Ls)^2 / u ≤ 2 * ((n : ℝ) * (Real.log Ln)^2 / v)
  calc
    (s : ℝ) * (Real.log Ls)^2 / u = ((s : ℝ)/u) * (Real.log Ls)^2 := by ring
    _ ≤ ((2 * n)/v) * (Real.log Ln)^2 :=
      mul_le_mul hcoef hj2 (sq_nonneg _) (by positivity)
    _ = 2 * ((n : ℝ) * (Real.log Ln)^2 / v) := by ring

end
end QecReliability.ExternalSATBridge.RateMajorant

#print axioms QecReliability.ExternalSATBridge.RateMajorant.runtimeScale_le_twice
