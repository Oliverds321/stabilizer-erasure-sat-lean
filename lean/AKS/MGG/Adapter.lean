/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
Adapter for the backported girving/aks MGG Rayleigh theorem.
The concrete graph retains port multiplicity, loops, and the factor-2 shears.
-/
import AKS.MGG.Rayleigh

open BigOperators Real

namespace QuantumExpander

/-- Remove the unit-norm premise by normalization. Only `3 ≤ s` and mean zero
are assumed; no spectral fact about the graph is an input. -/
theorem mgg_rayleigh_all (s : ℕ) (hs : 3 ≤ s)
    (f : EuclideanSpace ℝ (Fin (s * s)))
    (hzero : ∑ v, f v = 0) :
    |@inner ℝ _ _ f ((mgg s).walkCLM f)| ≤ (5 * √2 / 8) * ‖f‖ ^ 2 := by
  by_cases hf : f = 0
  · simp [hf]
  have hpos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hmean : meanCLM (s * s) f = 0 := by
    ext v
    simp [meanCLM_apply, hzero]
  let g := (1 / ‖f‖) • f
  have hg_norm : ‖g‖ = 1 := by
    rw [show g = (1 / ‖f‖) • f from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg zero_le_one hpos.le), div_mul_cancel₀ 1 hpos.ne']
  have hg_mean : meanCLM (s * s) g = 0 := by
    simp [g, map_smul, hmean]
  have hg_orth : @inner ℝ _ _ g (meanCLM (s * s) g) = 0 := by
    rw [hg_mean, inner_zero_right]
  have hunit := mgg_rayleigh_bound s hs g hg_orth hg_norm
  have hscale : f = ‖f‖ • g := by
    simp [g, smul_smul, hpos.ne']
  have hin : @inner ℝ _ _ f ((mgg s).walkCLM f) =
      ‖f‖ ^ 2 * @inner ℝ _ _ g ((mgg s).walkCLM g) := by
    conv_lhs => rw [hscale]
    rw [map_smul, inner_smul_left, inner_smul_right]
    simp only [conj_trivial, sq]
    ring
  rw [hin, abs_mul, abs_of_nonneg (sq_nonneg _)]
  nlinarith [mul_le_mul_of_nonneg_left hunit (sq_nonneg ‖f‖)]

/-- The convenient rational upper bound used by the lazy-graph bridge. -/
theorem mgg_constant_le : (5 * √2 / 8 : ℝ) ≤ 15 / 16 := by
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hnonneg := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

/-- Plain-function form, retaining the sharp upstream constant and absolute value. -/
theorem mgg_abs_rayleigh (s : ℕ) (hs : 3 ≤ s)
    (f : Fin (s * s) → ℝ) (hzero : ∑ v, f v = 0) :
    |∑ v, f v * ((∑ i : Fin 8, f ((mgg s).neighbor v i)) / 8)| ≤
      (5 * √2 / 8 : ℝ) * ∑ v, (f v) ^ 2 := by
  let x : EuclideanSpace ℝ (Fin (s * s)) := WithLp.toLp 2 f
  have h := mgg_rayleigh_all s hs x hzero
  have hnorm : ‖x‖ ^ 2 = ∑ v, (f v) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [x, Real.norm_eq_abs, sq_abs]
  have hin : @inner ℝ _ _ x ((mgg s).walkCLM x) =
      ∑ v, f v * ((∑ i : Fin 8, f ((mgg s).neighbor v i)) / 8) := by
    rw [PiLp.inner_apply]
    simp [RegularGraph.walkCLM_apply, x, mul_comm]
  rw [hnorm, hin] at h
  exact h

/-- The rational upper Rayleigh bound needed by the existing lazy-graph bridge. -/
theorem mgg_upper_rayleigh (s : ℕ) (hs : 3 ≤ s)
    (f : Fin (s * s) → ℝ) (hzero : ∑ v, f v = 0) :
    (∑ v, f v * ((∑ i : Fin 8, f ((mgg s).neighbor v i)) / 8)) ≤
      (15 / 16 : ℝ) * ∑ v, (f v) ^ 2 := by
  have h := mgg_abs_rayleigh s hs f hzero
  exact (le_abs_self _).trans (h.trans
    (mul_le_mul_of_nonneg_right mgg_constant_le
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)))

end QuantumExpander
