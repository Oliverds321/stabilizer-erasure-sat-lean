import QecReliability.CenteredSpectralGap

/-!




The only analytic input is the existing PortGraph.PositiveGap. The proof uses
energy_bound_of_rayleigh and symmetry, not an eigenbasis or operator norm.
-/

noncomputable section
namespace QecReliability.ExpanderWalk
open scoped BigOperators
namespace PortGraph

variable {m d : ℕ} (G : PortGraph m d)

/-- Constant mean as a finite-dimensional linear map. -/
def powerMean : RVec m →ₗ[ℝ] RVec m where
  toFun f _ := (∑ i, f i) / (m : ℝ)
  map_add' f h := by
    ext v
    simp [Finset.sum_add_distrib, add_div]
  map_smul' c f := by
    ext v
    simp [← Finset.mul_sum, mul_div_assoc]

def powerCenter : RVec m →ₗ[ℝ] RVec m := LinearMap.id - powerMean

def centeredTransition : RVec m →ₗ[ℝ] RVec m := G.transition - powerMean

include G in
theorem powerCenter_sum (f : RVec m) : ∑ i, powerCenter f i = 0 := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt G.vertices_pos)
  have hc : (m : ℝ) * ((∑ i, f i) / m) = ∑ i, f i := by field_simp
  change (∑ i : Fin m, (f i - (∑ j, f j) / (m : ℝ))) = 0
  simp only [Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hc, sub_self]

include G in
theorem powerCenter_energy (f : RVec m) : energy (powerCenter f) ≤ energy f := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt G.vertices_pos)
  let c : ℝ := (∑ i, f i) / m
  have hc : (m : ℝ) * c = ∑ i, f i := by dsimp [c]; field_simp
  have he : energy (powerCenter f) = energy f - (m : ℝ) * c ^ 2 := by
    change energy (f - (fun _ => c)) = _
    simp only [energy, dot_sub_left, dot_sub_right]
    rw [dot_comm f (fun _ => c), dot_const, dot_const]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← hc]
    ring
  rw [he]
  exact sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

theorem centeredTransition_apply (f : RVec m) :
    G.centeredTransition f = G.transition (powerCenter f) := by
  change G.transition f - powerMean f = G.transition (f - powerMean f)
  rw [map_sub]
  have hc : G.transition (powerMean f) = powerMean f := G.transition_const _
  rw [hc]

theorem powerMean_symmetric (f h : RVec m) :
    dot f (powerMean h) = dot (powerMean f) h := by
  change dot f (fun _ => (∑ i, h i) / (m : ℝ)) =
    dot (fun _ => (∑ i, f i) / (m : ℝ)) h
  rw [dot_comm f _, dot_const, dot_const]
  ring

theorem centeredTransition_symmetric (f h : RVec m) :
    dot f (G.centeredTransition h) = dot (G.centeredTransition f) h := by
  change dot f (G.transition h - powerMean h) =
    dot (G.transition f - powerMean f) h
  rw [dot_sub_right, dot_sub_left, G.transition_symmetric, powerMean_symmetric]

theorem centeredTransition_quadratic (f : RVec m) :
    dot f (G.centeredTransition f) =
      dot (powerCenter f) (G.transition (powerCenter f)) := by
  rw [G.centeredTransition_apply]
  have hz : dot (powerMean f) (G.transition (powerCenter f)) = 0 := by
    change dot (fun _ => (∑ i, f i) / (m : ℝ))
      (G.transition (powerCenter f)) = 0
    rw [dot_const, G.transition_sum, G.powerCenter_sum, mul_zero]
  change dot f (G.transition (powerCenter f)) =
    dot (f - powerMean f) (G.transition (powerCenter f))
  rw [dot_sub_left, hz, sub_zero]

/-- Centering upgrades a centered Rayleigh bound to a full-space one. -/
theorem centeredTransition_energy {ρ : ℝ} (hρ : 0 < ρ)
    (hpos : ∀ f, 0 ≤ dot f (G.transition f))
    (hupper : ∀ f : RVec m, (∑ i, f i) = 0 →
      dot f (G.transition f) ≤ ρ * energy f) (f : RVec m) :
    energy (G.centeredTransition f) ≤ ρ ^ 2 * energy f := by
  apply energy_bound_of_rayleigh G.centeredTransition
    G.centeredTransition_symmetric hρ
  · intro u
    rw [G.centeredTransition_quadratic]
    exact hpos _
  · intro u
    rw [G.centeredTransition_quadratic]
    exact (hupper _ (G.powerCenter_sum u)).trans
      (mul_le_mul_of_nonneg_left (G.powerCenter_energy u) hρ.le)

/-- The one-step squared-energy estimate on the mean-zero subspace. -/
theorem centered_energy_step {ρ : ℝ} (hρ : 0 < ρ)
    (hpos : ∀ f, 0 ≤ dot f (G.transition f))
    (hupper : ∀ f : RVec m, (∑ i, f i) = 0 →
      dot f (G.transition f) ≤ ρ * energy f)
    (f : RVec m) (hf : (∑ i, f i) = 0) :
    energy (G.transition f) ≤ ρ ^ 2 * energy f := by
  have h := G.centeredTransition_energy hρ hpos hupper f
  have hm : powerMean f = 0 := by ext v; simp [powerMean, hf]
  simpa only [centeredTransition, LinearMap.sub_apply, hm, sub_zero] using h

/-- Explicit recursion; no Function.iterate normalization is needed below. -/
def transitionPow (G : PortGraph m d) : ℕ → RVec m →ₗ[ℝ] RVec m
  | 0 => LinearMap.id
  | k + 1 => G.transition.comp (G.transitionPow k)

@[simp] theorem transitionPow_zero (f : RVec m) : G.transitionPow 0 f = f := rfl

@[simp] theorem transitionPow_succ (k : ℕ) (f : RVec m) :
    G.transitionPow (k + 1) f = G.transition (G.transitionPow k f) := rfl

theorem transitionPow_commute (k : ℕ) (f : RVec m) :
    G.transitionPow k (G.transition f) = G.transition (G.transitionPow k f) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [G.transitionPow_succ, ih]

theorem transitionPow_add (k l : ℕ) (f : RVec m) :
    G.transitionPow (k + l) f = G.transitionPow k (G.transitionPow l f) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_add, G.transitionPow_succ, ih, G.transitionPow_succ]

theorem transitionPow_symmetric (k : ℕ) (f h : RVec m) :
    dot f (G.transitionPow k h) = dot (G.transitionPow k f) h := by
  induction k generalizing f h with
  | zero => rfl
  | succ k ih =>
    rw [G.transitionPow_succ, G.transition_symmetric, ih,
      G.transitionPow_commute, G.transitionPow_succ]

theorem transitionPow_sum (k : ℕ) (f : RVec m) :
    (∑ i, G.transitionPow k f i) = ∑ i, f i := by
  induction k with
  | zero => rfl
  | succ k ih => rw [G.transitionPow_succ, G.transition_sum, ih]

theorem transitionPow_even_quadratic (k : ℕ) (f : RVec m) :
    dot f (G.transitionPow (2 * k) f) = energy (G.transitionPow k f) := by
  rw [two_mul, G.transitionPow_add, G.transitionPow_symmetric]
  rfl

theorem transitionPow_centered_energy {ρ : ℝ} (hρ : 0 < ρ)
    (hpos : ∀ f, 0 ≤ dot f (G.transition f))
    (hupper : ∀ f : RVec m, (∑ i, f i) = 0 →
      dot f (G.transition f) ≤ ρ * energy f)
    (k : ℕ) (f : RVec m) (hf : (∑ i, f i) = 0) :
    energy (G.transitionPow k f) ≤ ρ ^ (2 * k) * energy f := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hz : (∑ i, G.transitionPow k f i) = 0 := by
      rw [G.transitionPow_sum, hf]
    calc
      energy (G.transitionPow (k + 1) f)
          ≤ ρ ^ 2 * energy (G.transitionPow k f) :=
        G.centered_energy_step hρ hpos hupper _ hz
      _ ≤ ρ ^ 2 * (ρ ^ (2 * k) * energy f) :=
        mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = _ := by rw [← mul_assoc, ← pow_add]; congr 2; omega

/-- Elementary damped Bernoulli; exponents are never numerically expanded. -/
theorem damped_bernoulli {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) (k : ℕ) :
    (1 - c) ^ k * (1 + (k : ℝ) * c) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hcoef : (1 - c) * (1 + ((k + 1 : ℕ) : ℝ) * c) ≤
        1 + (k : ℝ) * c := by
      push_cast
      nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) + 1 by positivity) (sq_nonneg c)]
    calc
      (1 - c) ^ (k + 1) * (1 + ((k + 1 : ℕ) : ℝ) * c)
          = (1 - c) ^ k * ((1 - c) * (1 + ((k + 1 : ℕ) : ℝ) * c)) := by
            rw [pow_succ]; ring
      _ ≤ (1 - c) ^ k * (1 + (k : ℝ) * c) :=
        mul_le_mul_of_nonneg_left hcoef (pow_nonneg (sub_nonneg.mpr hc1) _)
      _ ≤ 1 := ih

theorem power_bound_32 : (31 / 32 : ℝ) ^ 32 ≤ 1 / 2 := by
  have h := damped_bernoulli (by norm_num : (0 : ℝ) ≤ 1 / 32)
    (by norm_num : (1 / 32 : ℝ) ≤ 1) 32
  have hc : (1 - 1 / 32 : ℝ) = 31 / 32 := by norm_num
  have hn : (1 + ((32 : ℕ) : ℝ) * (1 / 32)) = 2 := by norm_num
  rw [hc, hn] at h
  linarith

theorem power_mono_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (k : ℕ) :
    a ^ k ≤ b ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ]
    exact mul_le_mul ih hab ha (pow_nonneg (ha.trans hab) k)

theorem power_bound_384 : (31 / 32 : ℝ) ^ 384 ≤ 1 / 4096 := by
  calc
    (31 / 32 : ℝ) ^ 384 = ((31 / 32 : ℝ) ^ 32) ^ 12 := by rw [← pow_mul]
    _ ≤ (1 / 2 : ℝ) ^ 12 :=
      power_mono_nonneg (pow_nonneg (by norm_num) 32) power_bound_32 12
    _ = 1 / 4096 := by norm_num

/-- The contract supplied by the actualMGGlazy bridge is enough. -/
theorem transitionPow_384_centered (hg : G.PositiveGap (1 / 32))
    (f : RVec m) (hf : (∑ i, f i) = 0) :
    dot f (G.transitionPow 384 f) ≤ (1 / 4096 : ℝ) * energy f := by
  have hu : ∀ u : RVec m, (∑ i, u i) = 0 →
      dot u (G.transition u) ≤ (31 / 32 : ℝ) * energy u := by
    intro u hz
    have hc : (1 - 1 / 32 : ℝ) = 31 / 32 := by norm_num
    simpa only [hz, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, hc]
      using hg.rayleigh u
  calc
    dot f (G.transitionPow 384 f) = energy (G.transitionPow 192 f) :=
      G.transitionPow_even_quadratic 192 f
    _ ≤ (31 / 32 : ℝ) ^ 384 * energy f :=
      G.transitionPow_centered_energy (by norm_num) hg.positive hu 192 f hf
    _ ≤ (1 / 4096 : ℝ) * energy f :=
      mul_le_mul_of_nonneg_right power_bound_384 (energy_nonneg _)

end PortGraph
end QecReliability.ExpanderWalk
