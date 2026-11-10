import PaperExamples

/-!
# The sampling section (`sec:sampling`), machine-checked

(a) Chernoff bound for the binomial upper tail by the exponential-moment argument:
    for `0 < p < α ≤ 1` and a natural `d ≥ α n`,
    `Σ_{j=d}^{n} C(n,j) p^j (1-p)^(n-j) ≤ exp(-n D(α‖p))`, and `D(α‖p) > 0` for `α ≠ p`.
(b) For an isotropic `S` with distance `d ≥ α n` and `0 < p < α ≤ 1`:
    `p^n/2 ≤ I_H(p) ≤ exp(-n D(α‖p))`.
(c) Sample size: the `M` independent Bernoulli(θ) samples are all zero with probability
    `(1-θ)^M`, on which event the empirical mean has relative error one; hence any
    tolerance `ε < 1` fails with probability at least `(1-θ)^M`. If `(1-θ)^M ≤ δ`
    with `θ ∈ (0,1/2]`, `δ ∈ (0,1)`, then `M ≥ log(1/δ)/(-log(1-θ)) ≥ log(1/δ)/(2θ)`.
-/

set_option autoImplicit false
noncomputable section

namespace QecPhysical.Stabilizer.SamplingBounds

open scoped BigOperators
open Finset Real
open QecReliability QecReliability.Binary
open QecPhysical.Stabilizer.Uncorrectable

/-- Binary relative entropy `D(a‖p)` (with Lean's `log 0 = 0`, so `D(1‖p) = log(1/p)`). -/
def kl (a p : ℝ) : ℝ := a * log (a / p) + (1 - a) * log ((1 - a) / (1 - p))

/-! ## (a) The Chernoff bound -/

/-- Exponential-moment bound, for every `λ ≥ 0` and natural `d ≥ α n`. -/
theorem tail_le_moment (n d : ℕ) {p α t : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht : 0 ≤ t)
    (hd : α * n ≤ d) :
    ∑ j ∈ Ico d (n + 1), (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j) ≤
      (1 - p + p * exp t) ^ n * exp (-(t * α * n)) := by
  have hq : 0 ≤ 1 - p := by linarith
  have hterm : ∀ j ∈ Ico d (n + 1), (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j) ≤
      (n.choose j : ℝ) * (p * exp t) ^ j * (1 - p) ^ (n - j) * exp (-(t * α * n)) := by
    intro j hj
    have hjd : (d : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Ico.mp hj).1
    have h1 : 1 ≤ exp (t * j) * exp (-(t * α * n)) := by
      rw [← exp_add]
      apply one_le_exp
      nlinarith
    have hnn : 0 ≤ (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j) := by positivity
    calc (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)
        ≤ (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j) *
            (exp (t * j) * exp (-(t * α * n))) := le_mul_of_one_le_right hnn h1
      _ = (n.choose j : ℝ) * (p * exp t) ^ j * (1 - p) ^ (n - j) * exp (-(t * α * n)) := by
        rw [mul_pow, ← exp_nat_mul]
        ring_nf
  have hsub : Ico d (n + 1) ⊆ range (n + 1) := by
    intro j hj
    simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢
    omega
  calc ∑ j ∈ Ico d (n + 1), (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)
      ≤ ∑ j ∈ Ico d (n + 1),
          (n.choose j : ℝ) * (p * exp t) ^ j * (1 - p) ^ (n - j) * exp (-(t * α * n)) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ j ∈ range (n + 1),
          (n.choose j : ℝ) * (p * exp t) ^ j * (1 - p) ^ (n - j) * exp (-(t * α * n)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro j _ _
        positivity
    _ = (1 - p + p * exp t) ^ n * exp (-(t * α * n)) := by
        rw [← Finset.sum_mul, add_comm (1 - p), add_pow]
        congr 1
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring

/-- **Chernoff bound** for the binomial upper tail. -/
theorem binomial_tail_chernoff (n d : ℕ) {p α : ℝ} (hp : 0 < p) (hpα : p < α) (hα1 : α ≤ 1)
    (hd : α * n ≤ d) :
    ∑ j ∈ Ico d (n + 1), (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j) ≤
      exp (-(n * kl α p)) := by
  have hp1 : p < 1 := hpα.trans_le hα1
  have hq : 0 < 1 - p := by linarith
  have hα : 0 < α := hp.trans hpα
  rcases hα1.lt_or_eq with hα1 | rfl
  · -- `e^λ = α(1-p)/(p(1-α))`
    have hr : 0 < 1 - α := by linarith
    set t := log (α * (1 - p) / (p * (1 - α))) with htdef
    have hpos : 0 < α * (1 - p) / (p * (1 - α)) := by positivity
    have hge : 1 ≤ α * (1 - p) / (p * (1 - α)) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have ht : 0 ≤ t := log_nonneg hge
    refine (tail_le_moment n d hp.le hp1.le ht hd).trans (le_of_eq ?_)
    have hexp : exp t = α * (1 - p) / (p * (1 - α)) := exp_log hpos
    have hbase : 1 - p + p * exp t = (1 - p) / (1 - α) := by
      rw [hexp]
      field_simp
      ring
    rw [hbase, ← exp_log (show 0 < (1 - p) / (1 - α) by positivity), ← exp_nat_mul, ← exp_add]
    congr 1
    simp only [kl, htdef]
    rw [log_div hq.ne' hr.ne', log_div (by positivity) (by positivity),
      log_mul hα.ne' hq.ne', log_mul hp.ne' hr.ne', log_div hα.ne' hp.ne',
      log_div hr.ne' hq.ne']
    ring
  · -- `α = 1`: only `j = n` can occur, and `D(1‖p) = log(1/p)`
    have hdn : n ≤ d := by
      have : (n : ℝ) ≤ d := by simpa using hd
      exact_mod_cast this
    have hsub : Ico d (n + 1) ⊆ {n} := by
      intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_singleton]
      omega
    calc ∑ j ∈ Ico d (n + 1), (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)
        ≤ ∑ j ∈ ({n} : Finset ℕ), (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro j _ _
          positivity
      _ = p ^ n := by simp
      _ = exp (-(n * kl 1 p)) := by
          simp only [kl, sub_self, zero_mul, add_zero, one_mul, one_div, log_inv]
          rw [neg_mul_eq_mul_neg, neg_neg, exp_nat_mul, exp_log hp]

/-- `D(α‖p) > 0` for `α ∈ [0,1]`, `p ∈ (0,1)`, `α ≠ p` (Gibbs' inequality). -/
theorem kl_pos {p α : ℝ} (hp : 0 < p) (hp1 : p < 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hne : α ≠ p) : 0 < kl α p := by
  have hq : 0 < 1 - p := by linarith
  rcases hα0.lt_or_eq with hα0 | rfl
  · rcases hα1.lt_or_eq with hα1 | rfl
    · have hr : 0 < 1 - α := by linarith
      have h1 : log (p / α) < p / α - 1 :=
        log_lt_sub_one_of_pos (by positivity) (by
          intro h
          rw [div_eq_one_iff_eq hα0.ne'] at h
          exact hne h.symm)
      have h2 : log ((1 - p) / (1 - α)) ≤ (1 - p) / (1 - α) - 1 :=
        log_le_sub_one_of_pos (by positivity)
      have e1 : log (α / p) = -log (p / α) := by
        rw [← log_inv, inv_div]
      have e2 : log ((1 - α) / (1 - p)) = -log ((1 - p) / (1 - α)) := by
        rw [← log_inv, inv_div]
      have m1 : α * (p / α - 1) = p - α := by field_simp
      have m2 : (1 - α) * ((1 - p) / (1 - α) - 1) = α - p := by field_simp; ring
      have k1 := mul_lt_mul_of_pos_left h1 hα0
      have k2 := mul_le_mul_of_nonneg_left h2 hr.le
      simp only [kl, e1, e2]
      nlinarith
    · simp only [kl, sub_self, zero_mul, add_zero, one_mul, one_div, log_inv]
      have := log_neg hp hp1
      linarith
  · simp only [kl, zero_mul, zero_add, sub_zero, one_mul, zero_div, one_div, log_inv]
    have := log_neg hq (by linarith)
    linarith

/-! ## (b) Exponential smallness of the infidelity for linear distance -/

theorem infidelity_exponential {n : ℕ} (S : Submodule Bit (Pauli n))
    (hS : S ≤ QecReliability.normalizer (symplectic n) S) {d : ℕ} (hd : IsDistance S d)
    {p α : ℝ} (hp : 0 < p) (hpα : p < α) (hα1 : α ≤ 1) (hαd : α * n ≤ d) :
    p ^ n / 2 ≤ infidelity S p ∧ infidelity S p ≤ exp (-(n * kl α p)) := by
  have hp1 : p ≤ 1 := (hpα.trans_le hα1).le
  obtain ⟨h1, h2, h3, h4⟩ := PaperExamples.tail_bound S hS hd hp.le hp1
  obtain ⟨E, hE, _⟩ := hd.2
  have hdn : d ≤ n := by
    rw [← hE]
    simpa using E.card_le_univ
  refine ⟨le_trans ?_ h1, ?_⟩
  · exact div_le_div_of_nonneg_right (pow_le_pow_of_le_one hp.le hp1 hdn) (by norm_num)
  · exact h2.trans (h3.trans ((le_of_eq h4).trans (binomial_tail_chernoff n d hp hpα hα1 hαd)))

/-! ## (c) Sample size of the empirical mean -/

/-- Product Bernoulli(θ) weight of a sample vector. -/
def sampleWeight (θ : ℝ) {M : ℕ} (x : Fin M → Bool) : ℝ :=
  ∏ i, if x i then θ else 1 - θ

/-- The product weights form a probability law. -/
theorem sampleWeight_sum (θ : ℝ) (M : ℕ) : ∑ x : Fin M → Bool, sampleWeight θ x = 1 := by
  unfold sampleWeight
  rw [← Fintype.prod_sum (fun (_ : Fin M) (b : Bool) => if b then θ else 1 - θ)]
  simp

/-- The all-zero sample has probability `(1-θ)^M`. -/
theorem allZero_prob (θ : ℝ) (M : ℕ) :
    ∑ x : Fin M → Bool, sampleWeight θ x * (if ∀ i, x i = false then 1 else 0) =
      (1 - θ) ^ M := by
  have h : ∀ x : Fin M → Bool, (∀ i, x i = false) ↔ x = fun _ => false := by
    intro x
    exact ⟨fun h => funext h, fun h i => by rw [h]⟩
  simp_rw [h, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (fun _ => false)]
  simp [sampleWeight]

/-- Empirical mean of a sample vector. -/
def empiricalMean {M : ℕ} (x : Fin M → Bool) : ℝ :=
  ((Finset.univ.filter (fun i => x i = true)).card : ℝ) / M

/-- For `θ > 0` and any tolerance `ε < 1`, the empirical mean misses the relative
tolerance with probability at least `(1-θ)^M` (the all-zero sample has relative error one). -/
theorem failure_prob_ge {θ ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hε : ε < 1) (M : ℕ) :
    (1 - θ) ^ M ≤ ∑ x : Fin M → Bool,
      sampleWeight θ x * (if ε * θ < |empiricalMean x - θ| then 1 else 0) := by
  have hnn : ∀ x : Fin M → Bool,
      0 ≤ sampleWeight θ x * (if ε * θ < |empiricalMean x - θ| then 1 else 0) := by
    intro x
    apply mul_nonneg
    · unfold sampleWeight
      apply Finset.prod_nonneg
      intro i _
      split_ifs <;> linarith
    · split_ifs <;> norm_num
  have hz : empiricalMean (fun _ : Fin M => false) = 0 := by simp [empiricalMean]
  have hfail : ε * θ < |empiricalMean (fun _ : Fin M => false) - θ| := by
    rw [hz, zero_sub, abs_neg, abs_of_pos hθ0]
    nlinarith
  have hw : sampleWeight θ (fun _ : Fin M => false) = (1 - θ) ^ M := by simp [sampleWeight]
  calc (1 - θ) ^ M
      = sampleWeight θ (fun _ : Fin M => false) *
          (if ε * θ < |empiricalMean (fun _ : Fin M => false) - θ| then 1 else 0) := by
        simp only [hfail, ↓reduceIte, mul_one, hw]
    _ ≤ _ := Finset.single_le_sum (fun x _ => hnn x) (Finset.mem_univ _)

/-- Hence a failure probability at most `δ` forces `(1-θ)^M ≤ δ`. -/
theorem pow_le_of_failure_le {θ ε δ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hε : ε < 1) (M : ℕ)
    (hδ : ∑ x : Fin M → Bool,
      sampleWeight θ x * (if ε * θ < |empiricalMean x - θ| then 1 else 0) ≤ δ) :
    (1 - θ) ^ M ≤ δ :=
  (failure_prob_ge hθ0 hθ1 hε M).trans hδ

/-- `-log(1-θ) ≤ 2θ` for `0 ≤ θ ≤ 1/2`. -/
theorem neg_log_one_sub_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1/2) : -log (1 - θ) ≤ 2 * θ := by
  have hq : 0 < 1 - θ := by linarith
  have h := log_le_sub_one_of_pos (inv_pos.mpr hq)
  rw [log_inv] at h
  have e : (1 - θ)⁻¹ - 1 = θ / (1 - θ) := by field_simp; ring
  rw [e] at h
  have : θ / (1 - θ) ≤ 2 * θ := by
    rw [div_le_iff₀ hq]
    nlinarith
  linarith

/-- **Sample-size bound.** -/
theorem sample_size {θ δ : ℝ} {M : ℕ} (hθ0 : 0 < θ) (hθ : θ ≤ 1/2)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (h : (1 - θ) ^ M ≤ δ) :
    log (1/δ) / (-log (1 - θ)) ≤ M ∧ log (1/δ) / (2 * θ) ≤ log (1/δ) / (-log (1 - θ)) := by
  have hq : 0 < 1 - θ := by linarith
  have hlq : 0 < -log (1 - θ) := by
    have := log_neg hq (by linarith)
    linarith
  have hlδ : 0 < log (1/δ) := by
    rw [one_div, log_inv]
    have := log_neg hδ0 hδ1
    linarith
  have hM : log (1/δ) ≤ M * (-log (1 - θ)) := by
    have h1 : log ((1 - θ) ^ M) ≤ log δ := log_le_log (by positivity) h
    rw [log_pow] at h1
    rw [one_div, log_inv]
    linarith
  refine ⟨(div_le_iff₀ hlq).mpr hM, ?_⟩
  exact div_le_div_of_nonneg_left hlδ.le hlq (neg_log_one_sub_le hθ0.le hθ)

end QecPhysical.Stabilizer.SamplingBounds

#print axioms QecPhysical.Stabilizer.SamplingBounds.binomial_tail_chernoff
#print axioms QecPhysical.Stabilizer.SamplingBounds.kl_pos
#print axioms QecPhysical.Stabilizer.SamplingBounds.infidelity_exponential
#print axioms QecPhysical.Stabilizer.SamplingBounds.allZero_prob
#print axioms QecPhysical.Stabilizer.SamplingBounds.failure_prob_ge
#print axioms QecPhysical.Stabilizer.SamplingBounds.sample_size
