import SamplingBounds

/-!
# Sampling the exact rank values (`sec:sampling`, last remark), machine-checked

Draw `M` independent iid erasure patterns `E_1, ..., E_M` (each qubit erased with probability
`p`) and average the exact values `Y(E_i) = 1 - 2^{-d_{E_i}}`. With `q = U_H(p)` the
probability that a pattern is uncorrectable and `θ = I_H(p)` the infidelity:

* the patterns are all correctable with probability `(1-q)^M` (`allCorrectable_prob`);
* on that event the average is `0`, so for `θ > 0` and any tolerance `ε < 1` the average
  misses the relative tolerance with probability at least `(1-q)^M` (`failure_prob_ge`);
* hence a failure probability at most `δ < 1` with `q ≤ 1/2` forces
  `M ≥ log(1/δ)/(2q) ≥ log(1/δ)/(4θ)` (`rank_sample_size`), using `θ ≤ q ≤ 2θ`.
-/

set_option autoImplicit false
noncomputable section

namespace QecPhysical.Stabilizer.RankSampling

open scoped BigOperators
open Finset Real
open QecReliability QecReliability.Binary
open QecPhysical.BinaryPauli
open QecPhysical.Stabilizer.Uncorrectable

variable {n : ℕ}

/-- Product weight of `M` independent iid erasure patterns. -/
def patternWeight (p : ℝ) {M : ℕ} (x : Fin M → Finset (Fin n)) : ℝ :=
  ∏ i, causeMass p (x i)

theorem patternWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {M : ℕ}
    (x : Fin M → Finset (Fin n)) : 0 ≤ patternWeight p x :=
  Finset.prod_nonneg (fun i _ => causeMass_nonneg hp0 hp1 (x i))

/-- The product weights form a probability law. -/
theorem patternWeight_sum (p : ℝ) (M : ℕ) :
    ∑ x : Fin M → Finset (Fin n), patternWeight p x = 1 := by
  unfold patternWeight
  rw [← Fintype.prod_sum (fun (_ : Fin M) (E : Finset (Fin n)) => causeMass p E)]
  simp [causeMass_sum n p]

/-- Average of the exact rank values `1 - 2^{-d_E}` over the sample. -/
def rankMean (S : Submodule Bit (Pauli n)) {M : ℕ} (x : Fin M → Finset (Fin n)) : ℝ :=
  (∑ i, infidelityScore S (x i)) / M

theorem uncorrectable_eq_zero_or_one (S : Submodule Bit (Pauli n)) (E : Finset (Fin n)) :
    uncorrectable S E = 0 ∨ uncorrectable S E = 1 := by
  unfold uncorrectable
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The indicator that every sampled pattern is correctable, as a product. -/
theorem allCorrectable_indicator (S : Submodule Bit (Pauli n)) {M : ℕ}
    (x : Fin M → Finset (Fin n)) :
    (if ∀ i, uncorrectable S (x i) = 0 then (1 : ℝ) else 0) =
      ∏ i, (1 - uncorrectable S (x i)) := by
  split_ifs with h
  · symm
    apply Finset.prod_eq_one
    intro i _
    rw [h i, sub_zero]
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rcases uncorrectable_eq_zero_or_one S (x i) with h0 | h1
    · exact absurd h0 hi
    · rw [h1, sub_self]

/-- All `M` sampled patterns are correctable with probability `(1 - U_H(p))^M`. -/
theorem allCorrectable_prob (S : Submodule Bit (Pauli n)) (p : ℝ) (M : ℕ) :
    ∑ x : Fin M → Finset (Fin n),
        patternWeight p x * (if ∀ i, uncorrectable S (x i) = 0 then 1 else 0) =
      (1 - uncorrectableProb S p) ^ M := by
  have hone : ∑ E : Finset (Fin n), causeMass p E * (1 - uncorrectable S E) =
      1 - uncorrectableProb S p := by
    unfold uncorrectableProb
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [causeMass_sum n p]
  have hx : ∀ x : Fin M → Finset (Fin n),
      patternWeight p x * (if ∀ i, uncorrectable S (x i) = 0 then 1 else 0) =
        ∏ i, causeMass p (x i) * (1 - uncorrectable S (x i)) := by
    intro x
    rw [allCorrectable_indicator S x, patternWeight, ← Finset.prod_mul_distrib]
  simp_rw [hx]
  rw [← Fintype.prod_sum
    (fun (_ : Fin M) (E : Finset (Fin n)) => causeMass p E * (1 - uncorrectable S E))]
  rw [Finset.prod_const, hone]
  simp

/-- A correctable pattern has rank value `0`. -/
theorem infidelityScore_eq_zero (S : Submodule Bit (Pauli n)) {E : Finset (Fin n)}
    (h : uncorrectable S E = 0) : infidelityScore S E = 0 := by
  obtain ⟨h1, h2⟩ := infidelityScore_le_uncorrectable S E
  rw [h] at h1 h2
  linarith

/-- For `θ = I_H(p) > 0` and any tolerance `ε < 1`, the average of the rank values misses
the relative tolerance with probability at least `(1 - U_H(p))^M`. -/
theorem failure_prob_ge (S : Submodule Bit (Pauli n)) {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hθ : 0 < infidelity S p) (hε : ε < 1) (M : ℕ) :
    (1 - uncorrectableProb S p) ^ M ≤ ∑ x : Fin M → Finset (Fin n),
      patternWeight p x *
        (if ε * infidelity S p < |rankMean S x - infidelity S p| then 1 else 0) := by
  rw [← allCorrectable_prob S p M]
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (patternWeight_nonneg hp0 hp1 x)
  by_cases h : ∀ i, uncorrectable S (x i) = 0
  · have hz : rankMean S x = 0 := by
      unfold rankMean
      rw [Finset.sum_eq_zero (fun i _ => infidelityScore_eq_zero S (h i)), zero_div]
    have hfail : ε * infidelity S p < |rankMean S x - infidelity S p| := by
      rw [hz, zero_sub, abs_neg, abs_of_pos hθ]
      nlinarith
    rw [if_pos h, if_pos hfail]
  · rw [if_neg h]
    split_ifs <;> norm_num

/-- **Sample size for averaging the rank values.** If the average of `M` independent rank
values meets a relative tolerance `ε < 1` except with probability `δ < 1`, and
`U_H(p) ≤ 1/2`, then `M ≥ log(1/δ)/(2 U_H(p)) ≥ log(1/δ)/(4 I_H(p))`. -/
theorem rank_sample_size (S : Submodule Bit (Pauli n)) {p ε δ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hθ : 0 < infidelity S p) (hq : uncorrectableProb S p ≤ 1/2) (hε : ε < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (M : ℕ)
    (hfail : ∑ x : Fin M → Finset (Fin n),
      patternWeight p x *
        (if ε * infidelity S p < |rankMean S x - infidelity S p| then 1 else 0) ≤ δ) :
    log (1/δ) / (2 * uncorrectableProb S p) ≤ M ∧
      log (1/δ) / (4 * infidelity S p) ≤ log (1/δ) / (2 * uncorrectableProb S p) := by
  obtain ⟨hIU, hUI⟩ := infidelity_le_uncorrectableProb S hp0 hp1
  have hq0 : 0 < uncorrectableProb S p := lt_of_lt_of_le hθ hIU
  have hpow : (1 - uncorrectableProb S p) ^ M ≤ δ :=
    (failure_prob_ge S hp0 hp1 hθ hε M).trans hfail
  obtain ⟨h1, h2⟩ := SamplingBounds.sample_size hq0 hq hδ0 hδ1 hpow
  have hlδ : 0 ≤ log (1/δ) := by
    rw [one_div, log_inv]
    have := log_neg hδ0 hδ1
    linarith
  refine ⟨h2.trans h1, ?_⟩
  apply div_le_div_of_nonneg_left hlδ (by linarith)
  linarith

end QecPhysical.Stabilizer.RankSampling

#print axioms QecPhysical.Stabilizer.RankSampling.patternWeight_sum
#print axioms QecPhysical.Stabilizer.RankSampling.allCorrectable_prob
#print axioms QecPhysical.Stabilizer.RankSampling.failure_prob_ge
#print axioms QecPhysical.Stabilizer.RankSampling.rank_sample_size
