import QecReliability.HashMoments
import Mathlib.Data.Fintype.BigOperators

/-!
All-scale concentration on one common seed space. No independence between
scales is assumed; arbitrary seed-dependent selection is covered by a union bound.
-/

noncomputable section

namespace QecReliability

open scoped BigOperators

def zeroCell (r : ℕ) : Fin (2 ^ r) := ⟨0, pow_pos (by decide) r⟩

structure HashStages (Ω A : Type*) [Fintype Ω] (R : ℕ) where
  law : FiniteProbability Ω
  hash : (r : Fin (R + 1)) → Ω → A → Fin (2 ^ r.val)
  uniform : ∀ r a c, law.prob (fun ω => hash r ω a = c) = 1 / (2 : ℝ) ^ r.val
  pairwise : ∀ r a b, a ≠ b → ∀ c d,
    law.prob (fun ω => hash r ω a = c ∧ hash r ω b = d) = (1 / (2 : ℝ) ^ r.val) ^ 2

theorem sum_two_powers (R : ℕ) :
    (∑ r ∈ Finset.range (R + 1), (2 : ℝ) ^ r) = 2 ^ (R + 1) - 1 := by
  induction R with
  | zero => norm_num
  | succ R ih => rw [Finset.sum_range_succ, ih, pow_succ (2 : ℝ) (R + 1)]; ring

theorem dyadic_error_sum {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) (R : ℕ) :
    (∑ r : Fin (R + 1), 1 / (ε ^ 2 * (M / (2 : ℝ) ^ r.val))) ≤
      2 / (ε ^ 2 * (M / (2 : ℝ) ^ R)) := by
  have hden : 0 < ε ^ 2 * M := mul_pos (sq_pos_of_pos hε) hM
  have he : (∑ r : Fin (R + 1), 1 / (ε ^ 2 * (M / (2 : ℝ) ^ r.val))) =
      (∑ r ∈ Finset.range (R + 1), (2 : ℝ) ^ r) / (ε ^ 2 * M) := by
    rw [Finset.sum_div, ← Fin.sum_univ_eq_sum_range (fun r => (2 : ℝ) ^ r / (ε ^ 2 * M)) (R + 1)]
    apply Finset.sum_congr rfl
    intro r _
    field_simp
  rw [he, sum_two_powers]
  have hr : 0 < (2 : ℝ) ^ R := by positivity
  have hright : 2 / (ε ^ 2 * (M / (2 : ℝ) ^ R)) =
      (2 * (2 : ℝ) ^ R) / (ε ^ 2 * M) := by field_simp
  rw [hright, pow_succ]
  apply div_le_div_of_nonneg_right _ hden.le
  linarith

namespace HashStages

variable {Ω A : Type*} [Fintype Ω] {R : ℕ}

def view (H : HashStages Ω A R) (r : Fin (R + 1)) :
    PairwiseHashFamily Ω A (Fin (2 ^ r.val)) where
  law := H.law
  hash := H.hash r
  uniform := by intro a c; simpa using H.uniform r a c
  pairwise := by intro a b hab c d; simpa using H.pairwise r a b hab c d

def count (H : HashStages Ω A R) (S : Finset A) (r : Fin (R + 1)) (ω : Ω) : ℝ :=
  (H.view r).cellCount S (zeroCell r.val) ω

def mean (_H : HashStages Ω A R) (S : Finset A) (r : Fin (R + 1)) : ℝ :=
  (S.card : ℝ) / (2 : ℝ) ^ r.val

theorem view_mean (H : HashStages Ω A R) (S : Finset A) (r : Fin (R + 1)) :
    (H.view r).cellMean S = H.mean S r := by
  simp [PairwiseHashFamily.cellMean, PairwiseHashFamily.cellProbability, mean, div_eq_mul_inv]

theorem expectation (H : HashStages Ω A R) (S : Finset A) (r : Fin (R + 1)) :
    H.law.expect (H.count S r) = H.mean S r := by
  exact ((H.view r).cell_expectation S (zeroCell r.val)).trans (H.view_mean S r)

theorem variance_le (H : HashStages Ω A R) (S : Finset A) (r : Fin (R + 1)) :
    H.law.variance (H.count S r) ≤ H.mean S r := by
  have h := (H.view r).cell_variance_le_mean S (zeroCell r.val)
  rw [view_mean] at h
  exact h

theorem relative_deviation (H : HashStages Ω A R) {S : Finset A} (hS : S.Nonempty)
    (r : Fin (R + 1)) {ε : ℝ} (hε : 0 < ε) :
    H.law.prob (fun ω => ε * H.mean S r < |H.count S r ω - H.mean S r|) ≤
      1 / (ε ^ 2 * H.mean S r) := by
  letI : Nonempty (Fin (2 ^ r.val)) := ⟨zeroCell r.val⟩
  have h := (H.view r).cell_relative_deviation hS (zeroCell r.val) hε
  rw [view_mean] at h
  exact h

/-- The union covers every eligible scale on the same seed; no cross-scale independence is used. -/
theorem all_scales_relative_bound (H : HashStages Ω A R) {S : Finset A} (hS : S.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    H.law.prob (fun ω => ∃ r : Fin (R + 1),
      ε * H.mean S r < |H.count S r ω - H.mean S r|) ≤
      2 / (ε ^ 2 * H.mean S ⟨R, Nat.lt_succ_self R⟩) := by
  have hM : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  calc
    _ ≤ ∑ r : Fin (R + 1), H.law.prob
        (fun ω => ε * H.mean S r < |H.count S r ω - H.mean S r|) := by
      simpa using H.law.prob_union_bound Finset.univ
        (fun r ω => ε * H.mean S r < |H.count S r ω - H.mean S r|)
    _ ≤ ∑ r : Fin (R + 1), 1 / (ε ^ 2 * H.mean S r) :=
      Finset.sum_le_sum (fun r _ => H.relative_deviation hS r hε)
    _ ≤ 2 / (ε ^ 2 * H.mean S ⟨R, Nat.lt_succ_self R⟩) := dyadic_error_sum hM hε R

theorem rescaled_error_iff (H : HashStages Ω A R) (S : Finset A) (r : Fin (R + 1))
    (ω : Ω) (ε : ℝ) :
    ε * (S.card : ℝ) < |(2 : ℝ) ^ r.val * H.count S r ω - (S.card : ℝ)| ↔
      ε * H.mean S r < |H.count S r ω - H.mean S r| := by
  have hp : 0 < (2 : ℝ) ^ r.val := by positivity
  have hm : (2 : ℝ) ^ r.val * H.mean S r = (S.card : ℝ) := by
    unfold mean
    field_simp
  have he : (2 : ℝ) ^ r.val * H.count S r ω - (S.card : ℝ) =
      (2 : ℝ) ^ r.val * (H.count S r ω - H.mean S r) := by rw [mul_sub, hm]
  rw [he, abs_mul, abs_of_pos hp, ← hm]
  rw [mul_left_comm ε ((2 : ℝ) ^ r.val), mul_lt_mul_iff_right₀ hp]

/-- Any seed-dependent eligible stopping scale is controlled by the same simultaneous event. -/
theorem adaptive_selection_relative_bound (H : HashStages Ω A R) {S : Finset A}
    (hS : S.Nonempty) (select : Ω → Fin (R + 1)) {ε : ℝ} (hε : 0 < ε) :
    H.law.prob (fun ω => ε * (S.card : ℝ) <
      |(2 : ℝ) ^ (select ω).val * H.count S (select ω) ω - (S.card : ℝ)|) ≤
      2 / (ε ^ 2 * H.mean S ⟨R, Nat.lt_succ_self R⟩) := by
  calc
    _ ≤ H.law.prob (fun ω => ∃ r : Fin (R + 1),
        ε * H.mean S r < |H.count S r ω - H.mean S r|) :=
      H.law.prob_mono (fun ω h => ⟨select ω, (H.rescaled_error_iff S (select ω) ω ε).mp h⟩)
    _ ≤ _ := H.all_scales_relative_bound hS hε

theorem all_scales_failure_le_one_eighth (H : HashStages Ω A R) {S : Finset A}
    (hS : S.Nonempty) {ε : ℝ} (hε : 0 < ε)
    (hbudget : 16 ≤ ε ^ 2 * H.mean S ⟨R, Nat.lt_succ_self R⟩) :
    H.law.prob (fun ω => ∃ r : Fin (R + 1),
      ε * H.mean S r < |H.count S r ω - H.mean S r|) ≤ 1 / 8 := by
  apply le_trans (H.all_scales_relative_bound hS hε)
  apply (div_le_iff₀ (show 0 < ε ^ 2 * H.mean S ⟨R, Nat.lt_succ_self R⟩ by linarith)).mpr
  linarith

theorem all_scales_success_probability (H : HashStages Ω A R) {S : Finset A}
    (hS : S.Nonempty) {ε : ℝ} (hε : 0 < ε)
    (hbudget : 16 ≤ ε ^ 2 * H.mean S ⟨R, Nat.lt_succ_self R⟩) :
    7 / 8 ≤ H.law.prob (fun ω => ∀ r : Fin (R + 1),
      |H.count S r ω - H.mean S r| ≤ ε * H.mean S r) := by
  classical
  have he : (fun ω => ∀ r : Fin (R + 1), |H.count S r ω - H.mean S r| ≤ ε * H.mean S r) =
      (fun ω => ¬ ∃ r : Fin (R + 1), ε * H.mean S r < |H.count S r ω - H.mean S r|) := by
    funext ω
    simp
  rw [he, H.law.prob_complement]
  have h := H.all_scales_failure_le_one_eighth hS hε hbudget
  linarith

/-- On the simultaneous good event, the target scale is acceptable at threshold `4B`. -/
theorem target_accepts_on_good_event (H : HashStages Ω A R) {S : Finset A}
    (hS : S.Nonempty) {ε B : ℝ} (hε1 : ε ≤ 1)
    (htarget : H.mean S ⟨R, Nat.lt_succ_self R⟩ < 2 * B) (ω : Ω)
    (hgood : ∀ r : Fin (R + 1), |H.count S r ω - H.mean S r| ≤ ε * H.mean S r) :
    H.count S ⟨R, Nat.lt_succ_self R⟩ ω < 4 * B := by
  have hM : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  have hμ : 0 < H.mean S ⟨R, Nat.lt_succ_self R⟩ := div_pos hM (by positivity)
  have he := (abs_le.mp (hgood ⟨R, Nat.lt_succ_self R⟩)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hε1) hμ.le]

/--
A failed trial must either have no acceptable scale or an inaccurate acceptable
scale. This stronger event controls every possible first-acceptable stopping rule.
-/
theorem trial_failure_probability (H : HashStages Ω A R) {S : Finset A}
    (hS : S.Nonempty) {ε B : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (htarget : H.mean S ⟨R, Nat.lt_succ_self R⟩ < 2 * B)
    (hbudget : 16 ≤ ε ^ 2 * H.mean S ⟨R, Nat.lt_succ_self R⟩) :
    H.law.prob (fun ω =>
      (∀ r : Fin (R + 1), 4 * B < H.count S r ω) ∨
      ∃ r : Fin (R + 1), H.count S r ω ≤ 4 * B ∧
        ε * (S.card : ℝ) < |(2 : ℝ) ^ r.val * H.count S r ω - (S.card : ℝ)|) ≤ 1 / 8 := by
  apply le_trans (H.law.prob_mono ?_) (H.all_scales_failure_le_one_eighth hS hε hbudget)
  intro ω hfail
  rcases hfail with hnone | ⟨r, _, herr⟩
  · by_contra hnot
    push_neg at hnot
    have haccept := H.target_accepts_on_good_event hS hε1 htarget ω hnot
    have h := hnone ⟨R, Nat.lt_succ_self R⟩
    linarith
  · exact ⟨r, (H.rescaled_error_iff S r ω ε).mp herr⟩

end HashStages
end QecReliability
