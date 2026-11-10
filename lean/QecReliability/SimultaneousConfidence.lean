import QecReliability.ProjectedTrial
import QecReliability.MedianAmplification

/-! Repetition and coefficient allocation. Different coefficients may share seeds;
only the repeated full seeds are independent under the explicitly constructed product law. -/

noncomputable section
namespace QecReliability
open scoped BigOperators

def repeatedLaw {Ω : Type*} [Fintype Ω] (π : FiniteProbability Ω) (m : ℕ) :
    FiniteProbability (Fin (2 * m + 1) → Ω) := FiniteProbability.product (fun _ => π)

def medianEstimate {Ω : Type*} {m : ℕ} (X : Ω → ℝ) (ω : Fin (2 * m + 1) → Ω) : ℝ :=
  oddMedian (fun i => X (ω i))

theorem simultaneous_median_failure {I Ω : Type*} [Fintype I] [Fintype Ω]
    (π : FiniteProbability Ω) (m : ℕ) (X : I → Ω → ℝ) (M t : I → ℝ)
    (htrial : ∀ i, π.prob (fun ω => t i < |X i ω - M i|) ≤ 1 / 8) :
    (repeatedLaw π m).prob (fun ω => ∃ i, t i < |medianEstimate (X i) ω - M i|) ≤
      (Fintype.card I : ℝ) * (1 / 2 : ℝ) ^ (m + 2) := by
  classical
  calc
    _ ≤ ∑ i, (repeatedLaw π m).prob
        (fun ω => t i < |medianEstimate (X i) ω - M i|) := by
      simpa using (repeatedLaw π m).prob_union_bound Finset.univ
        (fun i ω => t i < |medianEstimate (X i) ω - M i|)
    _ ≤ ∑ _i : I, (1 / 2 : ℝ) ^ (m + 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact median_failure_bound m (fun _ => π) (fun _ => X i) (M i) (t i) (fun _ => htrial i)
    _ = _ := by simp

theorem simultaneous_median_success {I Ω : Type*} [Fintype I] [Fintype Ω]
    (π : FiniteProbability Ω) (m : ℕ) (X : I → Ω → ℝ) (M t : I → ℝ) (δ : ℝ)
    (htrial : ∀ i, π.prob (fun ω => t i < |X i ω - M i|) ≤ 1 / 8)
    (hbudget : (Fintype.card I : ℝ) * (1 / 2 : ℝ) ^ (m + 2) ≤ δ) :
    1 - δ ≤ (repeatedLaw π m).prob
      (fun ω => ∀ i, |medianEstimate (X i) ω - M i| ≤ t i) := by
  have he : (fun ω : Fin (2 * m + 1) → Ω => ∀ i, |medianEstimate (X i) ω - M i| ≤ t i) =
      (fun ω : Fin (2 * m + 1) → Ω => ¬ ∃ i, t i < |medianEstimate (X i) ω - M i|) := by funext ω; simp
  rw [he, FiniteProbability.prob_complement]
  have hh := (simultaneous_median_failure π m X M t htrial).trans hbudget
  linarith

namespace ExactTrialOracle
variable {I Ω A : Type*} [Fintype I] [Fintype Ω] {q : ℕ}
    {H : HashStages Ω A q} {S : I → Finset A}

def amplified (O : ∀ i, ExactTrialOracle H (S i)) (B m : ℕ)
    (ω : Fin (2 * m + 1) → Ω) (i : I) : ℝ :=
  medianEstimate (fun seed => ((O i).trial B seed : ℝ)) ω

omit [Fintype I] in
theorem amplified_zero (O : ∀ i, ExactTrialOracle H (S i)) (B m : ℕ)
    (ω : Fin (2 * m + 1) → Ω) (i : I) (hi : S i = ∅) : amplified O B m ω i = 0 := by
  unfold amplified medianEstimate oddMedian
  apply Nat.cast_eq_zero.mpr
  exact ((O i).trial_zero_iff B _).mpr hi

omit [Fintype I] in
theorem amplified_positive (O : ∀ i, ExactTrialOracle H (S i)) (B m : ℕ)
    (ω : Fin (2 * m + 1) → Ω) (i : I) (hi : (S i).Nonempty) : 0 < amplified O B m ω i := by
  unfold amplified medianEstimate oddMedian
  apply Nat.cast_pos.mpr
  exact (O i).trial_positive B _ hi

/-- A complete confidence statement from finite hashes and exact capped-count interfaces. -/
theorem simultaneous_count_confidence (O : ∀ i, ExactTrialOracle H (S i)) (B m : ℕ)
    (hB : 0 < B) (hM : ∀ i, (S i).card ≤ 2 ^ q)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hcell : 16 ≤ ε ^ 2 * (B : ℝ))
    (hrepeat : (Fintype.card I : ℝ) * (1 / 2 : ℝ) ^ (m + 2) ≤ δ) :
    1 - δ ≤ (repeatedLaw H.law m).prob (fun ω =>
      ∀ i, |amplified O B m ω i - ((S i).card : ℝ)| ≤ ε * ((S i).card : ℝ)) := by
  exact simultaneous_median_success H.law m
    (fun i seed => ((O i).trial B seed : ℝ)) (fun i => ((S i).card : ℝ))
    (fun i => ε * ((S i).card : ℝ)) δ
    (fun i => (O i).trial_failure_le_one_eighth B hB (hM i) hε hε1 hcell) hrepeat

end ExactTrialOracle
end QecReliability
