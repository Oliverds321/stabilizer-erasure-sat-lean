import QecReliability.SimultaneousConfidence
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! Concrete cell budget and existence/selection of a repetition budget.
The geometric error bound itself is checked; no machine bit-complexity theorem is claimed. -/

noncomputable section
namespace QecReliability

def cellBudget (ε : ℝ) : ℕ := ⌈16 / ε ^ 2⌉₊

theorem cellBudget_pos {ε : ℝ} (hε : 0 < ε) : 0 < cellBudget ε := by
  change 1 ≤ ⌈16 / ε ^ 2⌉₊
  apply Nat.one_le_ceil_iff.mpr
  exact div_pos (by norm_num) (sq_pos_of_pos hε)

theorem cellBudget_spec {ε : ℝ} (hε : 0 < ε) : 16 ≤ ε ^ 2 * (cellBudget ε : ℝ) := by
  unfold cellBudget
  have h := Nat.le_ceil (16 / ε ^ 2)
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg ε)
  have he : ε ^ 2 * (16 / ε ^ 2) = 16 := by field_simp
  rwa [he] at hh

theorem cellBudget_lt {ε : ℝ} (hε : 0 < ε) : (cellBudget ε : ℝ) < 16 / ε ^ 2 + 1 :=
  Nat.ceil_lt_add_one (le_of_lt (div_pos (by norm_num) (sq_pos_of_pos hε)))

theorem exists_repetition_budget (K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ m : ℕ, (K : ℝ) * (1 / 2 : ℝ) ^ (m + 2) ≤ δ := by
  have hkp : 0 < (K : ℝ) + 1 := by positivity
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hδ hkp)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨m, ?_⟩
  have hsmall : (1 / 2 : ℝ) ^ (m + 2) ≤ (1 / 2 : ℝ) ^ m := by
    rw [pow_add]
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) m]
  have hprod : ((K : ℝ) + 1) * (1 / 2 : ℝ) ^ m < δ := by
    have := (lt_div_iff₀ hkp).mp hm
    simpa [mul_comm] using this
  calc
    _ ≤ (K : ℝ) * (1 / 2 : ℝ) ^ m := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg K)
    _ ≤ ((K : ℝ) + 1) * (1 / 2 : ℝ) ^ m := by nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) m]
    _ ≤ δ := hprod.le

def repetitionBudget (K : ℕ) (δ : ℝ) (hδ : 0 < δ) : ℕ :=
  Nat.find (exists_repetition_budget K hδ)

theorem repetitionBudget_spec (K : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (K : ℝ) * (1 / 2 : ℝ) ^ (repetitionBudget K δ hδ + 2) ≤ δ :=
  Nat.find_spec (exists_repetition_budget K hδ)

theorem repetitionBudget_minimal (K : ℕ) (δ : ℝ) (hδ : 0 < δ) {m : ℕ}
    (hm : (K : ℝ) * (1 / 2 : ℝ) ^ (m + 2) ≤ δ) : repetitionBudget K δ hδ ≤ m :=
  Nat.find_min' (exists_repetition_budget K hδ) hm

/-- Parameter selection discharges both cell and repetition budgets. -/
theorem automatic_count_confidence {I Ω A : Type*} [Fintype I] [Fintype Ω] {q : ℕ}
    {H : HashStages Ω A q} {S : I → Finset A}
    (O : ∀ i, ExactTrialOracle H (S i)) (hM : ∀ i, (S i).card ≤ 2 ^ q)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) :
    1 - δ ≤ (repeatedLaw H.law (repetitionBudget (Fintype.card I) δ hδ)).prob
      (fun ω => ∀ i,
        |ExactTrialOracle.amplified O (cellBudget ε) (repetitionBudget (Fintype.card I) δ hδ) ω i -
          ((S i).card : ℝ)| ≤ ε * ((S i).card : ℝ)) :=
  ExactTrialOracle.simultaneous_count_confidence O _ _ (cellBudget_pos hε) hM hε hε1
    (cellBudget_spec hε) (repetitionBudget_spec _ δ hδ)

end QecReliability
