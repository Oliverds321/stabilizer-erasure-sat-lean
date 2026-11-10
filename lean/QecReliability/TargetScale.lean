import QecReliability.BitModelsCore
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Deterministic target-scale selection, with the small-count case separated. -/

namespace QecReliability

def eligibleScales (q M B : ℕ) : Finset ℕ :=
  (Finset.range (q + 1)).filter (fun r => B * 2 ^ r ≤ M)

theorem eligibleScales_nonempty {q M B : ℕ} (hBM : B ≤ M) :
    (eligibleScales q M B).Nonempty := by
  refine ⟨0, ?_⟩
  simp [eligibleScales, hBM]

def targetScale (q M B : ℕ) (hBM : B ≤ M) : ℕ :=
  (eligibleScales q M B).max' (eligibleScales_nonempty hBM)

theorem targetScale_spec {q M B : ℕ} (hBM : B ≤ M) (hB : 0 < B) (hM : M ≤ 2 ^ q) :
    targetScale q M B hBM ≤ q ∧
      B * 2 ^ targetScale q M B hBM ≤ M ∧
      M < 2 * B * 2 ^ targetScale q M B hBM := by
  have hmem := Finset.max'_mem (eligibleScales q M B) (eligibleScales_nonempty hBM)
  have hspec : targetScale q M B hBM < q + 1 ∧
      B * 2 ^ targetScale q M B hBM ≤ M := by
    simpa only [eligibleScales, Finset.mem_filter, Finset.mem_range, targetScale] using hmem
  refine ⟨by omega, hspec.2, ?_⟩
  by_contra hnot
  have hnext : B * 2 ^ (targetScale q M B hBM + 1) ≤ M := by
    rw [pow_succ]
    nlinarith
  by_cases hr : targetScale q M B hBM < q
  · have hmemnext : targetScale q M B hBM + 1 ∈ eligibleScales q M B := by
      simp only [eligibleScales, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hnext⟩
    have hmax := Finset.le_max' (eligibleScales q M B) _ hmemnext
    change targetScale q M B hBM + 1 ≤ targetScale q M B hBM at hmax
    omega
  · have hrq : targetScale q M B hBM = q := by omega
    rw [hrq, pow_succ] at hnext
    have hp : 0 < (2 : ℕ) ^ q := pow_pos (by omega) _
    nlinarith

theorem targetScale_real_spec {q M B : ℕ} (hBM : B ≤ M) (hB : 0 < B)
    (hM : M ≤ 2 ^ q) :
    (B : ℝ) ≤ (M : ℝ) / (2 : ℝ) ^ targetScale q M B hBM ∧
      (M : ℝ) / (2 : ℝ) ^ targetScale q M B hBM < 2 * B := by
  have h := targetScale_spec hBM hB hM
  have hp : 0 < (2 : ℝ) ^ targetScale q M B hBM := by positivity
  constructor
  · apply (le_div_iff₀ hp).mpr
    exact_mod_cast h.2.1
  · apply (div_lt_iff₀ hp).mpr
    exact_mod_cast h.2.2


theorem bitModels_card_bound {q : ℕ} (S : Finset (BitModels q)) : S.card ≤ 2 ^ q := by
  simpa [BitModels, Fintype.card_fun] using Finset.card_le_univ S

/-- Large instances have a selected scale in range; small counts are handled exactly at zero. -/
theorem target_or_small {q M B : ℕ} (hB : 0 < B) (hM : M ≤ 2 ^ q) :
    M ≤ 4 * B ∨ ∃ r ≤ q, (B : ℝ) ≤ (M : ℝ) / (2 : ℝ) ^ r ∧
      (M : ℝ) / (2 : ℝ) ^ r < 2 * B := by
  by_cases hsmall : M ≤ 4 * B
  · exact Or.inl hsmall
  · have hBM : B ≤ M := by omega
    exact Or.inr ⟨targetScale q M B hBM, (targetScale_spec hBM hB hM).1,
      targetScale_real_spec hBM hB hM⟩

end QecReliability
