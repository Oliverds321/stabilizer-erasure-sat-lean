import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Two-sided relative normalization and finite monotone repair. -/

namespace QecReliability

def RelPair (ε f g : ℝ) : Prop :=
  |g - f| ≤ ε * f ∧ |g - f| ≤ ε * (1 - f)

def relLower (ε f : ℝ) : ℝ := max ((1 - ε) * f) ((1 + ε) * f - ε)

def relUpper (ε f : ℝ) : ℝ := min ((1 + ε) * f) (ε + (1 - ε) * f)

theorem RelPair.range {ε f g : ℝ} (h : RelPair ε f g)
    (hε1 : ε ≤ 1) (hf : 0 ≤ f) (hf1 : f ≤ 1) : 0 ≤ g ∧ g ≤ 1 := by
  have hlo := (abs_le.mp h.1).1
  have hhi := (abs_le.mp h.2).2
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hε1) hf]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hε1) (sub_nonneg.mpr hf1)]

theorem relPair_iff_interval (ε f g : ℝ) :
    RelPair ε f g ↔ relLower ε f ≤ g ∧ g ≤ relUpper ε f := by
  simp only [RelPair, relLower, relUpper, abs_le, max_le_iff, le_min_iff]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;>
    constructor <;> constructor <;> linarith

theorem relLower_mono {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Monotone (relLower ε) := by
  intro x y hxy
  exact max_le_max
    (mul_le_mul_of_nonneg_left hxy (by linarith))
    (sub_le_sub_right (mul_le_mul_of_nonneg_left hxy (by linarith)) ε)

theorem relUpper_mono {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Monotone (relUpper ε) := by
  intro x y hxy
  exact min_le_min
    (mul_le_mul_of_nonneg_left hxy (by linarith))
    (add_le_add_right (mul_le_mul_of_nonneg_left hxy (sub_nonneg.mpr hε1)) ε)

theorem relLower_le_self {ε f : ℝ} (hε : 0 ≤ ε) (hf : 0 ≤ f) (hf1 : f ≤ 1) :
    relLower ε f ≤ f := by
  apply max_le
  · nlinarith [mul_nonneg hε hf]
  · nlinarith [mul_nonneg hε (sub_nonneg.mpr hf1)]

theorem self_le_relUpper {ε f : ℝ} (hε : 0 ≤ ε) (hf : 0 ≤ f) (hf1 : f ≤ 1) :
    f ≤ relUpper ε f := by
  apply le_min
  · nlinarith [mul_nonneg hε hf]
  · nlinarith [mul_nonneg hε (sub_nonneg.mpr hf1)]

theorem ratio_eps_third {ε u v : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hu : 1 - ε / 3 ≤ u) (hu' : u ≤ 1 + ε / 3)
    (hv : 1 - ε / 3 ≤ v) (hv' : v ≤ 1 + ε / 3) :
    0 < v ∧ 1 - ε ≤ u / v ∧ u / v ≤ 1 + ε := by
  have hv0 : 0 < v := by linarith
  refine ⟨hv0, (le_div_iff₀ hv0).mpr ?_, (div_le_iff₀ hv0).mpr ?_⟩
  · calc
      (1 - ε) * v ≤ (1 - ε) * (1 + ε / 3) :=
        mul_le_mul_of_nonneg_left hv' (by linarith)
      _ ≤ 1 - ε / 3 := by nlinarith [sq_nonneg ε]
      _ ≤ u := hu
  · calc
      u ≤ 1 + ε / 3 := hu'
      _ ≤ (1 + ε) * (1 - ε / 3) := by
        nlinarith [mul_nonneg hε (sub_nonneg.mpr hε1)]
      _ ≤ (1 + ε) * v := mul_le_mul_of_nonneg_left hv (by linarith)

/-- Multiplicative errors at tolerance ε/3 control both normalized tails. -/
theorem normalized_pair {ε f α β : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hf : 0 ≤ f) (hf1 : f ≤ 1)
    (hα : 1 - ε / 3 ≤ α) (hα' : α ≤ 1 + ε / 3)
    (hβ : 1 - ε / 3 ≤ β) (hβ' : β ≤ 1 + ε / 3) :
    RelPair ε f (f * α / (f * α + (1 - f) * β)) := by
  let D := f * α + (1 - f) * β
  have hfl : 0 ≤ 1 - f := sub_nonneg.mpr hf1
  have hD : 1 - ε / 3 ≤ D := by
    have h1 := mul_le_mul_of_nonneg_left hα hf
    have h2 := mul_le_mul_of_nonneg_left hβ hfl
    dsimp [D]
    nlinarith
  have hD' : D ≤ 1 + ε / 3 := by
    have h1 := mul_le_mul_of_nonneg_left hα' hf
    have h2 := mul_le_mul_of_nonneg_left hβ' hfl
    dsimp [D]
    nlinarith
  obtain ⟨hD0, hA, hA'⟩ := ratio_eps_third hε hε1 hα hα' hD hD'
  obtain ⟨_, hB, hB'⟩ := ratio_eps_third hε hε1 hβ hβ' hD hD'
  have h1 := mul_le_mul_of_nonneg_left hA hf
  have h2 := mul_le_mul_of_nonneg_left hA' hf
  have h3 := mul_le_mul_of_nonneg_left hB hfl
  have h4 := mul_le_mul_of_nonneg_left hB' hfl
  have hc : 1 - f * α / D = (1 - f) * β / D := by
    apply (eq_div_iff hD0.ne').mpr
    field_simp
    dsimp [D]
    ring
  rw [← mul_div_assoc] at h1 h2 h3 h4
  change RelPair ε f (f * α / D)
  constructor <;> apply abs_le.mpr <;> constructor <;> nlinarith

theorem exists_relative_multiplier {η a ah : ℝ} (hη : 0 ≤ η) (ha : 0 ≤ a)
    (herr : |ah - a| ≤ η * a) :
    ∃ α, 1 - η ≤ α ∧ α ≤ 1 + η ∧ ah = a * α := by
  by_cases ha0 : a = 0
  · have hah : ah = 0 := by simpa [ha0] using herr
    exact ⟨1, by linarith, by linarith, by simp [ha0, hah]⟩
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have he := abs_le.mp herr
    refine ⟨ah / a, (le_div_iff₀ ha').mpr ?_, (div_le_iff₀ ha').mpr ?_, ?_⟩
    · nlinarith [he.1]
    · nlinarith [he.2]
    · field_simp

/-- Count estimates with exact zeros can be normalized without losing either tail. -/
theorem normalize_counts {ε A B Ah Bh : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 < A + B)
    (hAh : |Ah - A| ≤ (ε / 3) * A) (hBh : |Bh - B| ≤ (ε / 3) * B) :
    0 < Ah + Bh ∧ 0 ≤ Ah / (Ah + Bh) ∧ Ah / (Ah + Bh) ≤ 1 ∧
      RelPair ε (A / (A + B)) (Ah / (Ah + Bh)) := by
  obtain ⟨α, hα, hα', rfl⟩ := exists_relative_multiplier (by positivity) hA hAh
  obtain ⟨β, hβ, hβ', rfl⟩ := exists_relative_multiplier (by positivity) hB hBh
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := by linarith
  have hD : 0 < A * α + B * β := by
    have h1 := mul_le_mul_of_nonneg_left hα hA
    have h2 := mul_le_mul_of_nonneg_left hβ hB
    nlinarith [mul_pos hT (show 0 < 1 - ε / 3 by linarith)]
  have hf0 : 0 ≤ A / (A + B) := div_nonneg hA hT.le
  have hf1 : A / (A + B) ≤ 1 := (div_le_one hT).mpr (by linarith)
  have hp := normalized_pair hε hε1 hf0 hf1 hα hα' hβ hβ'
  have heq : (A / (A + B) * α /
      (A / (A + B) * α + (1 - A / (A + B)) * β)) =
      A * α / (A * α + B * β) := by
    have hcomp : 1 - A / (A + B) = B / (A + B) := by
      field_simp
      ring
    rw [hcomp]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      div_div_div_cancel_right₀ hT.ne']
  refine ⟨hD, div_nonneg (mul_nonneg hA hα0.le) hD.le,
    (div_le_one hD).mpr (by nlinarith [mul_nonneg hB hβ0.le]), ?_⟩
  rwa [heq] at hp

def runningMin (g : ℕ → ℝ) : ℕ → ℝ
  | 0 => g 0
  | j + 1 => min (runningMin g j) (g (j + 1))

theorem runningMin_le_current (g : ℕ → ℝ) (j : ℕ) : runningMin g j ≤ g j := by
  cases j with
  | zero => exact le_rfl
  | succ j => exact min_le_right _ _

theorem le_runningMin_iff (g : ℕ → ℝ) (j : ℕ) (a : ℝ) :
    a ≤ runningMin g j ↔ ∀ i ≤ j, a ≤ g i := by
  induction j with
  | zero => simp [runningMin]
  | succ j ih =>
    rw [runningMin, le_min_iff, ih]
    constructor
    · rintro ⟨h, hlast⟩ i hi
      by_cases hij : i ≤ j
      · exact h i hij
      · have : i = j + 1 := by omega
        simpa [this] using hlast
    · intro h
      exact ⟨fun i hi => h i (by omega), h (j + 1) le_rfl⟩

theorem runningMin_antitone (g : ℕ → ℝ) : Antitone (runningMin g) := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hj ih => exact le_trans (min_le_left _ _) ih

def repaired (ell : ℝ) (g : ℕ → ℝ) (j : ℕ) : ℝ := max ell (runningMin g j)

theorem repaired_antitone (ell : ℝ) (g : ℕ → ℝ) : Antitone (repaired ell g) := by
  intro i j hij
  exact max_le_max_left ell (runningMin_antitone g hij)

theorem repaired_bounds {ell a : ℝ} {g : ℕ → ℝ} (hell : ell ≤ a) (h0 : g 0 = a)
    (j : ℕ) : ell ≤ repaired ell g j ∧ repaired ell g j ≤ a := by
  refine ⟨le_max_left _ _, max_le hell ?_⟩
  have h := runningMin_antitone g (Nat.zero_le j)
  simpa only [runningMin, h0] using h

theorem repaired_endpoints {ell a : ℝ} {g : ℕ → ℝ} {n : ℕ}
    (hell : ell ≤ a) (h0 : g 0 = a) (hn : g n = ell) :
    repaired ell g 0 = a ∧ repaired ell g n = ell := by
  constructor
  · simpa [repaired, runningMin, h0] using max_eq_right hell
  · apply max_eq_left
    simpa [hn] using runningMin_le_current g n

/-- Shape repair preserves both relative bounds without consuming more tolerance. -/
theorem repaired_relPair {ε ell : ℝ} {f g : ℕ → ℝ} {n j : ℕ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hj : j ≤ n)
    (hanti : ∀ i k, i ≤ k → k ≤ n → f k ≤ f i)
    (hpair : ∀ i ≤ n, RelPair ε (f i) (g i))
    (hf : 0 ≤ f j) (hf1 : f j ≤ 1) (hell : ell ≤ f j) :
    RelPair ε (f j) (repaired ell g j) := by
  apply (relPair_iff_interval _ _ _).mpr
  have hlo : relLower ε (f j) ≤ runningMin g j := by
    apply (le_runningMin_iff g j _).mpr
    intro i hi
    exact le_trans (relLower_mono hε hε1 (hanti i j hi hj))
      ((relPair_iff_interval _ _ _).mp (hpair i (by omega))).1
  have hhi : runningMin g j ≤ relUpper ε (f j) :=
    le_trans (runningMin_le_current g j) ((relPair_iff_interval _ _ _).mp (hpair j hj)).2
  exact ⟨le_trans hlo (le_max_right _ _),
    max_le (le_trans hell (self_le_relUpper hε hf hf1)) hhi⟩

end QecReliability
