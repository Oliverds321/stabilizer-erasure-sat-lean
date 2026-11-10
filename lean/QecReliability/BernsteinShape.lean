import QecReliability.Latent

/-! Bernstein curve shape from the elementary degree recursion. -/

namespace QecReliability

open scoped BigOperators

def bernsteinBasis (r : ℕ) (p : ℝ) (j : ℕ) : ℝ :=
  (r.choose j : ℝ) * p ^ j * (1 - p) ^ (r - j)

def bernsteinSeq (r : ℕ) (f : ℕ → ℝ) (p : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1), bernsteinBasis r p j * f j

@[simp] theorem bernsteinBasis_above (r : ℕ) (p : ℝ) :
    bernsteinBasis r p (r + 1) = 0 := by simp [bernsteinBasis]

theorem bernsteinBasis_zero_succ (r : ℕ) (p : ℝ) :
    bernsteinBasis (r + 1) p 0 = (1 - p) * bernsteinBasis r p 0 := by
  simp [bernsteinBasis, pow_succ, mul_comm]

theorem bernsteinBasis_succ {r j : ℕ} (hj : j ≤ r) (p : ℝ) :
    bernsteinBasis (r + 1) p (j + 1) =
      (1 - p) * bernsteinBasis r p (j + 1) + p * bernsteinBasis r p j := by
  obtain hlt | rfl := lt_or_eq_of_le hj
  · have he : r - j = (r - (j + 1)) + 1 := by omega
    simp only [bernsteinBasis, Nat.choose_succ_succ, Nat.cast_add,
      Nat.add_sub_add_right]
    rw [he, pow_succ (1 - p), pow_succ p]
    ring
  · simp [bernsteinBasis, pow_succ, mul_comm]

theorem bernsteinSeq_succ (r : ℕ) (f : ℕ → ℝ) (p : ℝ) :
    bernsteinSeq (r + 1) f p =
      (1 - p) * bernsteinSeq r f p + p * bernsteinSeq r (fun j => f (j + 1)) p := by
  have hshift : (∑ j ∈ Finset.range (r + 1), bernsteinBasis r p (j + 1) * f (j + 1)) +
      bernsteinBasis r p 0 * f 0 = bernsteinSeq r f p := by
    rw [← Finset.sum_range_succ' (fun j => bernsteinBasis r p j * f j),
      Finset.sum_range_succ]
    simp [bernsteinSeq]
  have hsum : (∑ j ∈ Finset.range (r + 1), bernsteinBasis (r + 1) p (j + 1) * f (j + 1)) =
      (1 - p) * (∑ j ∈ Finset.range (r + 1), bernsteinBasis r p (j + 1) * f (j + 1)) +
      p * bernsteinSeq r (fun j => f (j + 1)) p := by
    simp only [bernsteinSeq, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [bernsteinBasis_succ (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
    ring
  unfold bernsteinSeq at hshift ⊢
  rw [Finset.sum_range_succ', bernsteinBasis_zero_succ, hsum]
  unfold bernsteinSeq
  rw [← hshift]
  ring

theorem bernsteinSeq_mono {r : ℕ} {f g : ℕ → ℝ} {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hfg : ∀ j, f j ≤ g j) :
    bernsteinSeq r f p ≤ bernsteinSeq r g p := by
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left (hfg j)
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _))
    (pow_nonneg (sub_nonneg.mpr hp1) _)

theorem bernsteinSeq_antitone (r : ℕ) (f : ℕ → ℝ) (hf : Antitone f) :
    AntitoneOn (bernsteinSeq r f) (Set.Icc 0 1) := by
  induction r generalizing f with
  | zero => simp [bernsteinSeq, bernsteinBasis, AntitoneOn]
  | succ r ih =>
    intro p hp q hq hpq
    rw [bernsteinSeq_succ, bernsteinSeq_succ]
    have hfirst := ih f hf hp hq hpq
    have htail := ih (fun j => f (j + 1)) (fun i j hij => hf (by omega)) hp hq hpq
    have horder : bernsteinSeq r (fun j => f (j + 1)) q ≤ bernsteinSeq r f q :=
      bernsteinSeq_mono hq.1 hq.2 (fun j => hf (Nat.le_succ j))
    have h1 := mul_le_mul_of_nonneg_left hfirst (sub_nonneg.mpr hp.2)
    have h2 := mul_le_mul_of_nonneg_left htail hp.1
    have h3 := mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr horder)
    nlinarith

def extendCoefficients {r : ℕ} (f : Fin (r + 1) → ℝ) (j : ℕ) : ℝ :=
  f ⟨min j r, Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem extendCoefficients_antitone {r : ℕ} (f : Fin (r + 1) → ℝ) (hf : Antitone f) :
    Antitone (extendCoefficients f) := by
  intro i j hij
  exact hf (min_le_min_right r hij)

theorem bernsteinCurve_eq_seq (r : ℕ) (f : Fin (r + 1) → ℝ) (p : ℝ) :
    bernsteinCurve r f p = bernsteinSeq r (extendCoefficients f) p := by
  have he : (∑ j : Fin (r + 1), bernsteinBasis r p j.val * extendCoefficients f j.val) =
      bernsteinSeq r (extendCoefficients f) p :=
    Fin.sum_univ_eq_sum_range (fun j => bernsteinBasis r p j * extendCoefficients f j) (r + 1)
  rw [← he]
  unfold bernsteinCurve average
  apply Finset.sum_congr rfl
  intro j _
  have hj : min j.val r = j.val := min_eq_left (Nat.le_of_lt_succ j.isLt)
  simp [bernsteinWeight, bernsteinBasis, extendCoefficients, hj]

/-- Nonincreasing coefficients give a nonincreasing curve throughout the closed interval. -/
theorem bernsteinCurve_antitone {r : ℕ} (f : Fin (r + 1) → ℝ) (hf : Antitone f) :
    AntitoneOn (bernsteinCurve r f) (Set.Icc 0 1) := by
  intro p hp q hq hpq
  rw [bernsteinCurve_eq_seq, bernsteinCurve_eq_seq]
  exact bernsteinSeq_antitone r _ (extendCoefficients_antitone f hf) hp hq hpq

@[simp] theorem extendCoefficients_at {r : ℕ} (f : Fin (r + 1) → ℝ) (j : Fin (r + 1)) :
    extendCoefficients f j.val = f j := by
  simp [extendCoefficients, min_eq_left (Nat.le_of_lt_succ j.isLt)]

def shapeInput {r : ℕ} (f g : Fin (r + 1) → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then f ⟨0, Nat.zero_lt_succ r⟩
  else if j = r then f ⟨r, Nat.lt_succ_self r⟩ else extendCoefficients g j

def shapeCoefficients {r : ℕ} (f g : Fin (r + 1) → ℝ) (j : Fin (r + 1)) : ℝ :=
  repaired (f ⟨r, Nat.lt_succ_self r⟩) (shapeInput f g) j.val

theorem relPair_refl {ε f : ℝ} (hε : 0 ≤ ε) (hf : 0 ≤ f) (hf1 : f ≤ 1) :
    RelPair ε f f := by
  simp only [RelPair, sub_self, abs_zero]
  exact ⟨mul_nonneg hε hf, mul_nonneg hε (sub_nonneg.mpr hf1)⟩

theorem shapeInput_relPair {r : ℕ} {ε : ℝ} (f g : Fin (r + 1) → ℝ)
    (hε : 0 ≤ ε) (hf : ∀ j, 0 ≤ f j ∧ f j ≤ 1) (hfg : ∀ j, RelPair ε (f j) (g j))
    (j : ℕ) (hj : j ≤ r) : RelPair ε (extendCoefficients f j) (shapeInput f g j) := by
  let i : Fin (r + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hi : i.val = j := rfl
  rw [← hi, extendCoefficients_at]
  by_cases h0 : j = 0
  · have he : i = ⟨0, Nat.zero_lt_succ r⟩ := Fin.ext h0
    simp only [shapeInput, hi, h0, ite_true]
    rw [← he]
    exact relPair_refl hε (hf i).1 (hf i).2
  · by_cases hr : j = r
    · have he : i = ⟨r, Nat.lt_succ_self r⟩ := Fin.ext hr
      simp only [shapeInput, hi, if_neg h0, if_pos hr]
      rw [← he]
      exact relPair_refl hε (hf i).1 (hf i).2
    · simp only [shapeInput, hi, if_neg h0, if_neg hr]
      rw [← hi, extendCoefficients_at]
      exact hfg i

theorem shapeCoefficients_antitone {r : ℕ} (f g : Fin (r + 1) → ℝ) :
    Antitone (shapeCoefficients f g) := by
  intro i j hij
  exact repaired_antitone _ _ hij

theorem shapeInput_endpoints {r : ℕ} (f g : Fin (r + 1) → ℝ) :
    shapeInput f g 0 = f ⟨0, Nat.zero_lt_succ r⟩ ∧
      shapeInput f g r = f ⟨r, Nat.lt_succ_self r⟩ := by
  constructor
  · simp [shapeInput]
  · by_cases hr : r = 0
    · subst r
      simp [shapeInput]
    · simp [shapeInput, hr]

theorem shapeCoefficients_endpoints {r : ℕ} (f g : Fin (r + 1) → ℝ) (hanti : Antitone f) :
    shapeCoefficients f g ⟨0, Nat.zero_lt_succ r⟩ = f ⟨0, Nat.zero_lt_succ r⟩ ∧
      shapeCoefficients f g ⟨r, Nat.lt_succ_self r⟩ = f ⟨r, Nat.lt_succ_self r⟩ := by
  exact repaired_endpoints (hanti (show (⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1)) ≤
    ⟨r, Nat.lt_succ_self r⟩ from Nat.zero_le r))
    (shapeInput_endpoints f g).1 (shapeInput_endpoints f g).2

theorem shapeCoefficients_relPair {r : ℕ} {ε : ℝ} (f g : Fin (r + 1) → ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hf : ∀ j, 0 ≤ f j ∧ f j ≤ 1)
    (hanti : Antitone f) (hfg : ∀ j, RelPair ε (f j) (g j)) (j : Fin (r + 1)) :
    RelPair ε (f j) (shapeCoefficients f g j) := by
  have h := repaired_relPair (f := extendCoefficients f) (g := shapeInput f g)
    (n := r) hε hε1 (Nat.le_of_lt_succ j.isLt)
    (fun i k hik _ => extendCoefficients_antitone f hanti hik)
    (shapeInput_relPair f g hε hf hfg)
    (show 0 ≤ extendCoefficients f j.val by simpa using (hf j).1)
    (show extendCoefficients f j.val ≤ 1 by simpa using (hf j).2)
    (show f ⟨r, Nat.lt_succ_self r⟩ ≤ extendCoefficients f j.val by
      simpa using hanti (show j ≤ ⟨r, Nat.lt_succ_self r⟩ from Nat.le_of_lt_succ j.isLt))
  simpa only [shapeCoefficients, extendCoefficients_at] using h

/-- Exact endpoints, both-tail accuracy, range, and monotonicity of the repaired curve. -/
theorem shape_curve_contract {r : ℕ} {ε : ℝ} (f g : Fin (r + 1) → ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hf : ∀ j, 0 ≤ f j ∧ f j ≤ 1)
    (hanti : Antitone f) (hfg : ∀ j, RelPair ε (f j) (g j)) :
    AntitoneOn (bernsteinCurve r (shapeCoefficients f g)) (Set.Icc 0 1) ∧
      bernsteinCurve r (shapeCoefficients f g) 0 = f ⟨0, Nat.zero_lt_succ r⟩ ∧
      bernsteinCurve r (shapeCoefficients f g) 1 = f ⟨r, Nat.lt_succ_self r⟩ ∧
      ∀ p ∈ Set.Icc (0 : ℝ) 1,
        RelPair ε (bernsteinCurve r f p) (bernsteinCurve r (shapeCoefficients f g) p) ∧
        f ⟨r, Nat.lt_succ_self r⟩ ≤ bernsteinCurve r (shapeCoefficients f g) p ∧
        bernsteinCurve r (shapeCoefficients f g) p ≤ f ⟨0, Nat.zero_lt_succ r⟩ ∧
        0 ≤ bernsteinCurve r (shapeCoefficients f g) p ∧
        bernsteinCurve r (shapeCoefficients f g) p ≤ 1 := by
  have ha := bernsteinCurve_antitone _ (shapeCoefficients_antitone f g)
  have hends := shapeCoefficients_endpoints f g hanti
  have hz : bernsteinCurve r (shapeCoefficients f g) 0 = f ⟨0, Nat.zero_lt_succ r⟩ :=
    (bernsteinCurve_zero _ _).trans hends.1
  have ho : bernsteinCurve r (shapeCoefficients f g) 1 = f ⟨r, Nat.lt_succ_self r⟩ :=
    (bernsteinCurve_one _ _).trans hends.2
  refine ⟨ha, hz, ho, ?_⟩
  intro p hp
  have hlow := ha hp (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num) hp.2
  have hhigh := ha (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num) hp hp.1
  rw [ho] at hlow
  rw [hz] at hhigh
  exact ⟨bernsteinCurve_relPair hp.1 hp.2 (shapeCoefficients_relPair f g hε hε1 hf hanti hfg),
    hlow, hhigh, le_trans (hf _).1 hlow, le_trans hhigh (hf _).2⟩

end QecReliability
