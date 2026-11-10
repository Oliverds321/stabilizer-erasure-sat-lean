import PhysicalBridge.RationalBudgets

/-! A direct fixed-denominator Bernstein evaluator. Inputs and outputs are
natural numerator/denominator pairs. This is separate from acquisition of
exact physical endpoints or construction of rational repaired coefficients.
The size result bounds the output pair, not every intermediate or runtime. -/
namespace QecReliability
open scoped BigOperators

def commonDenominator {r : ℕ} (den : Fin (r+1) → ℕ) : ℕ := ∏ j, den j

def scaledNumerator {r : ℕ} (num den : Fin (r+1) → ℕ) (j : Fin (r+1)) : ℕ :=
  num j * (commonDenominator den / den j)

def integerBernstein (r : ℕ) (A : Fin (r+1) → ℕ) (u v : ℕ) : ℕ :=
  ∑ j, r.choose j.val * u^j.val * (v-u)^(r-j.val) * A j

/-- Direct finite-sum evaluation, not the optional rolling de Casteljau implementation. -/
def evaluateRationalCurve {r : ℕ} (num den : Fin (r+1) → ℕ) (u v : ℕ) : ℕ × ℕ :=
  if r=0 then (num 0,den 0) else
    (integerBernstein r (scaledNumerator num den) u v, commonDenominator den*v^r)

theorem commonDenominator_pos {r : ℕ} {den : Fin (r+1) → ℕ}
    (hd : ∀ j, 0<den j) : 0<commonDenominator den :=
  Finset.prod_pos (fun j _ => hd j)

theorem denominator_dvd_common {r : ℕ} (den : Fin (r+1) → ℕ) (j : Fin (r+1)) :
    den j ∣ commonDenominator den :=
  Finset.dvd_prod_of_mem den (Finset.mem_univ j)

theorem scaledNumerator_cast {r : ℕ} (num den : Fin (r+1) → ℕ) (j : Fin (r+1)) :
    (scaledNumerator num den j : ℝ) =
      (commonDenominator den : ℝ)*((num j : ℝ)/den j) := by
  unfold scaledNumerator
  rw [Nat.cast_mul,Nat.cast_div_charZero (denominator_dvd_common den j)]
  ring

theorem bernsteinWeight_fixed_denominator {r u v : ℕ}
    (huv : u≤v) (hv : 0<v) (j : Fin (r+1)) :
    (v:ℝ)^r * bernsteinWeight r ((u:ℝ)/v) j =
      (r.choose j.val:ℝ)*(u:ℝ)^j.val*((v-u:ℕ):ℝ)^(r-j.val) := by
  have hv' : (v:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hv
  have hj : j.val≤r := Nat.le_of_lt_succ j.isLt
  have hp : (v:ℝ)^r = (v:ℝ)^j.val*(v:ℝ)^(r-j.val) := by
    rw [←pow_add,Nat.add_sub_of_le hj]
  unfold bernsteinWeight
  rw [Nat.cast_sub huv,hp,one_sub_div hv',div_pow,div_pow]
  field_simp

theorem integerBernstein_cast {r u v : ℕ} (num den : Fin (r+1) → ℕ)
    (huv : u≤v) (hv : 0<v) :
    (integerBernstein r (scaledNumerator num den) u v:ℝ) =
      (commonDenominator den:ℝ)*(v:ℝ)^r *
        bernsteinCurve r (fun j => (num j:ℝ)/den j) ((u:ℝ)/v) := by
  unfold integerBernstein bernsteinCurve average
  rw [Nat.cast_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_pow,
    scaledNumerator_cast]
  have hw := bernsteinWeight_fixed_denominator huv hv j
  rw [←hw]
  ring

theorem evaluateRationalCurve_semantics {r u v : ℕ} (num den : Fin (r+1) → ℕ)
    (hd : ∀ j, 0<den j) (huv : u≤v) (hv : 0<v) :
    ((evaluateRationalCurve num den u v).1:ℝ)/(evaluateRationalCurve num den u v).2 =
      bernsteinCurve r (fun j => (num j:ℝ)/den j) ((u:ℝ)/v) := by
  unfold evaluateRationalCurve
  split_ifs with hr
  · subst r
    simp [bernsteinCurve,average,bernsteinWeight]
  · simp only [Nat.cast_mul,Nat.cast_pow]
    rw [integerBernstein_cast num den huv hv]
    have hD : (commonDenominator den:ℝ)≠0 := by
      exact_mod_cast Nat.ne_of_gt (commonDenominator_pos hd)
    have hv' : (v:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hv
    field_simp

theorem evaluateRationalCurve_den_pos {r u v : ℕ} (num den : Fin (r+1) → ℕ)
    (hd : ∀ j, 0<den j) (hv : 0<v) : 0<(evaluateRationalCurve num den u v).2 := by
  unfold evaluateRationalCurve
  split_ifs
  · exact hd 0
  · exact Nat.mul_pos (commonDenominator_pos hd) (Nat.pow_pos hv)

theorem evaluateRationalCurve_num_le_den {r u v : ℕ} (num den : Fin (r+1) → ℕ)
    (hd : ∀ j, 0<den j) (hn : ∀ j, num j≤den j) (huv : u≤v) (hv : 0<v) :
    (evaluateRationalCurve num den u v).1≤(evaluateRationalCurve num den u v).2 := by
  have hv' : (0:ℝ)<v := by exact_mod_cast hv
  have hp : (u:ℝ)/v≤1 := (div_le_one hv').mpr (by exact_mod_cast huv)
  have hf : ∀ j, 0≤(num j:ℝ)/den j ∧ (num j:ℝ)/den j≤1 := by
    intro j
    have hj : (0:ℝ)<den j := by exact_mod_cast hd j
    exact ⟨div_nonneg (Nat.cast_nonneg _) hj.le,
      (div_le_one hj).mpr (by exact_mod_cast hn j)⟩
  have h := (bernsteinCurve_range (div_nonneg (Nat.cast_nonneg _) hv'.le) hp hf).2
  rw [←evaluateRationalCurve_semantics num den hd huv hv] at h
  have hD : (0:ℝ)<(evaluateRationalCurve num den u v).2 := by
    exact_mod_cast evaluateRationalCurve_den_pos num den hd hv
  exact_mod_cast (div_le_one hD).mp h

theorem size_mul_pow_bound (D v r : ℕ) : (D*v^r).size≤D.size+r*v.size := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ,←Nat.mul_assoc]
    have h := size_mul_bound (D*v^r) v
    nlinarith

theorem size_prod_bound {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    (∏ j ∈ s, f j).size≤1+∑ j ∈ s, (f j).size := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha]
    have h := size_mul_bound (f a) (∏ j ∈ s, f j)
    omega

theorem commonDenominator_size {r H : ℕ} (den : Fin (r+1) → ℕ)
    (hH : ∀ j, (den j).size≤H) : (commonDenominator den).size≤1+(r+1)*H := by
  have h := size_prod_bound Finset.univ den
  have hs : (∑ j : Fin (r+1), (den j).size)≤(r+1)*H := by
    simpa using Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hH j)
  exact h.trans (Nat.add_le_add_left hs 1)

/-- Output storage only. No claim about all temporaries, heap space or runtime. -/
theorem evaluateRationalCurve_output_size {r u v H : ℕ} (num den : Fin (r+1) → ℕ)
    (hd : ∀ j, 0<den j) (hn : ∀ j, num j≤den j) (huv : u≤v) (hv : 0<v)
    (hH : ∀ j, (den j).size≤H) :
    (evaluateRationalCurve num den u v).1.size≤1+(r+1)*H+r*v.size ∧
    (evaluateRationalCurve num den u v).2.size≤1+(r+1)*H+r*v.size := by
  have hden : (evaluateRationalCurve num den u v).2.size≤1+(r+1)*H+r*v.size := by
    unfold evaluateRationalCurve
    split_ifs with hr
    · subst r
      simpa [Nat.add_comm] using (hH 0).trans (Nat.le_succ H)
    · exact (size_mul_pow_bound _ _ _).trans
        (Nat.add_le_add_right (commonDenominator_size den hH) _)
  exact ⟨(Nat.size_le_size (evaluateRationalCurve_num_le_den num den hd hn huv hv)).trans hden,hden⟩

theorem evaluateRationalCurve_zero (num den : Fin 1 → ℕ) (u v : ℕ) :
    evaluateRationalCurve num den u v=(num 0,den 0) := rfl

theorem evaluateRationalCurve_zero_size {H : ℕ} (num den : Fin 1 → ℕ) (u v : ℕ)
    (hn : num 0≤den 0) (hH : (den 0).size≤H) :
    (evaluateRationalCurve num den u v).1.size≤H ∧
    (evaluateRationalCurve num den u v).2.size≤H :=
  ⟨(Nat.size_le_size hn).trans hH,hH⟩

end QecReliability
