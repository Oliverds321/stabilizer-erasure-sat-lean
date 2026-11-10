import QecReliability.TensorBernstein
import QecReliability.HammingMonotonicity

/-! Multiple finite latent probability classes. Each class has its own Bernoulli
parameter. All causes are retained, even when the observation map is many-to-one.
The empty list and classes of size zero are included in every theorem below.
These are exact probability identities, without machine runtime claims. -/

noncomputable section

namespace QecReliability.TensorLatent

open scoped BigOperators
open TensorBernstein

/-- One subset of active causes for each class. -/
def CausesGrid : List ℕ → Type
  | [] => PUnit
  | r :: ds => Causes r × CausesGrid ds

instance causesGridFintype : (ds : List ℕ) → Fintype (CausesGrid ds)
  | [] => inferInstanceAs (Fintype PUnit)
  | r :: ds =>
    letI := causesGridFintype ds
    inferInstanceAs (Fintype (Causes r × CausesGrid ds))

/-- The product subset order compares the active causes in every class. -/
instance causesGridPartialOrder : (ds : List ℕ) → PartialOrder (CausesGrid ds)
  | [] => inferInstanceAs (PartialOrder PUnit)
  | r :: ds =>
    letI := causesGridPartialOrder ds
    inferInstanceAs (PartialOrder (Causes r × CausesGrid ds))

/-- Independent Bernoulli mass of a complete tuple of latent causes. -/
def mass : (ds : List ℕ) → Params ds → CausesGrid ds → ℝ
  | [], _, _ => 1
  | r :: ds, p, b =>
    (p.1 ^ b.1.card * (1 - p.1) ^ (r - b.1.card)) * mass ds p.2 b.2

/-- Iterated expectation over independent finite Bernoulli classes. -/
def expectation : (ds : List ℕ) → (CausesGrid ds → ℝ) → Params ds → ℝ
  | [], score, _ => score PUnit.unit
  | r :: ds, score, p =>
    latentCurve (id : Causes r → Causes r)
      (fun b => expectation ds (fun bs => score (b, bs)) p.2) p.1

/-- The iterated expectation is the sum of product masses over all cause tuples. -/
theorem expectation_eq_sum (ds : List ℕ) (score : CausesGrid ds → ℝ)
    (p : Params ds) :
    expectation ds score p = ∑ b, mass ds p b * score b := by
  induction ds with
  | nil =>
    classical
    change score PUnit.unit = ∑ b : PUnit, (1 : ℝ) * score b
    simp only [one_mul]
    symm
    apply Finset.sum_eq_single PUnit.unit
    · intro b _ hb
      exact (hb (Subsingleton.elim _ _)).elim
    · intro h
      exact (h (Finset.mem_univ _)).elim
  | cons r ds ih =>
    change (∑ b : Causes r, (p.1 ^ b.card * (1 - p.1) ^ (r - b.card)) *
      expectation ds (fun bs => score (b, bs)) p.2) =
      ∑ b : Causes r × CausesGrid ds,
        ((p.1 ^ b.1.card * (1 - p.1) ^ (r - b.1.card)) *
          mass ds p.2 b.2) * score b
    rw [Fintype.sum_prod_type]
    simp_rw [ih, Finset.mul_sum, mul_assoc]

/-- Average within every Hamming layer, counting each latent cause separately. -/
def layerCoefficients : (ds : List ℕ) → (CausesGrid ds → ℝ) → Grid ds → ℝ
  | [], score, _ => score PUnit.unit
  | r :: ds, score, j =>
    layerAverage (id : Causes r → Causes r)
      (fun b => layerCoefficients ds (fun bs => score (b, bs)) j.2) j.1

/-- At a Boolean parameter corner each class is deterministically empty or full. -/
def cornerCauses : (ds : List ℕ) → Corner ds → CausesGrid ds
  | [], _ => PUnit.unit
  | r :: ds, b => (if b.1 then Finset.univ else ∅, cornerCauses ds b.2)

/-- Tensor corner coefficients are the scores of their deterministic cause tuples. -/
theorem layerCoefficients_corner (ds : List ℕ) (score : CausesGrid ds → ℝ)
    (b : Corner ds) :
    layerCoefficients ds score (cornerIndex ds b) = score (cornerCauses ds b) := by
  induction ds with
  | nil => rfl
  | cons r ds ih =>
    rcases b with ⟨b, bs⟩
    cases b with
    | false =>
      change layerAverage (id : Causes r → Causes r)
        (fun a => layerCoefficients ds (fun cs => score (a, cs)) (cornerIndex ds bs))
        ⟨0, Nat.zero_lt_succ r⟩ = score (∅, cornerCauses ds bs)
      rw [layerAverage_zero]
      exact ih _ bs
    | true =>
      change layerAverage (id : Causes r → Causes r)
        (fun a => layerCoefficients ds (fun cs => score (a, cs)) (cornerIndex ds bs))
        ⟨r, Nat.lt_succ_self r⟩ = score (Finset.univ, cornerCauses ds bs)
      rw [layerAverage_last]
      exact ih _ bs

/-- A concrete representative chooses the first requested number of causes in each class. -/
def canonicalCauses : (ds : List ℕ) → Grid ds → CausesGrid ds
  | [], _ => PUnit.unit
  | r :: ds, j =>
    (Finset.univ.filter (fun i : Fin r => i.val < j.1.val), canonicalCauses ds j.2)

/-- The concrete prefix representatives agree with the deterministic corner tuples. -/
theorem canonicalCauses_corner (ds : List ℕ) (b : Corner ds) :
    canonicalCauses ds (cornerIndex ds b) = cornerCauses ds b := by
  induction ds with
  | nil => rfl
  | cons r ds ih =>
    rcases b with ⟨b, bs⟩
    cases b with
    | false =>
      change (Finset.univ.filter (fun i : Fin r => i.val < 0),
        canonicalCauses ds (cornerIndex ds bs)) = (∅, cornerCauses ds bs)
      have hz : Finset.univ.filter (fun i : Fin r => i.val < 0) = ∅ := by simp
      rw [hz, ih bs]
    | true =>
      change (Finset.univ.filter (fun i : Fin r => i.val < r),
        canonicalCauses ds (cornerIndex ds bs)) = (Finset.univ, cornerCauses ds bs)
      have hr : Finset.univ.filter (fun i : Fin r => i.val < r) = Finset.univ := by
        ext i
        simp [i.isLt]
      rw [hr, ih bs]

private theorem layerAverage_eq_average {r : ℕ} (f : Causes r → ℝ)
    (j : Fin (r + 1)) :
    layerAverage id f j =
      average (fun _ : {b : Causes r // hammingLayer b = j} =>
        (r.choose j.val : ℝ)⁻¹) (fun b => f b.val) := by
  classical
  simp only [layerAverage, average, id_eq, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  exact mul_comm _ _

private theorem curve_layerAverage (ds : List ℕ) {r : ℕ}
    (f : Causes r → Grid ds → ℝ) (j : Fin (r + 1)) (p : Params ds) :
    curve ds (fun k => layerAverage id (fun b => f b k) j) p =
      layerAverage id (fun b => curve ds (f b) p) j := by
  classical
  simp only [layerAverage_eq_average]
  exact curve_average ds _ _ p

/-- The actual independent latent expectation is exactly a tensor Bernstein curve. -/
theorem expectation_eq_tensor (ds : List ℕ) (score : CausesGrid ds → ℝ)
    (p : Params ds) :
    expectation ds score p = curve ds (layerCoefficients ds score) p := by
  induction ds with
  | nil => rfl
  | cons r ds ih =>
    change latentCurve (id : Causes r → Causes r)
      (fun b => expectation ds (fun bs => score (b, bs)) p.2) p.1 =
      bernsteinCurve r (fun j => curve ds
        (fun k => layerAverage id
          (fun b => layerCoefficients ds (fun bs => score (b, bs)) k) j) p.2) p.1
    rw [latentCurve_eq_bernstein]
    simp_rw [ih, curve_layerAverage]

/-- Unit-interval scores give unit-interval tensor coefficients. -/
theorem layerCoefficients_range (ds : List ℕ) (score : CausesGrid ds → ℝ)
    (hscore : ∀ b, 0 ≤ score b ∧ score b ≤ 1) (j : Grid ds) :
    0 ≤ layerCoefficients ds score j ∧ layerCoefficients ds score j ≤ 1 := by
  induction ds with
  | nil => exact hscore PUnit.unit
  | cons r ds ih =>
    apply layerAverage_range
    intro b
    exact ih (fun bs => score (b, bs)) (fun bs => hscore (b, bs)) j.2

private theorem layerAverage_mono {r : ℕ} {f g : Causes r → ℝ}
    (hfg : ∀ b, f b ≤ g b) (j : Fin (r + 1)) :
    layerAverage id f j ≤ layerAverage id g j := by
  classical
  unfold layerAverage
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun b _ => hfg b.val)
    (Nat.cast_nonneg _)

/-- Pointwise comparison of scores is preserved in every tensor coefficient. -/
theorem layerCoefficients_mono (ds : List ℕ) {f g : CausesGrid ds → ℝ}
    (hfg : ∀ b, f b ≤ g b) (j : Grid ds) :
    layerCoefficients ds f j ≤ layerCoefficients ds g j := by
  induction ds with
  | nil => exact hfg PUnit.unit
  | cons r ds ih =>
    apply layerAverage_mono
    intro b
    exact ih (fun bs => hfg (b, bs)) j.2

/-- Decreasing scores under addition of causes give an antitone coefficient array. -/
theorem layerCoefficients_antitone (ds : List ℕ) (score : CausesGrid ds → ℝ)
    (hscore : Antitone score) : Antitone (layerCoefficients ds score) := by
  induction ds with
  | nil => intro i j hij; exact le_rfl
  | cons r ds ih =>
    intro i j hij
    have htail (b : Causes r) :
        Antitone (layerCoefficients ds (fun bs => score (b, bs))) := by
      apply ih
      intro a c hac
      exact hscore (show (b, a) ≤ (b, c) from ⟨le_rfl, hac⟩)
    have hhead : Antitone (layerAverage (id : Causes r → Causes r)
        (fun b => layerCoefficients ds (fun bs => score (b, bs)) i.2)) := by
      apply layerAverage_antitone
      intro a b hab
      apply layerCoefficients_mono
      intro bs
      exact hscore (show (a, bs) ≤ (b, bs) from ⟨hab, le_rfl⟩)
    exact le_trans (layerAverage_mono (fun b => htail b hij.2) j.1) (hhead hij.1)

/-- An arbitrary observation map may identify any number of latent causes. -/
def latentExpectation {ds : List ℕ} {E : Type*} (C : CausesGrid ds → E)
    (score : E → ℝ) (p : Params ds) : ℝ :=
  expectation ds (fun b => score (C b)) p

def observedCoefficients {ds : List ℕ} {E : Type*} (C : CausesGrid ds → E)
    (score : E → ℝ) : Grid ds → ℝ :=
  layerCoefficients ds (fun b => score (C b))

theorem latentExpectation_eq_tensor {ds : List ℕ} {E : Type*}
    (C : CausesGrid ds → E) (score : E → ℝ) (p : Params ds) :
    latentExpectation C score p = curve ds (observedCoefficients C score) p :=
  expectation_eq_tensor ds (fun b => score (C b)) p

theorem observedCoefficients_range {ds : List ℕ} {E : Type*}
    (C : CausesGrid ds → E) (score : E → ℝ)
    (hscore : ∀ e, 0 ≤ score e ∧ score e ≤ 1) (j : Grid ds) :
    0 ≤ observedCoefficients C score j ∧ observedCoefficients C score j ≤ 1 :=
  layerCoefficients_range ds _ (fun b => hscore (C b)) j

theorem observedCoefficients_antitone {ds : List ℕ} {E : Type*}
    (C : CausesGrid ds → E) (score : E → ℝ)
    (hscore : Antitone (fun b => score (C b))) :
    Antitone (observedCoefficients C score) :=
  layerCoefficients_antitone ds _ hscore

theorem latentExpectation_range {ds : List ℕ} {E : Type*}
    (C : CausesGrid ds → E) (score : E → ℝ)
    (hscore : ∀ e, 0 ≤ score e ∧ score e ≤ 1) (p : Params ds) (hp : cube ds p) :
    0 ≤ latentExpectation C score p ∧ latentExpectation C score p ≤ 1 := by
  rw [latentExpectation_eq_tensor]
  exact curve_range ds _ (observedCoefficients_range C score hscore) p hp

theorem latentExpectation_antitone {ds : List ℕ} {E : Type*}
    (C : CausesGrid ds → E) (score : E → ℝ)
    (hscore : Antitone (fun b => score (C b))) :
    AntitoneOn (latentExpectation C score) {p | cube ds p} := by
  intro p hp q hq hpq
  rw [latentExpectation_eq_tensor, latentExpectation_eq_tensor]
  exact curve_antitone ds _ (observedCoefficients_antitone C score hscore) hp hq hpq

end QecReliability.TensorLatent
