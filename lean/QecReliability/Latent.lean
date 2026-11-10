import QecReliability.Averaging
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finite.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
Finite latent causes and positive Bernstein aggregation.
The deterministic map `C` is arbitrary and may be many-to-one.
These theorems do not assert correctness or size of a Boolean circuit encoding.
-/

noncomputable section

namespace QecReliability

open scoped BigOperators

/-- Aggregation retains every cause, including causes with the same observed output. -/
theorem latent_grouping {B E J : Type*} [Fintype B] [Fintype J] [DecidableEq J]
    (C : B → E) (layer : B → J) (w : J → ℝ) (f : E → ℝ) :
    (∑ b, w (layer b) * f (C b)) =
      ∑ j, w j * ∑ b : {b // layer b = j}, f (C b) := by
  rw [← Fintype.sum_fiberwise layer (fun b => w (layer b) * f (C b))]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [b.property]

theorem latent_output_grouping {B E : Type*} [Fintype B] [Fintype E] [DecidableEq E]
    (C : B → E) (mass : B → ℝ) (f : E → ℝ) :
    (∑ b, mass b * f (C b)) =
      ∑ e, (∑ b : {b // C b = e}, mass b) * f e := by
  rw [← Fintype.sum_fiberwise C (fun b => mass b * f (C b))]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [b.property]

theorem finite_predicate_partition {X : Type*} [Finite X] (P Q : X → Prop)
    (h : ∀ x, Q x ↔ ¬ P x) : Nat.card {x // P x} + Nat.card {x // Q x} = Nat.card X := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight h), ← Nat.card_sum]
  exact Nat.card_congr (Equiv.sumCompl P)

/-- Projecting onto `(cause,z)` gives one contribution for each cause, not each image of `C`. -/
theorem latent_pair_partition {B E Z J : Type*} [Finite B] [Finite Z]
    (C : B → E) (layer : B → J) (j : J) (P Q : E → Z → Prop)
    (h : ∀ e z, Q e z ↔ ¬ P e z) :
    Nat.card {bz : {b // layer b = j} × Z // P (C bz.1) bz.2} +
      Nat.card {bz : {b // layer b = j} × Z // Q (C bz.1) bz.2} =
      Nat.card {b // layer b = j} * Nat.card Z := by
  have hh := finite_predicate_partition
    (fun bz : {b // layer b = j} × Z => P (C bz.1) bz.2)
    (fun bz : {b // layer b = j} × Z => Q (C bz.1) bz.2)
    (fun bz => h (C bz.1) bz.2)
  simpa only [Nat.card_prod] using hh

theorem pair_predicate_card {B Z : Type*} [Fintype B] [Finite Z] (P : B → Z → Prop) :
    Nat.card {bz : B × Z // P bz.1 bz.2} = ∑ b, Nat.card {z // P b z} := by
  let e : {bz : B × Z // P bz.1 bz.2} ≃ (Σ b : B, {z // P b z}) :=
    { toFun := fun bz => ⟨bz.1.1, ⟨bz.1.2, bz.2⟩⟩
      invFun := fun bz => ⟨(bz.1, bz.2.1), bz.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_sigma]

abbrev Causes (r : ℕ) := Finset (Fin r)

def hammingLayer {r : ℕ} (b : Causes r) : Fin (r + 1) :=
  ⟨b.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ b)⟩

theorem hamming_layer_card (r : ℕ) (j : Fin (r + 1)) :
    Nat.card {b : Causes r // hammingLayer b = j} = r.choose j.val := by
  classical
  rw [Nat.card_eq_fintype_card]
  have he : ∀ b : Causes r,
      b ∈ Finset.powersetCard j.val Finset.univ ↔ hammingLayer b = j := by
    intro b
    simp [Finset.mem_powersetCard, hammingLayer, Fin.ext_iff]
  rw [Fintype.card_of_subtype _ he, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin]

def bernsteinWeight (r : ℕ) (p : ℝ) (j : Fin (r + 1)) : ℝ :=
  (r.choose j.val : ℝ) * p ^ j.val * (1 - p) ^ (r - j.val)

theorem bernsteinWeight_nonneg {r : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (j : Fin (r + 1)) : 0 ≤ bernsteinWeight r p j := by
  unfold bernsteinWeight
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _))
    (pow_nonneg (sub_nonneg.mpr hp1) _)

theorem bernsteinWeight_sum (r : ℕ) (p : ℝ) : ∑ j, bernsteinWeight r p j = 1 := by
  unfold bernsteinWeight
  rw [Fin.sum_univ_eq_sum_range
    (fun j => (r.choose j : ℝ) * p ^ j * (1 - p) ^ (r - j)) (r + 1)]
  have h := add_pow p (1 - p) r
  have he : p + (1 - p) = 1 := by ring
  rw [he, one_pow] at h
  calc
    _ = ∑ j ∈ Finset.range (r + 1), p ^ j * (1 - p) ^ (r - j) * (r.choose j : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 1 := h.symm

def bernsteinCurve (r : ℕ) (f : Fin (r + 1) → ℝ) (p : ℝ) : ℝ :=
  average (bernsteinWeight r p) f

theorem bernsteinCurve_relPair {r : ℕ} {ε p : ℝ} {f g : Fin (r + 1) → ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hfg : ∀ j, RelPair ε (f j) (g j)) :
    RelPair ε (bernsteinCurve r f p) (bernsteinCurve r g p) :=
  relPair_average (bernsteinWeight_nonneg hp hp1) (bernsteinWeight_sum r p) hfg

theorem bernsteinCurve_complement (r : ℕ) (f : Fin (r + 1) → ℝ) (p : ℝ) :
    bernsteinCurve r (fun j => 1 - f j) p = 1 - bernsteinCurve r f p :=
  average_complement _ _ (bernsteinWeight_sum r p)

theorem bernsteinCurve_range {r : ℕ} {f : Fin (r + 1) → ℝ} {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hf : ∀ j, 0 ≤ f j ∧ f j ≤ 1) :
    0 ≤ bernsteinCurve r f p ∧ bernsteinCurve r f p ≤ 1 :=
  average_range (bernsteinWeight_nonneg hp hp1) (bernsteinWeight_sum r p) hf

theorem bernsteinCurve_zero (r : ℕ) (f : Fin (r + 1) → ℝ) :
    bernsteinCurve r f 0 = f ⟨0, Nat.zero_lt_succ r⟩ := by
  classical
  unfold bernsteinCurve average
  rw [Finset.sum_eq_single ⟨0, Nat.zero_lt_succ r⟩]
  · simp [bernsteinWeight]
  · intro j _ hj
    have hj0 : j.val ≠ 0 := by intro h; apply hj; exact Fin.ext h
    simp [bernsteinWeight, zero_pow hj0]
  · simp

theorem bernsteinCurve_one (r : ℕ) (f : Fin (r + 1) → ℝ) :
    bernsteinCurve r f 1 = f ⟨r, Nat.lt_succ_self r⟩ := by
  classical
  unfold bernsteinCurve average
  rw [Finset.sum_eq_single ⟨r, Nat.lt_succ_self r⟩]
  · simp [bernsteinWeight]
  · intro j _ hj
    have hjr : j.val ≠ r := by intro h; apply hj; exact Fin.ext h
    have hsub : r - j.val ≠ 0 := by have h := j.isLt; omega
    simp [bernsteinWeight, zero_pow hsub]
  · simp

def layerAverage {r : ℕ} {E : Type*} (C : Causes r → E) (f : E → ℝ)
    (j : Fin (r + 1)) : ℝ :=
  (∑ b : {b // hammingLayer b = j}, f (C b)) / (r.choose j.val : ℝ)

def latentCurve {r : ℕ} {E : Type*} (C : Causes r → E) (f : E → ℝ) (p : ℝ) : ℝ :=
  ∑ b, (p ^ b.card * (1 - p) ^ (r - b.card)) * f (C b)

theorem latentCurve_eq_bernstein {r : ℕ} {E : Type*} (C : Causes r → E)
    (f : E → ℝ) (p : ℝ) :
    latentCurve C f p = bernsteinCurve r (layerAverage C f) p := by
  have h := latent_grouping C hammingLayer
    (fun j => p ^ j.val * (1 - p) ^ (r - j.val)) f
  change latentCurve C f p = _ at h
  rw [h]
  unfold bernsteinCurve average
  apply Finset.sum_congr rfl
  intro j _
  have hj : 0 < (r.choose j.val : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ j.isLt)
  unfold bernsteinWeight layerAverage
  field_simp

theorem layerAverage_range {r : ℕ} {E : Type*} (C : Causes r → E) (f : E → ℝ)
    (hf : ∀ e, 0 ≤ f e ∧ f e ≤ 1) (j : Fin (r + 1)) :
    0 ≤ layerAverage C f j ∧ layerAverage C f j ≤ 1 := by
  classical
  have hj : 0 < (r.choose j.val : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ j.isLt)
  have hc : (Fintype.card {b : Causes r // hammingLayer b = j} : ℝ) = r.choose j.val := by
    exact_mod_cast (by simpa only [Nat.card_eq_fintype_card] using hamming_layer_card r j)
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun b _ => (hf (C b)).1) hj.le
  · apply (div_le_one hj).mpr
    calc
      (∑ b : {b // hammingLayer b = j}, f (C b)) ≤ ∑ _b : {b // hammingLayer b = j}, (1 : ℝ) :=
        Finset.sum_le_sum fun b _ => (hf (C b)).2
      _ = r.choose j.val := by simpa using hc

theorem layerAverage_zero {r : ℕ} {E : Type*} (C : Causes r → E) (f : E → ℝ) :
    layerAverage C f ⟨0, Nat.zero_lt_succ r⟩ = f (C ∅) := by
  classical
  let b0 : {b : Causes r // hammingLayer b = ⟨0, Nat.zero_lt_succ r⟩} :=
    ⟨∅, by simp [hammingLayer]⟩
  have huniq : ∀ b : {b : Causes r // hammingLayer b = ⟨0, Nat.zero_lt_succ r⟩}, b = b0 := by
    intro b
    apply Subtype.ext
    apply Finset.card_eq_zero.mp
    exact congrArg Fin.val b.property
  unfold layerAverage
  rw [Finset.sum_eq_single b0]
  · simp [b0]
  · intro b _ hne
    exact False.elim (hne (huniq b))
  · exact fun h => False.elim (h (Finset.mem_univ b0))

theorem layerAverage_last {r : ℕ} {E : Type*} (C : Causes r → E) (f : E → ℝ) :
    layerAverage C f ⟨r, Nat.lt_succ_self r⟩ = f (C Finset.univ) := by
  classical
  let br : {b : Causes r // hammingLayer b = ⟨r, Nat.lt_succ_self r⟩} :=
    ⟨Finset.univ, by simp [hammingLayer]⟩
  have huniq : ∀ b : {b : Causes r // hammingLayer b = ⟨r, Nat.lt_succ_self r⟩}, b = br := by
    intro b
    apply Subtype.ext
    apply Finset.eq_univ_of_card
    simpa only [hammingLayer, Fintype.card_fin] using congrArg Fin.val b.property
  unfold layerAverage
  rw [Finset.sum_eq_single br]
  · simp [br]
  · intro b _ hne
    exact False.elim (hne (huniq b))
  · exact fun h => False.elim (h (Finset.mem_univ br))

theorem latentCurve_endpoints {r : ℕ} {E : Type*} (C : Causes r → E) (f : E → ℝ) :
    latentCurve C f 0 = f (C ∅) ∧ latentCurve C f 1 = f (C Finset.univ) := by
  simp only [latentCurve_eq_bernstein, bernsteinCurve_zero, bernsteinCurve_one,
    layerAverage_zero, layerAverage_last, and_self]

/-- A direct coefficientwise theorem: the same event controls every physical parameter. -/
theorem normalized_bernstein {r : ℕ} {ε : ℝ}
    (A B Ah Bh : Fin (r + 1) → ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 < A j + B j)
    (hAh : ∀ j, |Ah j - A j| ≤ (ε / 3) * A j)
    (hBh : ∀ j, |Bh j - B j| ≤ (ε / 3) * B j) :
    ∀ p, 0 ≤ p → p ≤ 1 →
      RelPair ε (bernsteinCurve r (fun j => A j / (A j + B j)) p)
        (bernsteinCurve r (fun j => Ah j / (Ah j + Bh j)) p) ∧
      0 ≤ bernsteinCurve r (fun j => Ah j / (Ah j + Bh j)) p ∧
      bernsteinCurve r (fun j => Ah j / (Ah j + Bh j)) p ≤ 1 := by
  intro p hp hp1
  have h := fun j => normalize_counts hε hε1 (hA j) (hB j) (hT j) (hAh j) (hBh j)
  exact ⟨bernsteinCurve_relPair hp hp1 (fun j => (h j).2.2.2),
    bernsteinCurve_range hp hp1 (fun j => ⟨(h j).2.1, (h j).2.2.1⟩)⟩

end QecReliability
