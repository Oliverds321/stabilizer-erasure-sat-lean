import QecReliability.BernsteinShape
import QecReliability.Averaging

/-! Tensor Bernstein curves for any finite list of degrees. Coordinates use
the product order. Empty lists and degree-zero coordinates require no special
assumptions. This module states mathematical curve properties only. -/

namespace QecReliability.TensorBernstein

open scoped BigOperators

/-- One coefficient index for each degree. -/
def Grid : List ℕ → Type
  | [] => PUnit
  | r :: ds => Fin (r + 1) × Grid ds

/-- One real parameter for each degree. -/
def Params : List ℕ → Type
  | [] => PUnit
  | _ :: ds => ℝ × Params ds

instance gridFintype : (ds : List ℕ) → Fintype (Grid ds)
  | [] => inferInstanceAs (Fintype PUnit)
  | r :: ds =>
    letI := gridFintype ds
    inferInstanceAs (Fintype (Fin (r + 1) × Grid ds))

instance gridPartialOrder : (ds : List ℕ) → PartialOrder (Grid ds)
  | [] => inferInstanceAs (PartialOrder PUnit)
  | r :: ds =>
    letI := gridPartialOrder ds
    inferInstanceAs (PartialOrder (Fin (r + 1) × Grid ds))

instance paramsPreorder : (ds : List ℕ) → Preorder (Params ds)
  | [] => inferInstanceAs (Preorder PUnit)
  | _ :: ds =>
    letI := paramsPreorder ds
    inferInstanceAs (Preorder (ℝ × Params ds))

/-- The closed parameter cube, including the unique empty tuple. -/
def cube : (ds : List ℕ) → Params ds → Prop
  | [], _ => True
  | _ :: ds, p => p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ cube ds p.2

@[simp] theorem cube_nil (p : Params []) : cube [] p := trivial

@[simp] theorem cube_cons (r : ℕ) (ds : List ℕ) (p : ℝ) (ps : Params ds) :
    cube (r :: ds) (p, ps) ↔ p ∈ Set.Icc (0 : ℝ) 1 ∧ cube ds ps := Iff.rfl

/-- Iterated Bernstein averaging of the coefficient array. -/
noncomputable def curve : (ds : List ℕ) → (Grid ds → ℝ) → Params ds → ℝ
  | [], f, _ => f PUnit.unit
  | r :: ds, f, p =>
    bernsteinCurve r (fun j => curve ds (fun k => f (j, k)) p.2) p.1

@[simp] theorem curve_nil (f : Grid [] → ℝ) (p : Params []) :
    curve [] f p = f PUnit.unit := rfl

@[simp] theorem curve_cons (r : ℕ) (ds : List ℕ) (f : Grid (r :: ds) → ℝ)
    (p : ℝ) (ps : Params ds) :
    curve (r :: ds) f (p, ps) =
      bernsteinCurve r (fun j => curve ds (fun k => f (j, k)) ps) p := rfl

/-- Coefficientwise comparison is preserved throughout the cube. -/
theorem curve_mono (ds : List ℕ) {f g : Grid ds → ℝ}
    (hfg : ∀ k, f k ≤ g k) {p : Params ds} (hp : cube ds p) :
    curve ds f p ≤ curve ds g p := by
  induction ds with
  | nil => exact hfg PUnit.unit
  | cons r ds ih =>
    apply average_mono (bernsteinWeight_nonneg hp.1.1 hp.1.2)
    intro j
    exact ih (f := fun k => f (j, k)) (g := fun k => g (j, k))
      (p := p.2) (fun k => hfg (j, k)) hp.2

/-- Coefficients in the unit interval give values in the unit interval. -/
theorem curve_range (ds : List ℕ) (f : Grid ds → ℝ)
    (hf : ∀ k, 0 ≤ f k ∧ f k ≤ 1) (p : Params ds) (hp : cube ds p) :
    0 ≤ curve ds f p ∧ curve ds f p ≤ 1 := by
  induction ds with
  | nil => exact hf PUnit.unit
  | cons r ds ih =>
    apply bernsteinCurve_range hp.1.1 hp.1.2
    intro j
    exact ih (fun k => f (j, k)) (fun k => hf (j, k)) p.2 hp.2

/-- One simultaneous coefficient event for both relative tails. -/
def pointwiseRelPair {ds : List ℕ} (ε : ℝ) (f g : Grid ds → ℝ) : Prop :=
  ∀ k, RelPair ε (f k) (g k)

/-- The same coefficient event controls every point of the closed cube. -/
theorem curve_relPair (ds : List ℕ) {ε : ℝ} {f g : Grid ds → ℝ}
    (hfg : pointwiseRelPair ε f g) :
    ∀ p : Params ds, cube ds p → RelPair ε (curve ds f p) (curve ds g p) := by
  induction ds with
  | nil => intro p hp; exact hfg PUnit.unit
  | cons r ds ih =>
    intro p hp
    apply bernsteinCurve_relPair hp.1.1 hp.1.2
    intro j
    exact ih (f := fun k => f (j, k)) (g := fun k => g (j, k))
      (fun k => hfg (j, k)) p.2 hp.2

/-- Tensor averaging commutes with any finite weighted average. No sign or
normalization hypotheses on the additional weights are needed. -/
theorem curve_average (ds : List ℕ) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (f : ι → Grid ds → ℝ) (p : Params ds) :
    curve ds (fun k => average w (fun i => f i k)) p =
      average w (fun i => curve ds (f i) p) := by
  induction ds with
  | nil => rfl
  | cons r ds ih =>
    simp only [curve]
    simp_rw [ih]
    simp only [bernsteinCurve, average, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Antitone arrays give curves antitone in the product order on the cube. -/
theorem curve_antitone (ds : List ℕ) (f : Grid ds → ℝ) (hf : Antitone f) :
    AntitoneOn (curve ds f) {p | cube ds p} := by
  induction ds with
  | nil => intro p hp q hq hpq; exact le_rfl
  | cons r ds ih =>
    intro p hp q hq hpq
    have hslices (j : Fin (r + 1)) : Antitone (fun k : Grid ds => f (j, k)) := by
      intro k l hkl
      exact hf (show (j, k) ≤ (j, l) from ⟨le_rfl, hkl⟩)
    have hhead : Antitone (fun j : Fin (r + 1) =>
        curve ds (fun k => f (j, k)) p.2) := by
      intro i j hij
      exact curve_mono ds (fun k => hf (show (i, k) ≤ (j, k) from ⟨hij, le_rfl⟩)) hp.2
    calc
      curve (r :: ds) f q ≤
          bernsteinCurve r (fun j => curve ds (fun k => f (j, k)) p.2) q.1 := by
        apply average_mono (bernsteinWeight_nonneg hq.1.1 hq.1.2)
        intro j
        exact ih (fun k => f (j, k)) (hslices j) hp.2 hq.2 hpq.2
      _ ≤ curve (r :: ds) f p :=
        bernsteinCurve_antitone _ hhead hp.1 hq.1 hpq.1

/-- A Boolean endpoint choice in each coordinate. -/
def Corner : List ℕ → Type
  | [] => PUnit
  | _ :: ds => Bool × Corner ds

def cornerParams : (ds : List ℕ) → Corner ds → Params ds
  | [], _ => PUnit.unit
  | _ :: ds, b => (if b.1 then 1 else 0, cornerParams ds b.2)

def cornerIndex : (ds : List ℕ) → Corner ds → Grid ds
  | [], _ => PUnit.unit
  | r :: ds, b =>
    (if b.1 then ⟨r, Nat.lt_succ_self r⟩ else ⟨0, Nat.zero_lt_succ r⟩,
      cornerIndex ds b.2)

theorem cornerParams_mem_cube (ds : List ℕ) (b : Corner ds) :
    cube ds (cornerParams ds b) := by
  induction ds with
  | nil => trivial
  | cons r ds ih =>
    rcases b with ⟨b, bs⟩
    cases b <;> exact ⟨by norm_num [cornerParams], ih bs⟩

/-- Every tensor corner is exactly its coefficient, including repeated corner
indices caused by degree-zero coordinates. -/
theorem curve_corner (ds : List ℕ) (f : Grid ds → ℝ) (b : Corner ds) :
    curve ds f (cornerParams ds b) = f (cornerIndex ds b) := by
  induction ds with
  | nil => rfl
  | cons r ds ih =>
    rcases b with ⟨b, bs⟩
    cases b with
    | false =>
      change bernsteinCurve r (fun j => curve ds (fun k => f (j, k))
        (cornerParams ds bs)) 0 = f (⟨0, Nat.zero_lt_succ r⟩, cornerIndex ds bs)
      rw [bernsteinCurve_zero]
      exact ih _ bs
    | true =>
      change bernsteinCurve r (fun j => curve ds (fun k => f (j, k))
        (cornerParams ds bs)) 1 = f (⟨r, Nat.lt_succ_self r⟩, cornerIndex ds bs)
      rw [bernsteinCurve_one]
      exact ih _ bs

end QecReliability.TensorBernstein
