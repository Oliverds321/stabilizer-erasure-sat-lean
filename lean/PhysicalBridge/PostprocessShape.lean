import PhysicalBridge.PhysicalAlgorithm

/-! Deterministic postprocessing. Structural shape requires ordered endpoints;
accuracy of running-minimum repair requires antitone true coefficients. -/
noncomputable section
namespace QecReliability

theorem layerAverage_fin_zero {r : ℕ} {E : Type*} (C : Causes r → E) (f : E → ℝ) :
    layerAverage C f 0 = f (C ∅) := layerAverage_zero C f

theorem layerAverage_fin_last {r : ℕ} {E : Type*} (C : Causes r → E) (f : E → ℝ) :
    layerAverage C f (Fin.last r) = f (C Finset.univ) := layerAverage_last C f

def endpointInput {r : ℕ} (a ell : ℝ) (g : Fin (r+1) → ℝ) (j : ℕ) : ℝ :=
  if j=0 then a else if j=r then ell else extendCoefficients g j

theorem shapeInput_eq_endpointInput {r : ℕ} (f g : Fin (r+1) → ℝ) :
    shapeInput f g = endpointInput (f 0) (f (Fin.last r)) g := rfl

def endpointCoefficients {r : ℕ} (f g : Fin (r+1) → ℝ) (j : Fin (r+1)) : ℝ :=
  shapeInput f g j.val

theorem endpointCoefficients_range {r : ℕ} (f g : Fin (r+1) → ℝ)
    (hf : ∀ j, 0≤f j ∧ f j≤1) (hg : ∀ j, 0≤g j ∧ g j≤1) :
    ∀ j, 0≤endpointCoefficients f g j ∧ endpointCoefficients f g j≤1 := by
  intro j
  unfold endpointCoefficients shapeInput
  split_ifs
  · exact hf _
  · exact hf _
  · simpa only [extendCoefficients_at] using hg j

theorem endpointCurve_structural {r : ℕ} (f g : Fin (r+1) → ℝ)
    (hf : ∀ j, 0≤f j ∧ f j≤1) (hg : ∀ j, 0≤g j ∧ g j≤1) :
    bernsteinCurve r (endpointCoefficients f g) 0 = f 0 ∧
    bernsteinCurve r (endpointCoefficients f g) 1 = f (Fin.last r) ∧
    ∀ p ∈ Set.Icc (0:ℝ) 1,
      0≤bernsteinCurve r (endpointCoefficients f g) p ∧
      bernsteinCurve r (endpointCoefficients f g) p≤1 := by
  refine ⟨(bernsteinCurve_zero _ _).trans (shapeInput_endpoints f g).1,
    (bernsteinCurve_one _ _).trans (shapeInput_endpoints f g).2, ?_⟩
  intro p hp
  exact bernsteinCurve_range hp.1 hp.2 (endpointCoefficients_range f g hf hg)

theorem endpointCurve_relPair {r : ℕ} {ε : ℝ} (f g : Fin (r+1) → ℝ)
    (hε : 0≤ε) (hf : ∀ j, 0≤f j ∧ f j≤1) (hfg : ∀ j, RelPair ε (f j) (g j)) :
    ∀ p ∈ Set.Icc (0:ℝ) 1,
      RelPair ε (bernsteinCurve r f p) (bernsteinCurve r (endpointCoefficients f g) p) := by
  intro p hp
  apply bernsteinCurve_relPair hp.1 hp.2
  intro j
  simpa only [endpointCoefficients, extendCoefficients_at] using
    shapeInput_relPair f g hε hf hfg j.val (Nat.le_of_lt_succ j.isLt)

/-- No accuracy or coefficient-monotonicity hypothesis is needed for structure. -/
theorem shapeCurve_structural {r : ℕ} (f g : Fin (r+1) → ℝ)
    (horder : f (Fin.last r)≤f 0) (hl : 0≤f (Fin.last r)) (ha : f 0≤1) :
    AntitoneOn (bernsteinCurve r (shapeCoefficients f g)) (Set.Icc 0 1) ∧
    bernsteinCurve r (shapeCoefficients f g) 0 = f 0 ∧
    bernsteinCurve r (shapeCoefficients f g) 1 = f (Fin.last r) ∧
    ∀ p ∈ Set.Icc (0:ℝ) 1,
      f (Fin.last r)≤bernsteinCurve r (shapeCoefficients f g) p ∧
      bernsteinCurve r (shapeCoefficients f g) p≤f 0 ∧
      0≤bernsteinCurve r (shapeCoefficients f g) p ∧
      bernsteinCurve r (shapeCoefficients f g) p≤1 := by
  have hm := bernsteinCurve_antitone _ (shapeCoefficients_antitone f g)
  have he := repaired_endpoints horder (shapeInput_endpoints f g).1 (shapeInput_endpoints f g).2
  have hz : bernsteinCurve r (shapeCoefficients f g) 0=f 0 := (bernsteinCurve_zero _ _).trans he.1
  have ho : bernsteinCurve r (shapeCoefficients f g) 1=f (Fin.last r) := (bernsteinCurve_one _ _).trans he.2
  refine ⟨hm,hz,ho,?_⟩
  intro p hp
  have hlo := hm hp (show (1:ℝ) ∈ Set.Icc 0 1 by norm_num) hp.2
  have hhi := hm (show (0:ℝ) ∈ Set.Icc 0 1 by norm_num) hp hp.1
  rw [ho] at hlo
  rw [hz] at hhi
  exact ⟨hlo,hhi,hl.trans hlo,hhi.trans ha⟩

theorem shapeCoefficients_only_endpoints {r : ℕ} (f f' g : Fin (r+1) → ℝ)
    (h0 : f 0=f' 0) (hr : f (Fin.last r)=f' (Fin.last r)) :
    shapeCoefficients f g = shapeCoefficients f' g := by
  unfold shapeCoefficients
  have hh : f ⟨r,Nat.lt_succ_self r⟩ = f' ⟨r,Nat.lt_succ_self r⟩ := hr
  simp only [shapeInput_eq_endpointInput, h0, hr, hh]

end QecReliability
