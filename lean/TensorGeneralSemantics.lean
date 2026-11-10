import PhysicalBridge.RationalTensorConfidence

/-! Multiclass reliability estimation for a GENERAL (not necessarily monotone)
observation map: no shape repair is applied. The corner coefficients of the
estimated table are replaced by their exact dyadic physical scores, and every
other coefficient is the normalized cached count estimate. For every seed the
table lies in `[0,1]`, has exact corners and identifies the coefficients equal
to one exactly; one finite seed event gives two-tail relative accuracy of the
tensor curve on the whole parameter cube. No monotonicity hypothesis appears.
This is the source-level (semantic) algorithm; it makes no machine claim. -/
set_option autoImplicit false
noncomputable section

namespace QecReliability.TensorGeneral
open Binary TensorBernstein TensorLatent TensorCoefficientCounting RationalOutput
open QecPhysical QecPhysical.Stabilizer

/-! ## Exactness of the coefficient one for the cached ratio estimates -/
section Counting
variable {Ω : Type*} [Fintype Ω] {n : ℕ} {ds : List ℕ}
  {S : Submodule Bit (Pauli n)} {C : CausesGrid ds → Finset (Fin n)}
  {H : HashStages Ω (Key n ds) (SharedCircuit.LatentEncoding.keySize n ds.sum)}

theorem amplified_nonneg (O : ∀ i, ExactTrialOracle H (coefficientModels S C i)) (B m : ℕ)
    (ω : Fin (2*m+1) → Ω) (i : Index ds) : 0 ≤ ExactTrialOracle.amplified O B m ω i := by
  unfold ExactTrialOracle.amplified medianEstimate oddMedian
  exact Nat.cast_nonneg _

theorem amplified_eq_zero_iff (O : ∀ i, ExactTrialOracle H (coefficientModels S C i))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) (i : Index ds) :
    ExactTrialOracle.amplified O B m ω i = 0 ↔ (coefficientModels S C i).card = 0 := by
  rw [Finset.card_eq_zero]
  constructor
  · intro hz
    by_contra hn
    have hp := ExactTrialOracle.amplified_positive O B m ω i
      (Finset.nonempty_iff_ne_empty.mpr hn)
    linarith
  · exact ExactTrialOracle.amplified_zero O B m ω i

/-- On every seed, the estimated ratio is one iff the true coefficient is one. -/
theorem estimates_eq_one_iff (hS : S ≤ normalizer (F := Bit) (symplectic n) S)
    (O : ∀ i, ExactTrialOracle H (coefficientModels S C i))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) (j : Grid ds) :
    estimates O B m ω j = 1 ↔ observedCoefficients C (score S) j = 1 := by
  rw [← coefficient_normalized S hS C j]
  have hcg : (coefficientModels S C (true,j)).card = goodCoefficient S C j := by
    simp only [TensorCoefficientCounting.coefficientModels_card, ↓reduceIte]
  have hcb : (coefficientModels S C (false,j)).card = badCoefficient S C j := by
    simp only [TensorCoefficientCounting.coefficientModels_card, Bool.false_eq_true, ↓reduceIte]
  have hsum := coefficient_total_pos S C j
  have hg0 := amplified_nonneg O B m ω (true,j)
  unfold estimates
  set g := ExactTrialOracle.amplified O B m ω (true,j)
  set b := ExactTrialOracle.amplified O B m ω (false,j)
  rw [div_eq_one_iff_eq hsum.ne']
  by_cases hD : badCoefficient S C j = 0
  · have hb : b = 0 := (amplified_eq_zero_iff O B m ω (false,j)).mpr (hcb.trans hD)
    have hG : goodCoefficient S C j ≠ 0 := by
      intro hG
      rw [hG, hD] at hsum
      simp at hsum
    have hgpos : g ≠ 0 := by
      intro hg
      exact hG (hcg.symm.trans ((amplified_eq_zero_iff O B m ω (true,j)).mp hg))
    rw [hb, add_zero, div_self hgpos, hD]
    simp
  · have hbpos : 0 < b := lt_of_le_of_ne (amplified_nonneg O B m ω (false,j))
      (fun e => hD (hcb.symm.trans ((amplified_eq_zero_iff O B m ω (false,j)).mp e.symm)))
    have hDpos : (0:ℝ) < badCoefficient S C j := by exact_mod_cast Nat.pos_of_ne_zero hD
    constructor
    · intro h
      have hlt : g / (g + b) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
      rw [h] at hlt
      exact absurd hlt (lt_irrefl _)
    · intro h
      linarith

end Counting

/-! ## Corner replacement, rational and real -/
section Replacement
variable {n : ℕ} (ds : List ℕ) (rows : List (List (SharedCircuit.PauliCoord n)))
  (C : CausesGrid ds → Finset (Fin n))

/-- Executable corner replacement: an exact dyadic physical score at every corner
(each class all-zero or all-one), the supplied estimate elsewhere. -/
def cornerCoefficient (est : Grid ds → Ratio) (j : Grid ds) : Ratio :=
  if RationalTensorRepair.cornerTest ds j then RationalTensorRepair.dyadicAnchor ds rows C j
  else est j

/-- The flat output table, in the enumeration order of the repaired machine output. -/
def cornerPrepare (est : Grid ds → Ratio) : List Ratio :=
  (RationalTensorRepair.enum ds).map (cornerCoefficient ds rows C est)

theorem cornerPrepare_length (est : Grid ds → Ratio) :
    (cornerPrepare ds rows C est).length = (ds.map (fun r => r+1)).prod := by
  rw [cornerPrepare, List.length_map, RationalTensorRepair.enum_length]

theorem cornerCoefficient_corner (est : Grid ds → Ratio) (b : Corner ds) :
    (cornerCoefficient ds rows C est (cornerIndex ds b)).value =
      multivariateCoefficients (SharedCircuit.rowSpace rows) C (cornerIndex ds b) := by
  have ht : RationalTensorRepair.cornerTest ds (cornerIndex ds b) = true :=
    (RationalTensorRepair.cornerTest_iff ds _).mpr ⟨b, rfl⟩
  simp only [cornerCoefficient, ht, ↓reduceIte]
  rw [RationalTensorRepair.dyadicAnchor_value]
  exact physicalCornerAnchorValues_exact _ C _ (MultivariateShapeRepair.cornerIndex_mem ds b)

theorem cornerCoefficient_corner_score (est : Grid ds → Ratio) (b : Corner ds) :
    (cornerCoefficient ds rows C est (cornerIndex ds b)).value =
      erasureScore (SharedCircuit.rowSpace rows) (C (cornerCauses ds b)) := by
  have ht : RationalTensorRepair.cornerTest ds (cornerIndex ds b) = true :=
    (RationalTensorRepair.cornerTest_iff ds _).mpr ⟨b, rfl⟩
  simp only [cornerCoefficient, ht, ↓reduceIte]
  rw [RationalTensorRepair.dyadicAnchor_value]
  simp only [physicalCornerAnchorValues, canonicalCauses_corner]

theorem cornerCoefficient_other (est : Grid ds → Ratio) (j : Grid ds)
    (hj : RationalTensorRepair.cornerTest ds j = false) :
    cornerCoefficient ds rows C est j = est j := by
  rw [cornerCoefficient, hj]
  rfl

/-- Every value of the corner-replaced table is either an exact coefficient
(at a corner) or the supplied estimate (elsewhere). -/
theorem cornerCoefficient_cases (est : Grid ds → Ratio) (j : Grid ds) :
    (cornerCoefficient ds rows C est j).value =
        multivariateCoefficients (SharedCircuit.rowSpace rows) C j ∨
      (RationalTensorRepair.cornerTest ds j = false ∧
        (cornerCoefficient ds rows C est j).value = (est j).value) := by
  cases ht : RationalTensorRepair.cornerTest ds j with
  | true =>
    obtain ⟨b, rfl⟩ := (RationalTensorRepair.cornerTest_iff ds j).mp ht
    exact Or.inl (cornerCoefficient_corner ds rows C est b)
  | false =>
    exact Or.inr ⟨rfl, by rw [cornerCoefficient_other ds rows C est j ht]⟩

/-- Pure mathematical content of corner replacement: if every estimate is
`ε`-accurate in both tails, so is the replaced table (exact corners are
trivially accurate). No order or monotonicity hypothesis. -/
theorem cornerCoefficient_relPair (est : Grid ds → Ratio) {ε : ℝ} (hε : 0 ≤ ε)
    (hpair : ∀ j, RelPair ε (multivariateCoefficients (SharedCircuit.rowSpace rows) C j)
      (est j).value) (j : Grid ds) :
    RelPair ε (multivariateCoefficients (SharedCircuit.rowSpace rows) C j)
      (cornerCoefficient ds rows C est j).value := by
  rcases cornerCoefficient_cases ds rows C est j with h | ⟨_, h⟩
  · rw [h]
    exact relPair_refl hε (multivariateCoefficients_range _ C j).1
      (multivariateCoefficients_range _ C j).2
  · rw [h]
    exact hpair j

end Replacement

/-! ## The general-circuit estimator built from cached counting queries -/
section Estimator
variable {Ω : Type*} [Fintype Ω] {n : ℕ} {ds : List ℕ}
  {H : HashStages Ω (Key n ds) (SharedCircuit.LatentEncoding.keySize n ds.sum)}
  (rows : List (List (SharedCircuit.PauliCoord n)))
  (C : CausesGrid ds → Finset (Fin n))

/-- Executable output: corner-replaced estimate ratios, no shape repair. -/
def output
    (D : ∀ i, DecisionQueries (keyBits n ds) H
      (coefficientModels (SharedCircuit.rowSpace rows) C i))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) : List Ratio :=
  cornerPrepare ds rows C (RationalTensorConfidence.estimateRatios D B m ω)

/-- The coefficient table of the output, in grid coordinates. -/
def table
    (D : ∀ i, DecisionQueries (keyBits n ds) H
      (coefficientModels (SharedCircuit.rowSpace rows) C i))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) : Grid ds → ℝ :=
  fun j => (cornerCoefficient ds rows C (RationalTensorConfidence.estimateRatios D B m ω) j).value

def outputCurve
    (D : ∀ i, DecisionQueries (keyBits n ds) H
      (coefficientModels (SharedCircuit.rowSpace rows) C i))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) : Params ds → ℝ :=
  curve ds (table rows C D B m ω)

theorem output_length
    (D : ∀ i, DecisionQueries (keyBits n ds) H
      (coefficientModels (SharedCircuit.rowSpace rows) C i))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) :
    (output rows C D B m ω).length = (ds.map (fun r => r+1)).prod :=
  cornerPrepare_length ds rows C _

theorem output_eq_map
    (D : ∀ i, DecisionQueries (keyBits n ds) H
      (coefficientModels (SharedCircuit.rowSpace rows) C i))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) :
    (output rows C D B m ω).map Ratio.value =
      (RationalTensorRepair.enum ds).map (table rows C D B m ω) := by
  simp only [output, cornerPrepare, List.map_map]
  rfl

/-- Deterministic structure of the table on every seed, for an arbitrary
observation map: unit range, exact corners, exact unit coefficients. -/
theorem table_structure (L : Lift (SharedCircuit.rowSpace rows))
    (D : ∀ i, DecisionQueries (keyBits n ds) H
      (coefficientModels (SharedCircuit.rowSpace rows) C i))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) :
    let g := table rows C D B m ω
    let f := multivariateCoefficients (SharedCircuit.rowSpace rows) C
    (∀ j, 0 ≤ g j ∧ g j ≤ 1) ∧
    (∀ b : Corner ds, g (cornerIndex ds b) = f (cornerIndex ds b) ∧
      g (cornerIndex ds b) = erasureScore (SharedCircuit.rowSpace rows) (C (cornerCauses ds b))) ∧
    (∀ j, g j = 1 ↔ f j = 1) := by
  intro g f
  refine ⟨fun j => Ratio.value_range _, fun b => ⟨cornerCoefficient_corner ds rows C _ b,
    cornerCoefficient_corner_score ds rows C _ b⟩, fun j => ?_⟩
  rcases cornerCoefficient_cases ds rows C
      (RationalTensorConfidence.estimateRatios D B m ω) j with h | ⟨_, h⟩
  · change (cornerCoefficient ds rows C _ j).value = 1 ↔ _
    rw [h]
  · change (cornerCoefficient ds rows C _ j).value = 1 ↔ _
    rw [h, RationalTensorConfidence.estimateRatios_value]
    exact estimates_eq_one_iff L.isotropic _ B m ω j

/-- General-circuit structure of a curve: unit range on the cube and exact
physical values at every corner (no antitonicity). -/
def GeneralStructure (L : Lift (SharedCircuit.rowSpace rows)) (g : Params ds → ℝ) : Prop :=
  (∀ p, cube ds p → 0 ≤ g p ∧ g p ≤ 1) ∧
  ∀ b : Corner ds, g (cornerParams ds b) =
    entanglementFidelity
      (L.erasureFlagDecoder.comp (L.multivariateLatentErasure C (cornerParams ds b)
        (cornerParams_mem_cube ds b))).map

theorem curve_structure (L : Lift (SharedCircuit.rowSpace rows))
    (D : ∀ i, DecisionQueries (keyBits n ds) H
      (coefficientModels (SharedCircuit.rowSpace rows) C i))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) :
    GeneralStructure rows C L (outputCurve rows C D B m ω) := by
  obtain ⟨hr, hc, _⟩ := table_structure rows C L D B m ω
  refine ⟨fun p hp => curve_range ds _ hr p hp, fun b => ?_⟩
  rw [(L.multivariateLatentErasure_optimum C _ (cornerParams_mem_cube ds b)).1,
    outputCurve, curve_corner, curve_corner]
  exact (hc b).1

/-- One finite-seed event gives two-tail relative accuracy of the output curve
at every point of the parameter cube, for an arbitrary observation map. -/
theorem output_physical_confidence (L : Lift (SharedCircuit.rowSpace rows))
    (D : ∀ i, DecisionQueries (keyBits n ds) H
      (coefficientModels (SharedCircuit.rowSpace rows) C i))
    (B m : ℕ) (hB : 0 < B) {ε δ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hcell : 16 ≤ (ε/3)^2*(B:ℝ))
    (hrepeat : (Fintype.card (Index ds):ℝ)*(1/2:ℝ)^(m+2) ≤ δ) :
    1-δ ≤ (repeatedLaw H.law m).prob (fun ω =>
      L.TensorPhysicalAccuracy C ε (outputCurve rows C D B m ω)) := by
  apply (coefficients_confidence (SharedCircuit.rowSpace rows) L.isotropic C H
    (fun i => (D i).toTrialOracle) B m hB hε hε1 hcell hrepeat).trans
  apply FiniteProbability.prob_mono
  intro ω hω p hp
  rw [(L.multivariateLatentErasure_optimum C p hp).1]
  apply curve_relPair ds _ p hp
  intro j
  apply cornerCoefficient_relPair ds rows C _ hε.le
  intro i
  rw [RationalTensorConfidence.estimateRatios_value]
  exact (hω i).1

end Estimator
end QecReliability.TensorGeneral

#print axioms QecReliability.TensorGeneral.table_structure
#print axioms QecReliability.TensorGeneral.curve_structure
#print axioms QecReliability.TensorGeneral.output_physical_confidence
