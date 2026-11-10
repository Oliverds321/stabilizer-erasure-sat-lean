import PhysicalBridge.PhysicalBernstein
import PhysicalBridge.ExactEndpoints
import QecReliability.QuantumBridge
import QecReliability.TensorLatent
import QecReliability.MultivariateShapeRepair

/-!
# Physical reliability for multiple independent latent probability classes

The flag exposes only the observed erasure set. Every latent cause tuple retains
its product probability, including when several tuples have the same observed
set. The tensor curve is the attained physical optimum, not an assumed surrogate.
Anchored repair preserves the original two-sided relative tolerance uniformly on
the entire parameter cube. These statements make no machine-runtime claim.
-/

noncomputable section
open scoped BigOperators

namespace QecReliability.TensorLatent
open TensorBernstein

/-- Product Bernoulli masses are nonnegative throughout the parameter cube. -/
theorem mass_nonneg (ds : List ℕ) (p : Params ds) (hp : cube ds p)
    (b : CausesGrid ds) : 0 ≤ mass ds p b := by
  induction ds with
  | nil => exact zero_le_one
  | cons r ds ih =>
    exact mul_nonneg
      (QecPhysical.Stabilizer.causeMass_nonneg hp.1.1 hp.1.2 b.1)
      (ih p.2 hp.2 b.2)

/-- The full latent product law has total mass one, including zero-sized classes. -/
theorem mass_sum (ds : List ℕ) (p : Params ds) : ∑ b, mass ds p b = 1 := by
  classical
  induction ds with
  | nil =>
    change (∑ _b : PUnit, (1 : ℝ)) = 1
    apply Finset.sum_eq_single PUnit.unit
    · intro b _ hb
      exact (hb (Subsingleton.elim _ _)).elim
    · intro h
      exact (h (Finset.mem_univ _)).elim
  | cons r ds ih =>
    change (∑ b : Causes r × CausesGrid ds,
      QecPhysical.Stabilizer.causeMass p.1 b.1 * mass ds p.2 b.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ih]
    simpa only [mul_one] using QecPhysical.Stabilizer.causeMass_sum r p.1

end QecReliability.TensorLatent

namespace QecPhysical.Stabilizer
open QecReliability QecReliability.Binary QecPhysical.BinaryPauli
open QecReliability.TensorBernstein QecReliability.TensorLatent

variable {n : ℕ} {ds : List ℕ}

/-- The actual erasure scores averaged within every tensor Hamming layer. -/
def multivariateCoefficients (S : Submodule Bit (Pauli n))
    (C : CausesGrid ds → Finset (Fin n)) : Grid ds → ℝ :=
  observedCoefficients C (erasureScore S)

theorem multivariateCoefficients_range (S : Submodule Bit (Pauli n))
    (C : CausesGrid ds → Finset (Fin n)) (j : Grid ds) :
    0 ≤ multivariateCoefficients S C j ∧ multivariateCoefficients S C j ≤ 1 := by
  apply observedCoefficients_range
  intro E
  exact ⟨(score_range S E).1.le, (score_range S E).2⟩

/-- Explicit physical corner data, extended to the grid by canonical prefix
cause sets. Only values at the corner anchor set are used by the repair. -/
def physicalCornerAnchorValues (S : Submodule Bit (Pauli n))
    (C : CausesGrid ds → Finset (Fin n)) (j : Grid ds) : ℝ :=
  erasureScore S (C (canonicalCauses ds j))

/-- For a code supplied by Pauli rows, every canonical anchor has the exact
rational value computed by the existing binary-elimination score routine. -/
theorem physicalCornerAnchorValues_scoreRat
    (rows : List (List (SharedCircuit.PauliCoord n)))
    (C : CausesGrid ds → Finset (Fin n)) (j : Grid ds) :
    (BinaryElimination.scoreRat rows (C (canonicalCauses ds j)) : ℝ) =
      physicalCornerAnchorValues (SharedCircuit.rowSpace rows) C j :=
  BinaryElimination.scoreRat_correct rows (C (canonicalCauses ds j))

/-- At every corner, the Hamming layer is the single canonical cause tuple.
Thus these supplied physical scores are exact coefficients, with no estimation
or separate anchor-exactness assumption. -/
theorem physicalCornerAnchorValues_exact (S : Submodule Bit (Pauli n))
    (C : CausesGrid ds → Finset (Fin n)) :
    ∀ j ∈ MultivariateShapeRepair.cornerAnchors ds,
      physicalCornerAnchorValues S C j = multivariateCoefficients S C j := by
  classical
  intro j hj
  change j ∈ Finset.univ.image (cornerIndex ds) at hj
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hj
  simp only [physicalCornerAnchorValues, canonicalCauses_corner,
    multivariateCoefficients, observedCoefficients, layerCoefficients_corner]

/-- Repair using the explicit physical corner scores and an arbitrary estimated
table. The anchor set has at most `2 ^ ds.length` distinct entries, including
when some coordinates have degree zero. -/
def physicalCornerRepairedCurve (S : Submodule Bit (Pauli n))
    (C : CausesGrid ds → Finset (Fin n)) (estimates : Grid ds → ℝ) : Params ds → ℝ :=
  MultivariateShapeRepair.repairedCurve ds (MultivariateShapeRepair.cornerAnchors ds)
    (physicalCornerAnchorValues S C) estimates

namespace Lift
variable {S : Submodule Bit (Pauli n)} (L : Lift S)

/-- The physical erasure channel induced by independent latent Bernoulli classes. -/
def multivariateLatentErasure (C : CausesGrid ds → Finset (Fin n))
    (p : Params ds) (hp : cube ds p) : Channel L.LogicalIndex (ErasureFlagOutput n) :=
  L.latentErasure C (mass ds p) (mass_nonneg ds p hp) (mass_sum ds p)

/-- One fixed physical decoder attains the tensor reliability curve, and every
recovery channel is bounded above by exactly that curve. -/
theorem multivariateLatentErasure_optimum (C : CausesGrid ds → Finset (Fin n))
    (p : Params ds) (hp : cube ds p) :
    entanglementFidelity
        (L.erasureFlagDecoder.comp (L.multivariateLatentErasure C p hp)).map =
      curve ds (multivariateCoefficients S C) p ∧
    ∀ Q : Channel (ErasureFlagOutput n) L.LogicalIndex,
      entanglementFidelity (Q.comp (L.multivariateLatentErasure C p hp)).map ≤
        curve ds (multivariateCoefficients S C) p := by
  have h := L.latentErasure_optimum C (mass ds p) (mass_nonneg ds p hp) (mass_sum ds p)
  have heq : (∑ b, mass ds p b * erasureScore S (C b)) =
      curve ds (multivariateCoefficients S C) p :=
    (expectation_eq_sum ds (fun b => erasureScore S (C b)) p).symm.trans
      (expectation_eq_tensor ds (fun b => erasureScore S (C b)) p)
  rw [heq] at h
  exact h

include L in
/-- Adding latent causes can only decrease the physical coefficients when the
observation map is monotone in the componentwise subset order. -/
theorem multivariateCoefficients_antitone (C : CausesGrid ds → Finset (Fin n))
    (hC : Monotone C) : Antitone (multivariateCoefficients S C) := by
  apply observedCoefficients_antitone
  intro a b hab
  exact score_antitone S L.isotropic (hC hab)

/-- The repaired curve has valid shape for arbitrary estimates. Exact supplied
anchor values inherit their range from the actual physical coefficients. -/
theorem multivariate_repairedCurve_shape (C : CausesGrid ds → Finset (Fin n))
    (anchors : Finset (Grid ds)) (anchorValues estimates : Grid ds → ℝ)
    (ha : ∀ a ∈ anchors, anchorValues a = multivariateCoefficients S C a) :
    AntitoneOn (MultivariateShapeRepair.repairedCurve ds anchors anchorValues estimates)
        {p | cube ds p} ∧
      ∀ p, cube ds p →
        0 ≤ MultivariateShapeRepair.repairedCurve ds anchors anchorValues estimates p ∧
        MultivariateShapeRepair.repairedCurve ds anchors anchorValues estimates p ≤ 1 := by
  apply MultivariateShapeRepair.repairedCurve_shape
  intro a ha'
  rw [ha a ha']
  exact multivariateCoefficients_range S C a

/-- The coefficient accuracy event implies simultaneous same-tolerance accuracy
against the attained physical optimum at every parameter vector. -/
theorem multivariate_repairedCurve_relPair (C : CausesGrid ds → Finset (Fin n))
    (hC : Monotone C) (anchors : Finset (Grid ds))
    (anchorValues estimates : Grid ds → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ha : ∀ a ∈ anchors, anchorValues a = multivariateCoefficients S C a)
    (hpair : ∀ j, RelPair ε (multivariateCoefficients S C j) (estimates j)) :
    ∀ p (hp : cube ds p),
      RelPair ε
        (entanglementFidelity
          (L.erasureFlagDecoder.comp (L.multivariateLatentErasure C p hp)).map)
        (MultivariateShapeRepair.repairedCurve ds anchors anchorValues estimates p) := by
  intro p hp
  rw [(L.multivariateLatentErasure_optimum C p hp).1]
  exact MultivariateShapeRepair.repairedCurve_relPair ds anchors anchorValues estimates
    (multivariateCoefficients S C) hε hε1 (L.multivariateCoefficients_antitone C hC)
    (multivariateCoefficients_range S C) ha hpair p hp

/-- Exact corner anchors recover the physical optimum at every cube corner,
without any accuracy assumption on the other supplied estimates. -/
theorem multivariate_repairedCurve_corner (C : CausesGrid ds → Finset (Fin n))
    (hC : Monotone C) (anchors : Finset (Grid ds))
    (anchorValues estimates : Grid ds → ℝ)
    (ha : ∀ a ∈ anchors, anchorValues a = multivariateCoefficients S C a)
    (hc : ∀ b, cornerIndex ds b ∈ anchors) (b : Corner ds) :
    MultivariateShapeRepair.repairedCurve ds anchors anchorValues estimates (cornerParams ds b) =
      entanglementFidelity
        (L.erasureFlagDecoder.comp (L.multivariateLatentErasure C (cornerParams ds b)
          (cornerParams_mem_cube ds b))).map := by
  rw [(L.multivariateLatentErasure_optimum C (cornerParams ds b)
    (cornerParams_mem_cube ds b)).1, curve_corner]
  exact MultivariateShapeRepair.repairedCurve_corner ds anchors anchorValues estimates
    (multivariateCoefficients S C) (L.multivariateCoefficients_antitone C hC)
    (fun j => (multivariateCoefficients_range S C j).1) ha hc b


/-- The explicit corner-anchored physical repair always has the desired shape,
regardless of estimate accuracy or monotonicity of the observation map. -/
theorem physicalCornerRepairedCurve_shape (C : CausesGrid ds → Finset (Fin n))
    (estimates : Grid ds → ℝ) :
    AntitoneOn (physicalCornerRepairedCurve S C estimates) {p | cube ds p} ∧
      ∀ p, cube ds p →
        0 ≤ physicalCornerRepairedCurve S C estimates p ∧
        physicalCornerRepairedCurve S C estimates p ≤ 1 :=
  multivariate_repairedCurve_shape C (MultivariateShapeRepair.cornerAnchors ds)
    (physicalCornerAnchorValues S C) estimates (physicalCornerAnchorValues_exact S C)

/-- A closed same-tolerance physical guarantee: the caller supplies only the
estimate table and its original pointwise accuracy event. Corner values are
computed from the physical erasure scores, rather than hypothesized exact. -/
theorem physicalCornerRepairedCurve_relPair (C : CausesGrid ds → Finset (Fin n))
    (hC : Monotone C) (estimates : Grid ds → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hpair : ∀ j, RelPair ε (multivariateCoefficients S C j) (estimates j)) :
    ∀ p (hp : cube ds p),
      RelPair ε
        (entanglementFidelity
          (L.erasureFlagDecoder.comp (L.multivariateLatentErasure C p hp)).map)
        (physicalCornerRepairedCurve S C estimates p) :=
  L.multivariate_repairedCurve_relPair C hC (MultivariateShapeRepair.cornerAnchors ds)
    (physicalCornerAnchorValues S C) estimates hε hε1
    (physicalCornerAnchorValues_exact S C) hpair

/-- Every corner equals the actual physical optimum, even for inaccurate tables.
Repeated corner indices in zero-sized latent classes need no special case. -/
theorem physicalCornerRepairedCurve_corner (C : CausesGrid ds → Finset (Fin n))
    (hC : Monotone C) (estimates : Grid ds → ℝ) (b : Corner ds) :
    physicalCornerRepairedCurve S C estimates (cornerParams ds b) =
      entanglementFidelity
        (L.erasureFlagDecoder.comp (L.multivariateLatentErasure C (cornerParams ds b)
          (cornerParams_mem_cube ds b))).map :=
  L.multivariate_repairedCurve_corner C hC (MultivariateShapeRepair.cornerAnchors ds)
    (physicalCornerAnchorValues S C) estimates (physicalCornerAnchorValues_exact S C)
    (MultivariateShapeRepair.cornerIndex_mem ds) b

end Lift
end QecPhysical.Stabilizer
