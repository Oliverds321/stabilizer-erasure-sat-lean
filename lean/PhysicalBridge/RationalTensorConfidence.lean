import PhysicalBridge.TensorConfidence
import PhysicalBridge.RationalTensorRepair
import QecReliability.CachedEvaluator

/-! Cached natural-number count estimates, exact rational tensor repair, and
the physical probability guarantee for that same returned coefficient table.
The concrete query builders and finite-tape implementation instantiate the
explicit decision-query interface used here. -/
set_option autoImplicit false

namespace QecReliability.RationalTensorConfidence
open Binary TensorBernstein TensorLatent TensorCoefficientCounting RationalOutput
open QecPhysical QecPhysical.Stabilizer

variable {Ω : Type*} [Fintype Ω] {n : ℕ} {ds : List ℕ}
  {S : Submodule Bit (Pauli n)} {C : CausesGrid ds → Finset (Fin n)}
  {H : HashStages Ω (Key n ds) (SharedCircuit.LatentEncoding.keySize n ds.sum)}

/-- The numerator and denominator are formed from the two cached natural
counts. No real computation participates in constructing this output. -/
def estimateRatios
    (D : ∀ i, DecisionQueries (keyBits n ds) H (coefficientModels S C i))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) (j : Grid ds) : Ratio :=
  Ratio.counts
    (CachedAnswers.median (D (true,j)).base.answer
      (fun s seed => ((D (true,j)).cell s seed).answer) B m ω).1
    (CachedAnswers.median (D (false,j)).base.answer
      (fun s seed => ((D (false,j)).cell s seed).answer) B m ω).1

theorem estimateRatios_value
    (D : ∀ i, DecisionQueries (keyBits n ds) H (coefficientModels S C i))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) (j : Grid ds) :
    (estimateRatios D B m ω j).value =
      estimates (fun i => (D i).toTrialOracle) B m ω j := by
  simp only [estimateRatios, CachedAnswers.median_eq, Ratio.counts_value, DecisionQueries.cachedMedian_value,
    estimates, ExactTrialOracle.amplified]

variable (rows : List (List (SharedCircuit.PauliCoord n)))
  (C : CausesGrid ds → Finset (Fin n))

def output
    (D : ∀ i, DecisionQueries (keyBits n ds) H
      (coefficientModels (SharedCircuit.rowSpace rows) C i))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) : List Ratio :=
  RationalTensorRepair.prepare ds rows C (estimateRatios D B m ω)

noncomputable def outputCurve
    (D : ∀ i, DecisionQueries (keyBits n ds) H
      (coefficientModels (SharedCircuit.rowSpace rows) C i))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) : Params ds → ℝ :=
  curve ds (fun j => (RationalTensorRepair.coefficient ds rows C
    (estimateRatios D B m ω) j).value)

theorem output_length
    (D : ∀ i, DecisionQueries (keyBits n ds) H
      (coefficientModels (SharedCircuit.rowSpace rows) C i))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) :
    (output rows C D B m ω).length = (ds.map (fun r => r+1)).prod := by
  simp only [output, RationalTensorRepair.prepare_eq_map, List.length_map,
    RationalTensorRepair.enum_length]

theorem outputCurve_eq
    (D : ∀ i, DecisionQueries (keyBits n ds) H
      (coefficientModels (SharedCircuit.rowSpace rows) C i))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) :
    outputCurve rows C D B m ω =
      physicalCornerRepairedCurve (SharedCircuit.rowSpace rows) C
        (estimates (fun i => (D i).toTrialOracle) B m ω) := by
  simp only [outputCurve, RationalTensorRepair.coefficient_value,
    estimateRatios_value, physicalCornerRepairedCurve, MultivariateShapeRepair.repairedCurve]

theorem output_physical_confidence
    (L : Lift (SharedCircuit.rowSpace rows)) (hC : Monotone C)
    (D : ∀ i, DecisionQueries (keyBits n ds) H
      (coefficientModels (SharedCircuit.rowSpace rows) C i))
    (B m : ℕ) (hB : 0 < B) {ε δ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hcell : 16 ≤ (ε/3)^2*(B:ℝ))
    (hrepeat : (Fintype.card (Index ds):ℝ)*(1/2:ℝ)^(m+2) ≤ δ) :
    (∀ ω, L.TensorPhysicalStructure C (outputCurve rows C D B m ω)) ∧
    1-δ ≤ (repeatedLaw H.law m).prob (fun ω =>
      L.TensorPhysicalAccuracy C ε (outputCurve rows C D B m ω)) := by
  simp only [outputCurve_eq]
  exact L.tensor_counting_physical_confidence C hC H
    (fun i => (D i).toTrialOracle) B m hB hε hε1 hcell hrepeat

end QecReliability.RationalTensorConfidence
