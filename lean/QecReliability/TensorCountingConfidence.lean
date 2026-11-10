import QecReliability.TensorQuantumEncoder
import QecReliability.CodeHashStages
import QecReliability.ExplicitBitSampler
import PhysicalBridge.RationalBudgets

/-! Concrete SAT decisions and one finite fair-bit word supply the joint
multiclass coefficient event. The hash system and its supplied circuits remain
explicit; this module makes no machine-cost or physical-channel claim. -/

noncomputable section
namespace QecReliability.TensorCountingConfidence
open TensorBernstein TensorLatent TensorCoefficientCounting
open SharedCircuit SharedCircuit.TensorEncoding

variable {n L t : ℕ} {ds : List ℕ}
  (rows : List (List (PauliCoord n))) (C : Program ds.sum n)
  (S : CodeHash.System (Key n ds) L t (SharedCircuit.LatentEncoding.keySize n ds.sum))
  (K : SuppliedHashCircuits S.stages (TensorCoefficientCounting.keyBits n ds))
  (solver : ∀ v, PrefixCNF.ExactSAT v 3)

def oracles (i : Index ds) :
    ExactTrialOracle S.stages
      (coefficientModels (rowSpace rows) (TensorEncoding.circuitMap C) i) :=
  (TensorEncoding.queries ds rows C S.stages K solver i).toTrialOracle

def coefficientEstimates (B m : ℕ) (ω : Fin (2*m+1) → CodeHash.Seed L t) : Grid ds → ℝ :=
  estimates (oracles rows C S K solver) B m ω

theorem coefficients_confidence
    (hS : rowSpace rows ≤ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows))
    (B m : ℕ) (hB : 0 < B) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcell : 16 ≤ (ε/3)^2*(B:ℝ))
    (hrepeat : (Fintype.card (Index ds):ℝ)*(1/2:ℝ)^(m+2) ≤ δ) :
    1-δ ≤ (repeatedLaw S.stages.law m).prob (fun ω => ∀ j,
      RelPair ε (observedCoefficients (TensorEncoding.circuitMap C) (Binary.score (rowSpace rows)) j)
        (coefficientEstimates rows C S K solver B m ω j) ∧
      0 ≤ coefficientEstimates rows C S K solver B m ω j ∧
      coefficientEstimates rows C S K solver B m ω j ≤ 1) :=
  TensorCoefficientCounting.coefficients_confidence (rowSpace rows) hS
    (TensorEncoding.circuitMap C) S.stages (oracles rows C S K solver)
    B m hB hε hε1 hcell hrepeat

def bitEstimates (B m : ℕ) (coins : CodeHash.BitTape (CodeHash.repeatBits L t m)) : Grid ds → ℝ :=
  coefficientEstimates rows C S K solver B m (CodeHash.repeatedSeedTapeEquiv L t m coins)

/-- The same complete finite bit word supplies every coefficient and both sides. -/
theorem finite_bit_confidence
    (hS : rowSpace rows ≤ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows))
    (B m : ℕ) (hB : 0 < B) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcell : 16 ≤ (ε/3)^2*(B:ℝ))
    (hrepeat : (Fintype.card (Index ds):ℝ)*(1/2:ℝ)^(m+2) ≤ δ) :
    1-δ ≤ (uniformLaw (CodeHash.BitTape (CodeHash.repeatBits L t m))).prob (fun coins => ∀ j,
      RelPair ε (observedCoefficients (TensorEncoding.circuitMap C) (Binary.score (rowSpace rows)) j)
        (bitEstimates rows C S K solver B m coins j) ∧
      0 ≤ bitEstimates rows C S K solver B m coins j ∧
      bitEstimates rows C S K solver B m coins j ≤ 1) := by
  let E : (Fin (2*m+1) → CodeHash.Seed L t) → Prop := fun ω => ∀ j,
    RelPair ε (observedCoefficients (TensorEncoding.circuitMap C) (Binary.score (rowSpace rows)) j)
      (coefficientEstimates rows C S K solver B m ω j) ∧
    0 ≤ coefficientEstimates rows C S K solver B m ω j ∧
    coefficientEstimates rows C S K solver B m ω j ≤ 1
  change 1-δ ≤ (uniformLaw (CodeHash.BitTape (CodeHash.repeatBits L t m))).prob
    (fun coins => E (CodeHash.repeatedSeedTapeEquiv L t m coins))
  rw [CodeHash.repeatedSeedTape_law L t m E]
  exact coefficients_confidence rows C S K solver hS B m hB hε hε1 hcell hrepeat

theorem index_card_pos (ds : List ℕ) : 0 < Fintype.card (Index ds) := by
  rw [index_card]
  have hp : 0 < (ds.map (fun r => r+1)).prod := by
    induction ds with
    | nil => exact Nat.zero_lt_one
    | cons r ds ih => exact Nat.mul_pos (Nat.zero_lt_succ r) ih
  exact Nat.mul_pos (by decide) hp

/-- Integer precision budgets discharge both cell and union-bound requirements. -/
theorem rational_finite_bit_confidence
    (hS : rowSpace rows ≤ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows))
    (a b c d : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (hab : a≤b) :
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (Fintype.card (Index ds)) c d
    1-(c:ℝ)/d ≤ (uniformLaw (CodeHash.BitTape (CodeHash.repeatBits L t m))).prob
      (fun coins => ∀ j,
        RelPair ((a:ℝ)/b)
          (observedCoefficients (TensorEncoding.circuitMap C) (Binary.score (rowSpace rows)) j)
          (bitEstimates rows C S K solver B m coins j) ∧
        0 ≤ bitEstimates rows C S K solver B m coins j ∧
        bitEstimates rows C S K solver B m coins j ≤ 1) := by
  exact finite_bit_confidence rows C S K solver hS _ _ (rationalCellBudget_pos ha hb)
    (rational_epsilon ha hb hab).1 (rational_epsilon ha hb hab).2
    (rationalCellBudget_spec ha hb) (rationalRepetitionBudget_spec (index_card_pos ds) hc hd)

end QecReliability.TensorCountingConfidence
