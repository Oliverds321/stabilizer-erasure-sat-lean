import TensorFactorySeeds
import PhysicalBridge.RationalTensorConfidence
import PhysicalBridge.GeneralStabilizer

/-! Concrete all-length hashes and rational precision budgets for the tensor
physical estimator. This source-algorithm guarantee is distinct from the
finite-tape execution/refinement theorem. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.TensorMachine.PhysicalAlgorithm
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open TensorBernstein TensorLatent TensorCoefficientCounting
open QecPhysical QecPhysical.Stabilizer

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t)
  {n : ℕ} {ds : List ℕ}
  (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
  (solver : ∀ v, PrefixCNF.ExactSAT v 3)

def decisions := TensorEncoding.queries ds rows C (Factory.system hD hd A n ds).stages
  (Factory.circuits hD hd A n ds) solver

def seedCurve (B m : ℕ)
    (ω : Fin (2*m+1) → CodeHash.Seed (Factory.length hD hd A n ds) (Factory.width hD hd A n ds)) :
    Params ds → ℝ :=
  RationalTensorConfidence.outputCurve rows (TensorEncoding.circuitMap C)
    (decisions hD hd A rows C solver) B m ω

def output (B m : ℕ)
    (coins : CodeHash.BitTape (CodeHash.repeatBits
      (Factory.length hD hd A n ds) (Factory.width hD hd A n ds) m)) : List RationalOutput.Ratio :=
  RationalTensorConfidence.output rows (TensorEncoding.circuitMap C)
    (decisions hD hd A rows C solver) B m
    (CodeHash.repeatedSeedTapeEquiv _ _ m coins)

def outputCurve (B m : ℕ)
    (coins : CodeHash.BitTape (CodeHash.repeatBits
      (Factory.length hD hd A n ds) (Factory.width hD hd A n ds) m)) : Params ds → ℝ :=
  seedCurve hD hd A rows C solver B m (CodeHash.repeatedSeedTapeEquiv _ _ m coins)

theorem rational_bit_guarantee
    (L : Lift (rowSpace rows)) (hC : Monotone (TensorEncoding.circuitMap C))
    (a b c d : ℕ) (ha : 0<a) (hab : a≤b) (hc : 0<c) (hd' : 0<d) :
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (Fintype.card (Index ds)) c d
    (∀ coins, (output hD hd A rows C solver B m coins).length =
      (ds.map (fun r => r+1)).prod ∧
      L.TensorPhysicalStructure (TensorEncoding.circuitMap C)
        (outputCurve hD hd A rows C solver B m coins)) ∧
    1-(c:ℝ)/d ≤ (uniformLaw (CodeHash.BitTape (CodeHash.repeatBits
      (Factory.length hD hd A n ds) (Factory.width hD hd A n ds) m))).prob
      (fun coins => L.TensorPhysicalAccuracy (TensorEncoding.circuitMap C) ((a:ℝ)/b)
        (outputCurve hD hd A rows C solver B m coins)) := by
  have hb : 0 < b := ha.trans_le hab
  dsimp only
  obtain ⟨hstructure,hconfidence⟩ := RationalTensorConfidence.output_physical_confidence
    rows (TensorEncoding.circuitMap C) L hC (decisions hD hd A rows C solver)
    (rationalCellBudget a b) (rationalRepetitionBudget (Fintype.card (Index ds)) c d)
    (rationalCellBudget_pos ha hb)
    (rational_epsilon ha hb hab).1 (rational_epsilon ha hb hab).2
    (rationalCellBudget_spec ha hb)
    (rationalRepetitionBudget_spec (TensorCountingConfidence.index_card_pos ds) hc hd')
  refine ⟨fun coins => ⟨?_, ?_⟩, ?_⟩
  · exact RationalTensorConfidence.output_length rows (TensorEncoding.circuitMap C)
      (decisions hD hd A rows C solver) _ _ _
  · exact hstructure _
  · exact CodeHash.confidence_from_raw_bits _ _ _
      (fun ω => L.TensorPhysicalAccuracy (TensorEncoding.circuitMap C) ((a:ℝ)/b)
        (seedCurve hD hd A rows C solver _ _ ω)) ((c:ℝ)/d) hconfidence

end QecReliability.TensorMachine.PhysicalAlgorithm
