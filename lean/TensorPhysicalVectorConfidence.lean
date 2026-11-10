import TensorPhysicalOutput

/-! Physical reliability guarantees stated for the flat rational vector that
the machine serializes, with exactly the runtime repetition budget 2Q. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.TensorMachine.PhysicalAlgorithm
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open TensorBernstein TensorCoefficientCounting QecPhysical QecPhysical.Stabilizer

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t)
  {n : ℕ} {ds : List ℕ} (rows : List (List (PauliCoord n)))
  (C : SharedCircuit.Program ds.sum n) (solver : ∀ v, PrefixCNF.ExactSAT v 3)

theorem vector_confidence (L : Lift (rowSpace rows))
    (hC : Monotone (TensorEncoding.circuitMap C))
    (a b c d : ℕ) (ha : 0<a) (hab : a≤b) (hc : 0<c) (hd' : 0<d) :
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*slots ds) c d
    (∀ coins, L.TensorPhysicalStructure (TensorEncoding.circuitMap C)
      (vectorCurve ds (outputVector hD hd A rows C solver B m coins))) ∧
    1-(c:ℝ)/d ≤ (uniformLaw (CodeHash.BitTape (CodeHash.repeatBits
      (Factory.length hD hd A n ds) (Factory.width hD hd A n ds) m))).prob
      (fun coins => L.TensorPhysicalAccuracy (TensorEncoding.circuitMap C) ((a:ℝ)/b)
        (vectorCurve ds (outputVector hD hd A rows C solver B m coins))) := by
  have h := rational_bit_guarantee hD hd A rows C solver L hC a b c d ha hab hc hd'
  rw [index_card] at h
  change (∀ coins, (output hD hd A rows C solver _ _ coins).length = slots ds ∧ _) ∧ _ at h
  simp only [vectorCurve_output]
  exact ⟨fun coins => (h.1 coins).2,h.2⟩

end QecReliability.TensorMachine.PhysicalAlgorithm
