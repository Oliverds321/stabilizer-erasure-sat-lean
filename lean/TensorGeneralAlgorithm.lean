import TensorPhysicalVectorConfidence
import TensorGeneralSemantics

/-! The general-circuit multiclass estimator over the concrete all-length hashes,
cached SAT decision queries and rational budgets of the tensor machine, as a
function of the raw coin string. Same queries, same coins, same budgets as
`PhysicalAlgorithm.outputVector`; only the final step differs: corner
replacement instead of shape repair. Source-level algorithm, no machine claim. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.TensorMachine.GeneralAlgorithm
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate RationalOutput
open TensorBernstein TensorLatent TensorCoefficientCounting QecPhysical QecPhysical.Stabilizer

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t)
  {n : ℕ} {ds : List ℕ} (rows : List (List (PauliCoord n)))
  (C : SharedCircuit.Program ds.sum n) (solver : ∀ v, PrefixCNF.ExactSAT v 3)

/-- The coefficient table carried by an output vector, in grid coordinates
(same definition as `TensorMachine.vectorTable` of `TensorFixedQuantumStrong`). -/
def vectorTable (ds : List ℕ) (v : RationalOutput.Vector (slots ds-1)) : Grid ds → ℝ :=
  fun j => (v.get (position ds j)).value

theorem vectorCurve_eq_table (ds : List ℕ) (v : RationalOutput.Vector (slots ds-1)) :
    vectorCurve ds v = curve ds (vectorTable ds v) := rfl

/-- Flat output list on a coin string. -/
def output (B m : ℕ)
    (coins : CodeHash.BitTape (CodeHash.repeatBits
      (Factory.length hD hd A n ds) (Factory.width hD hd A n ds) m)) : List Ratio :=
  TensorGeneral.output rows (TensorEncoding.circuitMap C)
    (PhysicalAlgorithm.decisions hD hd A rows C solver) B m
    (CodeHash.repeatedSeedTapeEquiv _ _ m coins)

/-- The same output as a rational vector of the machine's output length. -/
def outputVector (B m : ℕ)
    (coins : CodeHash.BitTape (CodeHash.repeatBits
      (Factory.length hD hd A n ds) (Factory.width hD hd A n ds) m)) :
    RationalOutput.Vector (slots ds-1) where
  entries := (output hD hd A rows C solver B m coins).toArray
  length_eq := by
    rw [List.size_toArray]
    exact (TensorGeneral.output_length rows (TensorEncoding.circuitMap C)
      (PhysicalAlgorithm.decisions hD hd A rows C solver) B m _).trans
        (Boundary.slots_pred_succ ds).symm

theorem outputVector_get (B m : ℕ)
    (coins : CodeHash.BitTape (CodeHash.repeatBits
      (Factory.length hD hd A n ds) (Factory.width hD hd A n ds) m))
    (j : Fin (slots ds-1+1)) :
    (outputVector hD hd A rows C solver B m coins).get j =
      TensorGeneral.cornerCoefficient ds rows (TensorEncoding.circuitMap C)
        (RationalTensorConfidence.estimateRatios (PhysicalAlgorithm.decisions hD hd A rows C solver)
          B m (CodeHash.repeatedSeedTapeEquiv _ _ m coins)) (Boundary.index ds j) := by
  simp only [outputVector,RationalOutput.Vector.get,List.getElem_toArray,output,
    TensorGeneral.output,TensorGeneral.cornerPrepare,List.getElem_map,
    Boundary.index,ordinalIndex,List.get_eq_getElem]

theorem vectorTable_eq (B m : ℕ)
    (coins : CodeHash.BitTape (CodeHash.repeatBits
      (Factory.length hD hd A n ds) (Factory.width hD hd A n ds) m)) :
    vectorTable ds (outputVector hD hd A rows C solver B m coins) =
      TensorGeneral.table rows (TensorEncoding.circuitMap C)
        (PhysicalAlgorithm.decisions hD hd A rows C solver) B m
        (CodeHash.repeatedSeedTapeEquiv _ _ m coins) := by
  funext j
  simp only [vectorTable, TensorGeneral.table]
  rw [outputVector_get, position_index]

/-- General-circuit guarantee for the vector: deterministic table structure on
every coin string, and one coin event of probability at least `1-c/d` giving
two-tail accuracy `a/b` of the tensor curve on the entire parameter cube. -/
theorem vector_guarantee (L : Lift (rowSpace rows))
    (a b c d : ℕ) (ha : 0<a) (hab : a≤b) (hc : 0<c) (hd' : 0<d) :
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*slots ds) c d
    let f := multivariateCoefficients (rowSpace rows) (TensorEncoding.circuitMap C)
    (∀ coins,
      let g := vectorTable ds (outputVector hD hd A rows C solver B m coins)
      (∀ j, 0 ≤ g j ∧ g j ≤ 1) ∧
      (∀ b : Corner ds, g (cornerIndex ds b) = f (cornerIndex ds b) ∧
        g (cornerIndex ds b) =
          erasureScore (rowSpace rows) (TensorEncoding.circuitMap C (cornerCauses ds b))) ∧
      (∀ j, g j = 1 ↔ f j = 1) ∧
      TensorGeneral.GeneralStructure rows (TensorEncoding.circuitMap C) L
        (vectorCurve ds (outputVector hD hd A rows C solver B m coins))) ∧
    1-(c:ℝ)/d ≤ (uniformLaw (CodeHash.BitTape (CodeHash.repeatBits
      (Factory.length hD hd A n ds) (Factory.width hD hd A n ds) m))).prob
      (fun coins => L.TensorPhysicalAccuracy (TensorEncoding.circuitMap C) ((a:ℝ)/b)
        (vectorCurve ds (outputVector hD hd A rows C solver B m coins))) := by
  have hb : 0 < b := ha.trans_le hab
  intro B m f
  have hcurve : ∀ coins, vectorCurve ds (outputVector hD hd A rows C solver B m coins) =
      TensorGeneral.outputCurve rows (TensorEncoding.circuitMap C)
        (PhysicalAlgorithm.decisions hD hd A rows C solver) B m
        (CodeHash.repeatedSeedTapeEquiv _ _ m coins) := by
    intro coins
    rw [vectorCurve_eq_table, vectorTable_eq]
    rfl
  refine ⟨fun coins => ?_, ?_⟩
  · intro g
    have hg : g = TensorGeneral.table rows (TensorEncoding.circuitMap C)
        (PhysicalAlgorithm.decisions hD hd A rows C solver) B m
        (CodeHash.repeatedSeedTapeEquiv _ _ m coins) := vectorTable_eq hD hd A rows C solver B m coins
    obtain ⟨h1,h2,h3⟩ := TensorGeneral.table_structure rows (TensorEncoding.circuitMap C) L
      (PhysicalAlgorithm.decisions hD hd A rows C solver) B m
      (CodeHash.repeatedSeedTapeEquiv _ _ m coins)
    rw [hg, hcurve]
    exact ⟨h1,h2,h3,TensorGeneral.curve_structure rows (TensorEncoding.circuitMap C) L _ B m _⟩
  · simp only [hcurve]
    have hm : m = rationalRepetitionBudget (Fintype.card (Index ds)) c d := by
      simp only [m, index_card]
      rfl
    have hconf := TensorGeneral.output_physical_confidence rows (TensorEncoding.circuitMap C) L
      (PhysicalAlgorithm.decisions hD hd A rows C solver) B m
      (rationalCellBudget_pos ha hb)
      (rational_epsilon ha hb hab).1 (rational_epsilon ha hb hab).2
      (rationalCellBudget_spec ha hb)
      (hm ▸ rationalRepetitionBudget_spec (TensorCountingConfidence.index_card_pos ds) hc hd')
    exact CodeHash.confidence_from_raw_bits _ _ _
      (fun ω => L.TensorPhysicalAccuracy (TensorEncoding.circuitMap C) ((a:ℝ)/b)
        (TensorGeneral.outputCurve rows (TensorEncoding.circuitMap C)
          (PhysicalAlgorithm.decisions hD hd A rows C solver) B m ω)) ((c:ℝ)/d) hconf

end QecReliability.TensorMachine.GeneralAlgorithm

#print axioms QecReliability.TensorMachine.GeneralAlgorithm.vector_guarantee
