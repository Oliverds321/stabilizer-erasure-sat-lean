import PhysicalBridge.RationalBudgets
import PhysicalBridge.PhysicalCachedTails

/-! The actual cached estimator now selects its cell/repetition budgets using
only integer arithmetic. Endpoint acquisition and real postprocessing remain
explicitly separated mathematical interfaces. -/
namespace QecReliability.SharedCircuit.ConcreteQuantum
open LatentEncoding Binary

/-- Computable relative to supplied hash circuits, concrete SAT and the seed vector. -/
def prepareRational {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (a b c d : ℕ)
    (ω : Fin (2*rationalRepetitionBudget (2*(r+1)) c d+1) → Ω) : CoefficientTable r :=
  prepare rows C H K solver (rationalCellBudget a b) (rationalRepetitionBudget (2*(r+1)) c d) ω

end QecReliability.SharedCircuit.ConcreteQuantum

namespace QecPhysical.Stabilizer.Lift
open QecReliability QecReliability.Binary
open QecReliability.SharedCircuit
open QecReliability.SharedCircuit.LatentEncoding
open QecReliability.SharedCircuit.ConcreteQuantum

variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (L : Lift (rowSpace rows)) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (a b c d : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (hab : a≤b)

include ha hb hc hd hab

/-- Arbitrary latent circuit: deterministic raw resources/endpoints/range, and
one simultaneous physical both-tail event. No real search chooses the budgets. -/
theorem rational_endpoint_confidence :
    (∀ ω,
      let T := prepareRational rows C H K solver a b c d ω
      RawCacheResources n r (rationalCellBudget a b) (rationalRepetitionBudget (2*(r+1)) c d) T ∧
      EndpointStructure (rowSpace rows) (circuitMap C)
        (cachedEndpointCurve (rowSpace rows) (circuitMap C) T)) ∧
    1-(c:ℝ)/d ≤ (repeatedLaw H.law (rationalRepetitionBudget (2*(r+1)) c d)).prob
      (fun ω => L.PhysicalAccuracy (circuitMap C) ((a:ℝ)/b)
        (cachedEndpointCurve (rowSpace rows) (circuitMap C) (prepareRational rows C H K solver a b c d ω))) := by
  have he := rational_epsilon ha hb hab
  exact cached_physical_endpoint_confidence rows C H K solver L _ _
    (rationalCellBudget_pos ha hb) he.1 he.2 (rationalCellBudget_spec ha hb)
    (by exact_mod_cast rationalRepetitionBudget_spec (K:=2*(r+1)) (by omega) hc hd)

/-- True-layer antitonicity is the only additional assumption for repair accuracy. -/
theorem rational_shape_confidence
    (hanti : Antitone (layerAverage (circuitMap C) (score (rowSpace rows)))) :
    (∀ ω,
      let T := prepareRational rows C H K solver a b c d ω
      RawCacheResources n r (rationalCellBudget a b) (rationalRepetitionBudget (2*(r+1)) c d) T ∧
      ShapeStructure (rowSpace rows) (circuitMap C)
        (cachedShapeCurve (rowSpace rows) (circuitMap C) T)) ∧
    1-(c:ℝ)/d ≤ (repeatedLaw H.law (rationalRepetitionBudget (2*(r+1)) c d)).prob
      (fun ω => L.PhysicalAccuracy (circuitMap C) ((a:ℝ)/b)
        (cachedShapeCurve (rowSpace rows) (circuitMap C) (prepareRational rows C H K solver a b c d ω))) := by
  have he := rational_epsilon ha hb hab
  exact cached_physical_shape_confidence_of_layers_antitone rows C H K solver L hanti _ _
    (rationalCellBudget_pos ha hb) he.1 he.2 (rationalCellBudget_spec ha hb)
    (by exact_mod_cast rationalRepetitionBudget_spec (K:=2*(r+1)) (by omega) hc hd)

end QecPhysical.Stabilizer.Lift
