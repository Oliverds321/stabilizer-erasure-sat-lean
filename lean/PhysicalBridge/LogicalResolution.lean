import PhysicalBridge.LogicalQuotient
import PhysicalBridge.TraceResolution

/-! A derived logical unitary resolution, valid for every supplied stabilizer
lift and its chosen codespace isometry. It uses no canonical-Pauli-frame premise. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace QecPhysical.Stabilizer.Lift
open scoped BigOperators
open Matrix Module
open QecReliability.Binary
open QecPhysical.BinaryPauli
variable {n : ℕ} {S : Submodule Bit (Pauli n)} (L : Lift S)

def logicalResolution : UnitaryResolution L.LogicalIndex (LogicalClass S) :=
  UnitaryResolution.ofTraceOrthogonal L.logicalClassOp L.logicalClassOp_unitary
    L.logicalClass_card_square L.logicalClassOp_trace_inner

theorem logicalResolution_intertwine (c : LogicalClass S) :
    L.encoding * L.logicalResolution.op c = pauli (logicalRepresentative c).val * L.encoding :=
  L.logicalOp_intertwine _

/-- The all-CPTP theorem now applies to the derived logical coset operators. -/
theorem logical_uniform_optimal_recovery (A : Finset (LogicalClass S)) (hA : A.Nonempty)
    (m : LogicalClass S) (hm : m ∈ A) :
    entanglementFidelity ((L.logicalResolution.inverseChannel m).comp
      (L.logicalResolution.noiseChannel (UnitaryResolution.uniformWeights A)
        (UnitaryResolution.uniformWeights_nonneg A) (UnitaryResolution.uniformWeights_sum A hA))).map =
      (A.card : ℝ)⁻¹ ∧
    ∀ R : Channel L.LogicalIndex L.LogicalIndex,
      entanglementFidelity (R.comp
        (L.logicalResolution.noiseChannel (UnitaryResolution.uniformWeights A)
          (UnitaryResolution.uniformWeights_nonneg A) (UnitaryResolution.uniformWeights_sum A hA))).map ≤
        (A.card : ℝ)⁻¹ :=
  L.logicalResolution.uniform_optimal_recovery A hA m hm

end QecPhysical.Stabilizer.Lift
