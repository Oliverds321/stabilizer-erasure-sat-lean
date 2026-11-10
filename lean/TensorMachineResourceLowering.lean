import TensorMachineLowering
import ResourceAssemblyAdapter

/-! Resource-aware SAT lowering for the same fixed tensor machine. The proof
uses the decoded request extent, including both dimension and encoded payload. -/

set_option autoImplicit false
noncomputable section
namespace QecReliability.TensorMachine
open FL RegMachine Interp Assembly Final OracleCost OracleCost.MultiTape

theorem tape_run_resource {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    {E : Machine kE ΓE ΛE} {density : ℕ} {PtE PsE : PolynomialEnvelope} {timeE : ℕ → ℕ}
    {resource : SATRequest → ℕ} (spec : ResourceEncodedSAT E density PtE PsE timeE resource)
    {P : FL.Program} {I : Assembly.Indices} {cap S Cost : ℕ} {bits : List Bool}
    {r : ℕ} {v : RationalOutput.Vector r}
    (h : ∃ u : Regs 20,
      ORuns (resourceSatOracle E density resource cap) S (mainProg P I).body
        (inputRegs (R := 19) bits) u Cost ∧ u rOUT = outputWord v) :
    ∃ run : Completed (theMachine E P I) bits,
      Outputs (theMachine E P I) run (outTape kE) v ∧
      run.time ≤ (3 * kE + 6) * (Cost + 1) ∧
      run.cells ≤ (19 + kE + 1 + 1) * (2 * max S (PsE.eval cap) + 3) := by
  obtain ⟨u,hr,ho⟩ := h
  exact complete_of_oruns_resource (resourceSatOracle E density resource cap)
    (resourceSatOracle_realizes spec cap) hr ho

end QecReliability.TensorMachine
end
