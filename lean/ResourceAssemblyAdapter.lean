import Assembly.Main
import ResourceSATOracle

/-! Generic proof adapter for the unchanged fixed assembly machine. No resource
measure, cap, or oracle specification is passed to the runtime machine. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.Assembly
open RegMachine Interp FL Function
open OracleCost OracleCost.MultiTape OracleCost.MultiTape.InjectiveTapeLift
open OracleCost.WholeWrapperCandidate
open SharedCircuit SharedCircuit.LatentEncoding RationalOutput QecPhysical QecPhysical.Stabilizer
open Final SharedCircuit.FixedLocalEmitter.AllLength FiniteLocalSelectorCandidate
variable {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]

/-- From an abstract run of the main program body to a completed machine run. -/
theorem complete_of_oruns_resource {E : Machine kE ΓE ΛE} (O : OracleSpec) {Cb : ℕ}
    (hE : ∀ w, O.qok w → ∃ run : Completed E w, run.output = O.oracle w ∧
      run.time + run.cells ≤ O.ocost w ∧ run.cells ≤ Cb)
    {P : Program} {I : Indices}
    {S Cst : ℕ} {bits : List Bool} {u : Regs 20} {r : ℕ} {v : RationalOutput.Vector r}
    (h : ORuns O S (mainProg P I).body (inputRegs (R := 19) bits) u Cst)
    (hout : u rOUT = outputWord v) :
    ∃ run : Completed (theMachine E P I) bits,
      Outputs (theMachine E P I) run (outTape kE) v ∧
      run.time ≤ (3 * kE + 6) * (Cst + 1) ∧
      run.cells ≤ (19 + kE + 1 + 1) * (2 * max S Cb + 3) := by
  obtain ⟨N, C, hbs, hC⟩ := h
  have hN := BigStep.steps_le_cost hbs
  obtain ⟨run, -, htime, hcells, htapes⟩ := oracle_sprog_completed E (stdRegEmb 19 kE)
    (stdEngEmb 19 kE) (stdRegEmb_zero 19 kE) (std_disjoint 19 kE) O
    hE (mainProg P I) hbs trivial rfl hbs.inv_end
  refine ⟨run, ?_, ?_, hcells⟩
  · have hin : (theMachine E P I).inputSymbol = RegSyms.sym :=
      oGadget_input E (stdEngEmb 19 kE) _
    unfold Outputs
    rw [htapes rOUT, hout, hin]
  · have h1 : (oracleSem O (19 + 1) fun _ => True).cost
        (mainProg P I).final u = 1 := rfl
    rw [h1] at htime
    have h2 : (3 * kE + 5) * (C + 1) ≤ (3 * kE + 5) * (Cst + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h3 : (3 * kE + 6) * (Cst + 1) = (3 * kE + 5) * (Cst + 1) + (Cst + 1) := by ring
    omega

end QecReliability.Assembly
end
