import TensorMachineCallbackRuns

/-! Composition of the actual initializer, counting loop, tensor repair and
output serializer, followed by the existing injective finite-tape compiler. -/

set_option autoImplicit false
noncomputable section
namespace QecReliability.TensorMachine

open FL RegMachine Interp Assembly
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.MultiTape
open Final

/-- A whole register run including the one new repair iteration. -/
theorem register_run {O : OracleSpec} {S M T D K : ℕ} {P : FL.Program} {I : Assembly.Indices}
    {q r B m : ℕ} {shape : Bool} {ext : External}
    (vals : Config → Val) (Good : Config → Prop) (finish : Config → Config)
    (hfinish : ∀ s, (finish s).pc = .done)
    (hgood : ∀ s e, Good s → WholeWrapperCandidate.step q r B m shape ext s = some e → Good e.next)
    (hfit : ∀ s, Good s → Fits S (headRegs (vals s) (decide (s.pc = .done))))
    (hbody : ∀ s e, Good s → s.pc ≠ .endpointZero →
      WholeWrapperCandidate.step q r B m shape ext s = some e →
      ORuns O S (body P I) (headRegs (vals s) false)
        (headRegs (vals e.next) (decide (e.next.pc = .done))) (K + e.oracleTime))
    (hrepair : ∀ s, Good s → s.pc = .endpointZero →
      ORuns O S (body P I) (headRegs (vals s) false) (headRegs (vals (finish s)) true) K)
    {start boundary : Config} {totals : Totals} {events : List RequestKey}
    (htr : Trace q r B m shape ext start totals events boundary) (hs : Good start)
    (hb : boundary.pc = .endpointZero) (bits word : List Bool)
    (hS : stBound P I M D + (FL.Program.enc P).size + 2 ≤ S) (hm : 2 * M + 4 ≤ S)
    (hinit : FL.Computes P I.init (bitsVal bits) (vals start) M T D)
    (hdone : FL.Computes P I.isDone (vals start) (Enc.bool (decide (start.pc = .done))) M T D)
    (hout : FL.Computes P I.output (vals (finish boundary)) (bitsVal word) M T D) :
    ∃ u : Regs 20,
      ORuns O S (mainProg P I).body (inputRegs (R := 19) bits) u
        (preCost P I S M T D + (totals.dispatches + 2) * (K + 1) +
          totals.oracleTime + postCost P I S M T D) ∧ u rOUT = word := by
  have hpre := preamble_run (O := O) hS hm hinit hdone
  have hloop := loop_to_repaired vals Good finish hfinish hgood hfit hbody hrepair htr hs hb
  have hpost := postamble_run (O := O) hS hout hloop.fits_end
  exact ⟨_, (hpre.seq (hloop.seq hpost)).mono (by omega), rfl⟩

/-- The fixed finite-tape machine executes that register run, including SAT on
its disjoint embedded tapes, with explicit compiler overhead. -/
theorem tape_run {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    {E : Machine kE ΓE ΛE} {density : ℕ} {PtE PsE : PolynomialEnvelope} {timeE : ℕ → ℕ}
    (spec : EncodedSAT E density PtE PsE timeE) {P : FL.Program} {I : Assembly.Indices}
    {Lq S Cost : ℕ} {bits : List Bool} {r : ℕ} {v : RationalOutput.Vector r}
    (h : ∃ u : Regs 20,
      ORuns (satOracle E density Lq) S (mainProg P I).body (inputRegs (R := 19) bits) u Cost ∧
        u rOUT = outputWord v) :
    ∃ run : Completed (theMachine E P I) bits,
      Outputs (theMachine E P I) run (outTape kE) v ∧
      run.time ≤ (3 * kE + 6) * (Cost + 1) ∧
      run.cells ≤ (19 + kE + 1 + 1) * (2 * max S (PsE.eval Lq) + 3) := by
  obtain ⟨u,hr,ho⟩ := h
  exact complete_of_oruns spec hr ho

/-- The numerical degree sum is charged by the explicit grid cardinality,
even when individual degree headers are encoded in binary. -/
theorem sum_add_one_le_slots (ds : List ℕ) : ds.sum + 1 ≤ slots ds := by
  induction ds with
  | nil => simp [slots]
  | cons r ds ih =>
    have hp := slots_pos ds
    simp only [List.sum_cons, slots, List.map_cons, List.prod_cons] at *
    nlinarith

end QecReliability.TensorMachine
end
