import TensorMachineProgramSpec
import Assembly.Loop

/-! The tensor machine follows exactly the old counting trace until the first
whole-table boundary, then runs its installed tensor repair once. In particular,
no old scalar endpoint or repair transition is transferred. -/

set_option autoImplicit false

noncomputable section
namespace QecReliability.TensorMachine

open OracleCost OracleCost.WholeWrapperCandidate Trans.Control

/-- The scalar postprocessing suffix cannot return to the counting boundary. -/
theorem late_step {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} {e : Edge} (hl : 15 ≤ pcCode s.pc)
    (he : WholeWrapperCandidate.step q r B m shape ext s = some e) :
    15 ≤ pcCode e.next.pc := by
  cases hp : s.pc <;> simp only [hp, pcCode] at hl
  all_goals try omega
  all_goals simp only [WholeWrapperCandidate.step, hp] at he
  all_goals try contradiction
  all_goals repeat' first
    | (simp only [localEdge, Option.some.injEq] at he; subst e; simp [hp, pcCode])
    | split at he

 theorem late_trace {q r B m : ℕ} {shape : Bool} {ext : External}
    {s t : Config} {totals : Totals} {events : List RequestKey}
    (h : Trace q r B m shape ext s totals events t) (hs : 15 ≤ pcCode s.pc) :
    15 ≤ pcCode t.pc := by
  induction h with
  | nil => exact hs
  | cons he tail ih => exact ih (late_step hs he)

/-- Every genuine edge of a trace ending at the table boundary starts before
that boundary. This discharges the restriction on the compiled-step transfer. -/
theorem preboundary_head {q r B m : ℕ} {shape : Bool} {ext : External}
    {s t : Config} {e : Edge} {totals : Totals} {events : List RequestKey}
    (he : WholeWrapperCandidate.step q r B m shape ext s = some e)
    (tail : Trace q r B m shape ext e.next totals events t)
    (ht : t.pc = .endpointZero) : s.pc ≠ .endpointZero := by
  intro hs
  have hn : e.next.pc = .endpointOne := by
    simp only [WholeWrapperCandidate.step, hs, Option.some.injEq] at he
    subst e
    rfl
  have hlate := late_trace tail (by simp [hn, pcCode])
  simp [ht, pcCode] at hlate

open RegMachine Interp FL Function Assembly

/-- Concrete register-loop execution. The inherited trace stops at the table
boundary; the extra iteration invokes the installed tensor repair and halts. -/
theorem loop_to_repaired {O : OracleSpec} {S K : ℕ} {P : FL.Program} {I : Assembly.Indices}
    {q r B m : ℕ} {shape : Bool} {ext : External}
    (vals : Config → Val) (Good : Config → Prop) (finish : Config → Config)
    (hfinish : ∀ s, (finish s).pc = .done)
    (hgood : ∀ s e, Good s → WholeWrapperCandidate.step q r B m shape ext s = some e →
      Good e.next)
    (hfit : ∀ s, Good s → Fits S (headRegs (vals s) (decide (s.pc = .done))))
    (hbody : ∀ s e, Good s → s.pc ≠ .endpointZero →
      WholeWrapperCandidate.step q r B m shape ext s = some e →
      ORuns O S (body P I) (headRegs (vals s) false)
        (headRegs (vals e.next) (decide (e.next.pc = .done))) (K + e.oracleTime))
    (hrepair : ∀ s, Good s → s.pc = .endpointZero →
      ORuns O S (body P I) (headRegs (vals s) false)
        (headRegs (vals (finish s)) true) K)
    {s boundary : Config} {totals : Totals} {events : List RequestKey}
    (htr : Trace q r B m shape ext s totals events boundary) (hs : Good s)
    (hb : boundary.pc = .endpointZero) :
    ORuns O S (mainLoop P I) (headRegs (vals s) (decide (s.pc = .done)))
      (headRegs (vals (finish boundary)) true)
      ((totals.dispatches + 2) * (K + 1) + totals.oracleTime) := by
  induction htr with
  | nil s =>
    have hd : decide (s.pc = .done) = false := by simp [hb]
    have hf := hfit s hs
    rw [hd] at hf ⊢
    obtain ⟨N1, C1, h1, hC1⟩ := hrepair s hs hb
    have hf' := h1.inv_end
    have h2 := Stmt.BigStep.loopF (σ := σO O)
      (t := .basic (.headIs rDN true)) (pol := false) (body := body P I) hf' trivial
      (headIs_eval rDN _ true (by simp)) (by decide) hf'
    refine ⟨_, _, Stmt.BigStep.loopT (σ := σO O) hf trivial
      (headIs_eval rDN _ false (by simp)) h1 h2, ?_⟩
    simp only [σO, oracleSem, OInstr.cost, Instr.cost]
    nlinarith
  | @cons s e t totals events he tail ih =>
    have hne := pc_ne_done_of_step he
    have hd : decide (s.pc = .done) = false := by simp [hne]
    have hf := hfit s hs
    rw [hd] at hf ⊢
    obtain ⟨N1, C1, h1, hC1⟩ := hbody s e hs (preboundary_head he tail hb) he
    obtain ⟨N2, C2, h2, hC2⟩ := ih (hgood s e hs he) hb
    refine ⟨_, _, Stmt.BigStep.loopT (σ := σO O) hf trivial
      (headIs_eval rDN _ false (by simp)) h1 h2, ?_⟩
    simp only [σO, oracleSem, OInstr.cost, Instr.cost, Totals.cons]
    nlinarith

end QecReliability.TensorMachine
end
