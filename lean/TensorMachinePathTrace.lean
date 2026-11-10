import TensorMachineTrace

/-! Path-sensitive lowering carries the remaining concrete counting trace into
each callback proof, excluding fault without postulating a global invariant. -/

set_option autoImplicit false
noncomputable section
namespace QecReliability.TensorMachine
open OracleCost OracleCost.WholeWrapperCandidate Trans.Control
open RegMachine Interp FL Function Assembly

theorem boundary_trace_ne_fault {q r B m : ℕ} {shape : Bool} {ext : External}
    {s final : Config} {totals : Totals} {events : List RequestKey}
    (h : Trace q r B m shape ext s totals events final) (hd : final.pc = .endpointZero) :
    s.pc ≠ .fault := by
  intro hf
  cases h with
  | nil => have hh := hf.symm.trans hd; cases hh
  | cons he _ => simp only [WholeWrapperCandidate.step,hf] at he; contradiction

/-- Concrete register-loop execution. The inherited trace stops at the table
boundary; the extra iteration invokes the installed tensor repair and halts. -/
theorem loop_to_repaired_path {O : OracleSpec} {S K : ℕ} {P : FL.Program} {I : Assembly.Indices}
    {q r B m : ℕ} {shape : Bool} {ext : External}
    {boundary : Config}
    (vals : Config → Val) (Good : Config → Prop) (finish : Config → Config)
    (hfinish : ∀ s, (finish s).pc = .done)
    (hgood : ∀ s e, Good s → WholeWrapperCandidate.step q r B m shape ext s = some e →
      Good e.next)
    (hfit : ∀ s, Good s → Fits S (headRegs (vals s) (decide (s.pc = .done))))
    (hbody : ∀ s e, Good s → s.pc ≠ .endpointZero →
      WholeWrapperCandidate.step q r B m shape ext s = some e →
      (∃ totals events, Trace q r B m shape ext e.next totals events boundary) →
      ORuns O S (body P I) (headRegs (vals s) false)
        (headRegs (vals e.next) (decide (e.next.pc = .done))) (K + e.oracleTime))
    (hrepair : Good boundary →
      ORuns O S (body P I) (headRegs (vals boundary) false)
        (headRegs (vals (finish boundary)) true) K)
    {s : Config} {totals : Totals} {events : List RequestKey}
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
    obtain ⟨N1, C1, h1, hC1⟩ := hrepair hs
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
    obtain ⟨N1, C1, h1, hC1⟩ := hbody s e hs (preboundary_head he tail hb) he ⟨_,_,tail⟩
    obtain ⟨N2, C2, h2, hC2⟩ := ih hbody hrepair (hgood s e hs he) hb
    refine ⟨_, _, Stmt.BigStep.loopT (σ := σO O) hf trivial
      (headIs_eval rDN _ false (by simp)) h1 h2, ?_⟩
    simp only [σO, oracleSem, OInstr.cost, Instr.cost, Totals.cons]
    nlinarith

end QecReliability.TensorMachine
end
