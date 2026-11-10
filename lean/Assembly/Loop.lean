import Assembly.Body

/-!
# Assembly.Loop: the main loop along a controller trace

`loop_trace`: if every controller edge from a "good" state is simulated by one run of the
loop body (state register `(vals s).bits`, flag register `isDone`), then the main loop
simulates the whole trace to the terminal state, with cost
`≤ (dispatches + 1)·(K + 1) + oracleTime` where `K` bounds one iteration without SAT time.
-/

set_option autoImplicit false

noncomputable section
namespace QecReliability.Assembly
open RegMachine Interp FL Function
open OracleCost OracleCost.WholeWrapperCandidate

/-! ## Controller facts -/

section Controller
variable {q r B m : ℕ} {shape : Bool} {ext : External}

theorem step_eq_none_of_done {s : Config} (h : s.pc = .done) :
    step q r B m shape ext s = none := by
  simp [WholeWrapperCandidate.step, h]

theorem pc_ne_done_of_step {s : Config} {e : Edge} (he : step q r B m shape ext s = some e) :
    s.pc ≠ .done := fun h => by rw [step_eq_none_of_done h] at he; cases he

theorem reachable_next {s : Config} {e : Edge} (hs : Reachable q r B m shape ext s)
    (he : step q r B m shape ext s = some e) : Reachable q r B m shape ext e.next := by
  obtain ⟨T, E, h⟩ := hs
  exact ⟨_, _, Trace.trans h (Trace.cons he (Trace.nil _))⟩

theorem reachable_initial : Reachable q r B m shape ext (initial q r m) :=
  ⟨{}, [], Trace.nil _⟩

/-- The invoke edge charges exactly the reply time. -/
theorem invoke_edge_time {s : Config} {e : Edge} (hpc : s.pc = .invoke)
    (he : step q r B m shape ext s = some e) : e.oracleTime = (ext.sat s.query).time := by
  simp only [WholeWrapperCandidate.step, hpc] at he
  cases he
  rfl

end Controller

/-! ## The loop -/

/-- Loop-head register file of a controller state. -/
abbrev headRegs (v : Val) (done : Bool) : Regs 20 := regsOf v.bits [] (dnBits done) [] []

theorem loop_trace {O : OracleSpec} {S K : ℕ} {P : Program} {I : Indices}
    {q r B m : ℕ} {shape : Bool} {ext : External}
    (vals : Config → Val) (Good : Config → Prop)
    (hgood : ∀ s e, Good s → step q r B m shape ext s = some e → Good e.next)
    (hfit : ∀ s, Good s → Fits S (headRegs (vals s) (decide (s.pc = .done))))
    (hbody : ∀ s e, Good s → step q r B m shape ext s = some e →
      ORuns O S (body P I) (headRegs (vals s) false)
        (headRegs (vals e.next) (decide (e.next.pc = .done))) (K + e.oracleTime))
    {s final : Config} {totals : Totals} {events : List RequestKey}
    (htr : Trace q r B m shape ext s totals events final) (hs : Good s)
    (hfin : final.pc = .done) :
    ORuns O S (mainLoop P I) (headRegs (vals s) (decide (s.pc = .done)))
      (headRegs (vals final) true) ((totals.dispatches + 1) * (K + 1) + totals.oracleTime) := by
  induction htr with
  | nil s =>
      have hf := hfit s hs
      have hd : decide (s.pc = .done) = true := by simp [hfin]
      rw [hd] at hf ⊢
      refine ⟨1, _, Stmt.BigStep.loopF (σ := σO O) hf trivial
        (headIs_eval rDN _ true (by simp)) (by decide) hf, ?_⟩
      simp [σO, oracleSem, OInstr.cost, Instr.cost]
  | @cons s e t totals events he tail ih =>
      have hne := pc_ne_done_of_step he
      have hd : decide (s.pc = .done) = false := by simp [hne]
      have hf := hfit s hs
      rw [hd] at hf ⊢
      obtain ⟨N1, C1, h1, hC1⟩ := hbody s e hs he
      obtain ⟨N2, C2, h2, hC2⟩ := ih (hgood s e hs he) hfin
      refine ⟨_, _, Stmt.BigStep.loopT (σ := σO O) hf trivial
        (headIs_eval rDN _ false (by simp)) h1 h2, ?_⟩
      simp only [σO, oracleSem, OInstr.cost, Instr.cost, Totals.cons]
      nlinarith

end QecReliability.Assembly

end
