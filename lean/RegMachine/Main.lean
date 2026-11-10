import RegMachine.Struct
import RegMachine.SATOracle
import RegMachine.Macros

/-!
# Main results for structured register programs

End-to-end statements for structured programs (`SProg`): a big-step run of the body
followed by the final (output) primitive yields a `MultiTape.Completed` run of the
compiled machine on the input bits.

* `basic_sprog_completed`: basic instructions, registers = tapes, alphabet any `RegSyms Γ`.
* `oracle_sprog_completed`: with oracle calls realized by an engine `E`, registers placed
  by `ρ`, engine tapes by `e`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.RegMachine
open QecReliability.OracleCost.MultiTape QecReliability.OracleCost.MultiTape.InjectiveTapeLift
open Turing RegSyms Function

section Basic
variable {k : ℕ} {Γ : Type} [Fintype Γ] [Inhabited Γ] [RegSyms Γ]

/-- Structured basic programs on the multi-tape machine. -/
theorem basic_sprog_completed (sp : SProg (Instr (k + 1))) {S : ℕ} {bits : List Bool} {N C : ℕ}
    {t u : Regs (k + 1)} {b : Bool}
    (h : Stmt.BigStep (basicSem (k + 1)) (Fits S) sp.body (inputRegs bits) N C t)
    (hp : (basicSem (k + 1)).pre sp.final t)
    (he : (basicSem (k + 1)).eval sp.final t = (u, b)) (hu : Fits S u) :
    ∃ run : Completed (basicMachine (Γ := Γ) sp.toProg) bits,
      run.output = b ∧
      run.time ≤ 4 * (C + (basicSem (k + 1)).cost sp.final t) + (N + 1) ∧
      run.cells ≤ (k + 1) * (S + 3) ∧
      (∀ i, run.final.core.tapes i = Tape.mk₁ ((u i).map sym)) := by
  obtain ⟨run, h1, h2, h3, _, h5, _⟩ :=
    basic_completed (Γ := Γ) sp.toProg (sp.exec h h.inv_end hp he hu)
  exact ⟨run, h1, h2, h3, h5⟩

end Basic

section Oracle
variable {k kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]

/-- Structured oracle programs on one multi-tape machine embedding the engine. -/
theorem oracle_sprog_completed {R S Cb : ℕ} (E : Machine kE ΓE ΛE) (ρ : Embedding R k)
    (e : Embedding kE k) (hρ0 : ρ 0 = 0) (hdisj : ∀ r j, ρ r ≠ e j) (O : OracleSpec)
    (hE : ∀ w, O.qok w → ∃ run : Completed E w, run.output = O.oracle w ∧
      run.time + run.cells ≤ O.ocost w ∧ run.cells ≤ Cb)
    (sp : SProg (OInstr (R + 1))) {bits : List Bool} {N C : ℕ} {t u : Regs (R + 1)} {b : Bool}
    (h : Stmt.BigStep (oracleSem O (R + 1) (fun _ => True)) (Fits S) sp.body (inputRegs bits) N C t)
    (hp : (oracleSem O (R + 1) (fun _ => True)).pre sp.final t)
    (he : (oracleSem O (R + 1) (fun _ => True)).eval sp.final t = (u, b)) (hu : Fits S u) :
    ∃ run : Completed (oracleMachine E e (sp.toProg.map ρ)) bits,
      run.output = b ∧
      run.time ≤ (3 * kE + 5) * (C + (oracleSem O (R + 1) (fun _ => True)).cost sp.final t) +
        (N + 1) ∧
      run.cells ≤ (k + 1) * (2 * max S Cb + 3) ∧
      (∀ r, run.final.core.tapes (ρ r) = Tape.mk₁ ((u r).map sym)) := by
  obtain ⟨run, h1, h2, h3, h4, _, _⟩ :=
    oracle_completed E ρ e hρ0 hdisj O hE sp.toProg (sp.exec h h.inv_end hp he hu)
  exact ⟨run, h1, h2, h3, h4⟩

end Oracle

/-! ## End-to-end example -/

/-- Sanity check of the whole pipeline on a looping program: moving the input (register
0) bit by bit into register 1 is a two-tape machine over `Option Bool` that halts with
answer `true`, in time `≤ 4·(|bits|+1)·(4+|bits|) + 4|bits| + …` and with at most
`2·(|bits|+3)` visited cells. -/
theorem moveAll_machine (bits : List Bool) :
    ∃ run : Completed (basicMachine (k := 1) (Γ := Option Bool)
        (SProg.toProg ⟨moveAll (1 : Fin 2) 0, .const true⟩)) bits,
      run.output = true ∧ run.cells ≤ 2 * (bits.length + 3) ∧
      run.final.core.tapes 1 = Tape.mk₁ (bits.map some) := by
  have hne : (1 : Fin 2) ≠ 0 := by decide
  have hs : Fits bits.length (inputRegs (R := 1) bits) := by
    intro r; by_cases hr : r = 0 <;> simp [inputRegs, hr]
  obtain ⟨N, C, hrun, -⟩ := moveAll_run (S := bits.length) hne bits (inputRegs bits)
    (by simp [inputRegs]) hs (by simp [inputRegs])
  set t := update (update (inputRegs (R := 1) bits) 1 (inputRegs (R := 1) bits 1 ++ bits)) 0 []
  have ht : Fits bits.length t := hrun.inv_end
  obtain ⟨run, h1, -, h3, h4⟩ := basic_sprog_completed (Γ := Option Bool)
    ⟨moveAll (1 : Fin 2) 0, .const true⟩ (u := t) (b := true) hrun trivial rfl ht
  refine ⟨run, h1, h3, ?_⟩
  rw [h4 1]
  simp [t, inputRegs]
  rfl

end QecReliability.RegMachine
