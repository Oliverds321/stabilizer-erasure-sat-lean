import RegMachine.Compile
import RegMachine.GadgetsPushFront

/-!
# The basic register machine compiler (phases 1–3)

`basicLib` realizes the basic instruction set `Instr (k+1)` (register `t` = tape `t`)
with time factor `4` inside the window `[-1, S+1]` on every tape, for programs whose
registers never exceed length `S` (`basic_realizes`).

Main theorem `basic_completed`: if the abstract program halts from the input
register file `inputRegs bits` (input in register 0) with abstract cost `C` after `N`
primitive steps and all register lengths `≤ S` throughout, then the compiled
`MultiTape.Machine` has a `Completed` run on `bits` with the same answer,
`time ≤ 4·C + N`, every visited cell of every tape inside `[-1, S+1]`, hence
`cells ≤ (k+1)·(S+3)`, and final tapes `Tape.mk₁ ((t i).map sym)` with heads on 0.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.RegMachine
open QecReliability.OracleCost.MultiTape Turing Function RegSyms

/-- The default register alphabet: `none` is blank, `some b` is bit `b`. -/
instance : RegSyms (Option Bool) := ⟨some, id, fun _ => rfl, rfl⟩

/-- Gadget label types of the basic instructions. -/
def basicL {R : ℕ} : Instr R → Type
  | .clear _ => ClearL
  | .pushBack _ _ => PushL
  | .popFront _ => PopL
  | .append _ _ => AppL
  | .isEmpty _ => Unit
  | .headIs _ _ => Unit
  | .const _ => Unit
  | .pushFront _ _ => PushFL

instance basicL_fintype {R : ℕ} (p : Instr R) : Fintype (basicL p) := by
  cases p <;> (unfold basicL; infer_instance)

variable {k : ℕ} {Γ : Type} [Fintype Γ] [Inhabited Γ] [RegSyms Γ]

/-- Gadget of each basic instruction. -/
def basicGadget : (p : Instr (k + 1)) → Machine k Γ (basicL p)
  | .clear r => clearM r
  | .pushBack r b => pushBackM r b
  | .popFront r => popFrontM r
  | .append d s => appendM d s
  | .isEmpty r => isEmptyM r
  | .headIs r b => headIsM r b
  | .const b => constM b
  | .pushFront r b => pushFrontM r b

/-- The basic gadget library. -/
def basicLib : Library k Γ (Instr (k + 1)) := ⟨basicL, basicL_fintype, basicGadget⟩

theorem basicGadget_input (p : Instr (k + 1)) : (basicGadget (Γ := Γ) p).inputSymbol = sym := by
  cases p <;> rfl

/-- Register `t` is encoded on tape `t`. -/
def regEnc (s : Regs (k + 1)) : Fin (k + 1) → ℤ → Γ := fun t => cellOf (s t)

/-- The space window `[-1, S+1]` on every tape. -/
def window (S : ℕ) : Fin (k + 1) → Set ℤ := fun _ => Set.Icc (-1) (S + 1)

theorem basic_realizes (S : ℕ) :
    Realizes (basicLib (k := k) (Γ := Γ)) (basicSem (k + 1)) regEnc (Fits S) (window S) 4 := by
  intro p s hs hp hs'
  have hW : ∀ t, (0 : ℤ) ∈ window (k := k) S t := fun t => ⟨by omega, by omega⟩
  have hWr : ∀ r : Fin (k + 1), ∀ z : ℤ, -1 ≤ z → z ≤ (s r).length → z ∈ window (k := k) S r :=
    fun r z h1 h2 => ⟨h1, by have := hs r; omega⟩
  cases p with
  | clear r =>
    obtain ⟨hrun, hans⟩ := clear_spec (Γ := Γ) r s hW (hWr r)
    exact ⟨_, ClearL.done, by simp [basicSem, Instr.cost]; omega, hrun, hans⟩
  | pushBack r b =>
    obtain ⟨hrun, hans⟩ := pushBack_spec (Γ := Γ) r b s hW (hWr r)
    exact ⟨_, PushL.done, by simp [basicSem, Instr.cost]; omega, hrun, hans⟩
  | popFront r =>
    obtain ⟨hrun, hans⟩ := popFront_spec (Γ := Γ) r s hW (hWr r)
    exact ⟨_, PopL.done, by simp [basicSem, Instr.cost]; omega, hrun, hans⟩
  | append d r =>
    have hdr : d ≠ r := hp
    have hlen : (s d).length + (s r).length ≤ S := by
      have := hs' d
      simpa [basicSem, Instr.eval] using this
    obtain ⟨hrun, hans⟩ := append_spec (Γ := Γ) hdr s hW
      (fun z h1 h2 => ⟨h1, by omega⟩) (hWr r)
    exact ⟨_, AppL.done, by simp [basicSem, Instr.cost]; omega, hrun, hans⟩
  | isEmpty r =>
    exact ⟨0, (), by omega, nf_run_zero _ () s hW, isEmpty_answer r s⟩
  | headIs r b =>
    exact ⟨0, (), by omega, nf_run_zero _ () s hW, headIs_answer r b s⟩
  | const b =>
    exact ⟨0, (), by omega, nf_run_zero _ () s hW, const_answer b s⟩
  | pushFront r b =>
    obtain ⟨hrun, hans⟩ := pushFront_spec (Γ := Γ) r b s hW (hWr r)
    exact ⟨_, PushFL.done, by simp [basicSem, Instr.cost]; omega, hrun, hans⟩

/-- The compiled machine of a basic program. -/
abbrev basicMachine {n : ℕ} (prog : Prog (Instr (k + 1)) n) :
    Machine k Γ (CLabel (basicLib (k := k) (Γ := Γ)) prog) :=
  compile basicLib prog

theorem basic_initial_nth {n : ℕ} (prog : Prog (Instr (k + 1)) n) (bits : List Bool)
    (i : Fin (k + 1)) (z : ℤ) :
    (((basicMachine (Γ := Γ) prog).initial bits).tapes i).nth z =
      regEnc (inputRegs bits) i z := by
  have hin : (basicMachine (Γ := Γ) prog).inputSymbol = sym :=
    basicGadget_input (prog.prim prog.entry)
  by_cases hi : i = 0
  · subst hi
    simp only [Machine.initial, if_true, hin, nth_mk₁_map, regEnc, inputRegs]
  · simp [Machine.initial, hi, regEnc, inputRegs]

theorem initial_visited_window {Λ : Type} [Fintype Λ] (M : Machine k Γ Λ) (bits : List Bool)
    (S : ℕ) (hb : bits.length ≤ S) (i : Fin (k + 1)) :
    ↑((initialObserved M bits).visited i) ⊆ window (k := k) S i := by
  intro x hx
  by_cases hi : i = 0
  · subst hi
    simp only [initialObserved, if_true, Finset.coe_insert, Finset.coe_image, Finset.coe_range,
      Set.mem_insert_iff, Set.mem_image, Set.mem_Iio] at hx
    rcases hx with hx | ⟨j, hj, rfl⟩
    · subst hx; exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  · simp only [initialObserved, hi, if_false, Finset.coe_singleton, Set.mem_singleton_iff] at hx
    subst hx; exact ⟨by omega, by omega⟩

/-- **Main theorem.** A halting abstract run of a basic program (all register
lengths `≤ S`) is realized by an actual completed run of the compiled machine on the
input bits: same answer, `time ≤ 4·C + N`, visited cells of every tape inside
`[-1, S+1]`, so `cells ≤ (k+1)·(S+3)`, and the final tapes are the normal form of the
final registers. -/
theorem basic_completed {n S : ℕ} (prog : Prog (Instr (k + 1)) n) {bits : List Bool} {N C : ℕ}
    {t : Regs (k + 1)} {b : Bool}
    (h : Exec (basicSem (k + 1)) prog (Fits S) prog.entry (inputRegs bits) N C t b) :
    ∃ run : Completed (basicMachine (Γ := Γ) prog) bits,
      run.output = b ∧ run.time ≤ 4 * C + N ∧ run.cells ≤ (k + 1) * (S + 3) ∧
      (∀ i, ↑(run.final.visited i) ⊆ Set.Icc (-1 : ℤ) (S + 1)) ∧
      (∀ i, run.final.core.tapes i = Tape.mk₁ ((t i).map sym)) ∧
      run.final.position = fun _ => 0 := by
  have hb : bits.length ≤ S := by
    have := h.inv_start 0
    simpa [inputRegs] using this
  obtain ⟨run, hout, htime, hvis, htapes, hpos⟩ :=
    compile_completed (basic_realizes (k := k) (Γ := Γ) S) h bits
      (basic_initial_nth prog bits) (initial_visited_window _ bits S hb)
  refine ⟨run, hout, htime, ?_, hvis, ?_, hpos⟩
  · show visitedCells run.final ≤ _
    apply visitedCells_le_of_window (lo := fun _ => -1) (hi := fun _ => (S : ℤ) + 1) hvis
    intro i
    omega
  · intro i
    apply tape_ext
    intro z
    rw [htapes i z, nth_mk₁_map]
    rfl

end QecReliability.RegMachine
