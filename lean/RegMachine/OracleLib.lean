import RegMachine.BasicLib
import RegMachine.CallClean

/-!
# Register programs with an oracle call (tape level)

`OInstr R` extends the basic instructions by `call q`: ask the oracle about the
contents of register `q`; the answer is the routing Boolean (the call is a test),
registers are unchanged. `oracleSem O R callOK` gives the abstract semantics for an
`OracleSpec O` (oracle function, abstract cost of a query, and the predicate `qok`
of queries on which the engine is assumed to halt); its cost for `call q` is
`1 + |q| + O.ocost q`.

`oLib E e` realizes this instruction set on the tape arena `Fin (k+1)` (every tape
is a register; engine `E` lives on the tapes `e j`), over the alphabet `Cell ΓE`.

* `oracle_realizes`: if the engine `E` has, on every allowed query `w`, a completed run
  with output `O.oracle w`, `time + cells ≤ O.ocost w` and `cells ≤ Cb`, the library
  realizes `oracleSem` with factor `3·kE + 5`, inside the window `oWindow e S Cb`
  (`[-1, S+1]` on non-engine tapes, `[-(B+1), B+1]` on engine tapes, `B = max S Cb`),
  for the invariant `TapeInv e S` (lengths `≤ S`, engine registers empty).
* `oracle_completed_tapes`: the corresponding `Completed` run of the compiled machine.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.RegMachine
open QecReliability.OracleCost.MultiTape QecReliability.OracleCost.MultiTape.InjectiveTapeLift
open Turing Function RegSyms

/-- An abstract oracle: answers, abstract query cost, and allowed queries. -/
structure OracleSpec where
  oracle : List Bool → Bool
  ocost : List Bool → ℕ
  qok : List Bool → Prop

/-- Basic instructions plus an oracle call on a register. -/
inductive OInstr (R : ℕ) where
  | basic (i : Instr R)
  | call (q : Fin R)

namespace OInstr
variable {R : ℕ} (O : OracleSpec)

/-- Preconditions; `callOK` restricts which registers may be queried. -/
def pre (callOK : Fin R → Prop) : OInstr R → Regs R → Prop
  | .basic i, s => i.pre s
  | .call q, s => O.qok (s q) ∧ callOK q

def eval : OInstr R → Regs R → Regs R × Bool
  | .basic i, s => i.eval s
  | .call q, s => (s, O.oracle (s q))

def cost : OInstr R → Regs R → ℕ
  | .basic i, s => i.cost s
  | .call q, s => 1 + (s q).length + O.ocost (s q)

end OInstr

/-- Semantics of register programs with oracle calls. -/
def oracleSem (O : OracleSpec) (R : ℕ) (callOK : Fin R → Prop) : PrimSem (OInstr R) (Regs R) :=
  ⟨OInstr.pre O callOK, OInstr.eval O, OInstr.cost O⟩

variable {k kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]

/-- Gadget label types. -/
def oL (kE : ℕ) (ΛE : Type) {k : ℕ} : OInstr (k + 1) → Type
  | .basic i => basicL i
  | .call _ => CallL kE ΛE

instance oL_fintype (p : OInstr (k + 1)) : Fintype (oL kE ΛE p) := by
  cases p <;> (unfold oL; infer_instance)

/-- Gadgets: basic gadgets and the call gadget. -/
def oGadget (E : Machine kE ΓE ΛE) (e : Embedding kE k) :
    (p : OInstr (k + 1)) → Machine k (Cell ΓE) (oL kE ΛE p)
  | .basic i => basicGadget i
  | .call q => callM E e q

/-- The gadget library with an engine. -/
def oLib (E : Machine kE ΓE ΛE) (e : Embedding kE k) : Library k (Cell ΓE) (OInstr (k + 1)) :=
  ⟨oL kE ΛE, oL_fintype, oGadget E e⟩

theorem oGadget_input (E : Machine kE ΓE ΛE) (e : Embedding kE k) (p : OInstr (k + 1)) :
    (oGadget E e p).inputSymbol = sym := by
  cases p with
  | basic i => exact basicGadget_input i
  | call q => rfl

/-- Space window: `[-1, S+1]` off the engine, `[-(B+1), B+1]` on engine tapes. -/
def oWindow (e : Embedding kE k) (S Cb : ℕ) : Fin (k + 1) → Set ℤ :=
  assemble e (fun _ => Set.Icc (-((max S Cb : ℕ) + 1 : ℤ)) ((max S Cb : ℕ) + 1))
    (fun _ => Set.Icc (-1) (S + 1))

/-- Tape-level invariant: lengths `≤ S` and empty engine registers. -/
def TapeInv (e : Embedding kE k) (S : ℕ) (s : Regs (k + 1)) : Prop :=
  Fits S s ∧ ∀ j, s (e j) = []

theorem oWindow_sub (e : Embedding kE k) (S Cb : ℕ) (t : Fin (k + 1)) :
    Set.Icc (-1 : ℤ) (S + 1) ⊆ oWindow e S Cb t ∧
      Set.Icc (-((max S Cb : ℕ) + 1 : ℤ)) ((max S Cb : ℕ) + 1) ⊇ oWindow e S Cb t := by
  have hm : S ≤ max S Cb := le_max_left _ _
  by_cases ht : ∃ j, e j = t
  · obtain ⟨j, rfl⟩ := ht
    simp only [oWindow, assemble_image]
    refine ⟨Set.Icc_subset_Icc (by omega) (by omega), le_refl _⟩
  · push_neg at ht
    simp only [oWindow, assemble_outside e _ _ ht]
    refine ⟨le_refl _, Set.Icc_subset_Icc (by omega) (by omega)⟩

theorem oracle_realizes (E : Machine kE ΓE ΛE) (e : Embedding kE k) (O : OracleSpec) (S Cb : ℕ)
    (hE : ∀ w, O.qok w → ∃ run : Completed E w, run.output = O.oracle w ∧
      run.time + run.cells ≤ O.ocost w ∧ run.cells ≤ Cb) :
    Realizes (oLib E e) (oracleSem O (k + 1) (fun q => ∀ j, e j ≠ q)) regEnc (TapeInv e S)
      (oWindow e S Cb) (3 * kE + 5) := by
  intro p s hs hp hs'
  cases p with
  | basic i =>
    obtain ⟨m, q', hm, hrun, hans⟩ :=
      basic_realizes (k := k) (Γ := Cell ΓE) S i s hs.1 hp hs'.1
    refine ⟨m, q', ?_, hrun.mono fun t => (oWindow_sub e S Cb t).1, hans⟩
    have : 4 * (basicSem (k + 1)).cost i s ≤ (3 * kE + 5) * (basicSem (k + 1)).cost i s :=
      Nat.mul_le_mul_right _ (by omega)
    exact hm.trans this
  | call q =>
    obtain ⟨hq, hqe⟩ := hp
    obtain ⟨run, hout, hcost, hcells⟩ := hE (s q) hq
    have hC : run.cells ≤ max S Cb := hcells.trans (le_max_right _ _)
    obtain ⟨m, hm, hrun, hans⟩ := call_spec (E := E) (e := e) (fun j => hqe j) s hs.2 run hC
      (fun t => (oWindow_sub e S Cb t).1 ⟨by omega, by omega⟩)
      (fun z h1 h2 => by
        have hqS := hs.1 q
        have hq' : ∀ j, e j ≠ q := hqe
        simp only [oWindow, assemble_outside e _ _ hq']
        exact ⟨h1, by omega⟩)
      (fun j z h1 h2 => by
        simp only [oWindow, assemble_image]
        exact ⟨h1, h2⟩)
    refine ⟨m, CallL.done run.output, ?_, ?_, ?_⟩
    · show m ≤ (3 * kE + 5) * (1 + (s q).length + O.ocost (s q))
      have h1 : run.time ≤ O.ocost (s q) := by omega
      have h2 : run.cells ≤ O.ocost (s q) := by omega
      have h3 : (kE + 1) * (3 * run.cells + 2) ≤ (kE + 1) * (3 * O.ocost (s q) + 2) :=
        Nat.mul_le_mul_left _ (by omega)
      nlinarith
    · show ARun (callM E e q) _ (nf .init s) m (nf (.done run.output) s)
      exact hrun
    · show aanswer (callM E e q) (nf (.done run.output) s) = some (O.oracle (s q))
      rw [hans, hout]

/-- The compiled machine of a tape-level oracle program. -/
abbrev oracleMachine {n : ℕ} (E : Machine kE ΓE ΛE) (e : Embedding kE k)
    (prog : Prog (OInstr (k + 1)) n) : Machine k (Cell ΓE) (CLabel (oLib E e) prog) :=
  compile (oLib E e) prog

theorem oracle_initial_nth {n : ℕ} (E : Machine kE ΓE ΛE) (e : Embedding kE k)
    (prog : Prog (OInstr (k + 1)) n) (bits : List Bool) (i : Fin (k + 1)) (z : ℤ) :
    (((oracleMachine E e prog).initial bits).tapes i).nth z = regEnc (inputRegs bits) i z := by
  have hin : (oracleMachine E e prog).inputSymbol = sym := oGadget_input E e (prog.prim prog.entry)
  by_cases hi : i = 0
  · subst hi
    simp only [Machine.initial, if_true, hin, nth_mk₁_map, regEnc, inputRegs]
  · simp [Machine.initial, hi, regEnc, inputRegs]

/-- **Main theorem (tape level).** A halting abstract run of a tape-level oracle program
(registers `≤ S`, engine registers empty, queried registers off the engine, every query
allowed) yields a completed run of the compiled machine with the same answer, time
`≤ (3kE+5)·C + N`, visited cells inside `oWindow e S Cb` on every tape, hence
`cells ≤ (k+1)·(2·max S Cb + 3)`, and final tapes in normal form. -/
theorem oracle_completed_tapes {n S Cb : ℕ} (E : Machine kE ΓE ΛE) (e : Embedding kE k)
    (O : OracleSpec)
    (hE : ∀ w, O.qok w → ∃ run : Completed E w, run.output = O.oracle w ∧
      run.time + run.cells ≤ O.ocost w ∧ run.cells ≤ Cb)
    (prog : Prog (OInstr (k + 1)) n) {bits : List Bool} {N C : ℕ} {t : Regs (k + 1)} {b : Bool}
    (h : Exec (oracleSem O (k + 1) (fun q => ∀ j, e j ≠ q)) prog (TapeInv e S) prog.entry
      (inputRegs bits) N C t b) :
    ∃ run : Completed (oracleMachine E e prog) bits,
      run.output = b ∧ run.time ≤ (3 * kE + 5) * C + N ∧
      run.cells ≤ (k + 1) * (2 * max S Cb + 3) ∧
      (∀ i, ↑(run.final.visited i) ⊆ oWindow e S Cb i) ∧
      (∀ i, run.final.core.tapes i = Tape.mk₁ ((t i).map sym)) ∧
      run.final.position = fun _ => 0 := by
  have hb : bits.length ≤ S := by
    have := h.inv_start.1 0
    simpa [inputRegs] using this
  have hvis : ∀ i, ↑((initialObserved (oracleMachine E e prog) bits).visited i) ⊆
      oWindow e S Cb i := fun i =>
    (initial_visited_window _ bits S hb i).trans (oWindow_sub e S Cb i).1
  obtain ⟨run, hout, htime, hv, htapes, hpos⟩ :=
    compile_completed (oracle_realizes E e O S Cb hE) h bits (oracle_initial_nth E e prog bits) hvis
  refine ⟨run, hout, htime, ?_, hv, ?_, hpos⟩
  · show visitedCells run.final ≤ _
    apply visitedCells_le_of_window (lo := fun _ => -((max S Cb : ℕ) + 1 : ℤ))
      (hi := fun _ => ((max S Cb : ℕ) + 1 : ℤ)) (fun i => (hv i).trans (oWindow_sub e S Cb i).2)
    intro i
    omega
  · intro i
    apply tape_ext
    intro z
    rw [htapes i z, nth_mk₁_map]
    rfl

end QecReliability.RegMachine
