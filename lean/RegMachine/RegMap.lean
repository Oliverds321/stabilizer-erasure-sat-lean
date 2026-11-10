import RegMachine.OracleLib

/-!
# Register programs placed on a tape arena (user level)

A program over registers `Fin (R+1)` is placed on the tapes `Fin (k+1)` by an
injective register map `ρ` (with `ρ 0 = 0`, so the input register is the input tape)
disjoint from the engine tapes `e j`. `Prog.map ρ` renames registers; `extRegs ρ s`
is the tape-level register file (non-register tapes empty). `exec_map` transports
abstract executions, so the tape-level invariants (engine registers empty, queried
registers off the engine) hold automatically.

Main theorem `oracle_completed`: a halting abstract run of an oracle program
(register lengths `≤ S`) is realized by a `Completed` run of
`oracleMachine E e (prog.map ρ)` on the input bits, with the same answer,
`time ≤ (3·kE+5)·C + N`, `cells ≤ (k+1)·(2·max S Cb + 3)`.
`stdRegEmb` / `stdEngEmb` give the canonical layout `k = R + kE + 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.RegMachine
open QecReliability.OracleCost.MultiTape QecReliability.OracleCost.MultiTape.InjectiveTapeLift
open Turing Function RegSyms

/-! ## Renaming registers -/

namespace Instr
variable {R R' : ℕ}

/-- Rename the registers of a basic instruction. -/
def map (f : Fin R → Fin R') : Instr R → Instr R'
  | .clear r => .clear (f r)
  | .pushBack r b => .pushBack (f r) b
  | .popFront r => .popFront (f r)
  | .append d s => .append (f d) (f s)
  | .isEmpty r => .isEmpty (f r)
  | .headIs r b => .headIs (f r) b
  | .const b => .const b
  | .pushFront r b => .pushFront (f r) b

end Instr

/-- Rename the registers of an oracle instruction. -/
def OInstr.map {R R' : ℕ} (f : Fin R → Fin R') : OInstr R → OInstr R'
  | .basic i => .basic (i.map f)
  | .call q => .call (f q)

/-- Rename the registers of a program. -/
def Prog.map {R R' n : ℕ} (f : Fin R → Fin R') (prog : Prog (OInstr R) n) : Prog (OInstr R') n :=
  ⟨prog.entry, fun i => (prog.prim i).map f, prog.next⟩

section Ext
variable {R k kE : ℕ} (ρ : Embedding R k)

/-- Tape-level register file of a register file placed by `ρ`. -/
def extRegs (s : Regs (R + 1)) : Regs (k + 1) := assemble ρ s (fun _ => [])

@[simp] theorem extRegs_image (s : Regs (R + 1)) (r : Fin (R + 1)) : extRegs ρ s (ρ r) = s r := by
  simp [extRegs]

theorem extRegs_outside (s : Regs (R + 1)) {t : Fin (k + 1)} (ht : ∀ r, ρ r ≠ t) :
    extRegs ρ s t = [] := by
  simp [extRegs, assemble_outside ρ _ _ ht]

theorem extRegs_update (s : Regs (R + 1)) (r : Fin (R + 1)) (w : List Bool) :
    extRegs ρ (update s r w) = update (extRegs ρ s) (ρ r) w := by
  simp [extRegs, assemble_update_eng]

theorem fits_extRegs {S : ℕ} {s : Regs (R + 1)} (h : Fits S s) : Fits S (extRegs ρ s) := by
  intro t
  by_cases ht : ∃ r, ρ r = t
  · obtain ⟨r, rfl⟩ := ht; simpa using h r
  · push_neg at ht; simp [extRegs_outside ρ s ht]

theorem extRegs_inputRegs (hρ0 : ρ 0 = 0) (bits : List Bool) :
    extRegs ρ (inputRegs bits) = inputRegs bits := by
  funext t
  by_cases ht : ∃ r, ρ r = t
  · obtain ⟨r, rfl⟩ := ht
    simp only [extRegs_image, inputRegs]
    by_cases hr : r = 0
    · subst hr; simp [hρ0]
    · have : ρ r ≠ 0 := fun h => hr (ρ.injective (h.trans hρ0.symm))
      simp [hr, this]
  · push_neg at ht
    have : t ≠ 0 := fun h => ht 0 (hρ0.trans h.symm)
    simp [extRegs_outside ρ _ ht, inputRegs, this]

variable (O : OracleSpec)

theorem eval_map (p : OInstr (R + 1)) (s : Regs (R + 1)) :
    OInstr.eval O (p.map ρ) (extRegs ρ s) = (extRegs ρ (OInstr.eval O p s).1, (OInstr.eval O p s).2) := by
  cases p with
  | basic i =>
    cases i <;> simp [OInstr.map, Instr.map, OInstr.eval, Instr.eval, extRegs_update]
  | call q => simp [OInstr.map, OInstr.eval]

theorem cost_map (p : OInstr (R + 1)) (s : Regs (R + 1)) :
    OInstr.cost O (p.map ρ) (extRegs ρ s) = OInstr.cost O p s := by
  cases p with
  | basic i => cases i <;> simp [OInstr.map, Instr.map, OInstr.cost, Instr.cost]
  | call q => simp [OInstr.map, OInstr.cost]

theorem pre_map (e : Embedding kE k) (hdisj : ∀ r j, ρ r ≠ e j) (p : OInstr (R + 1))
    (s : Regs (R + 1)) (h : OInstr.pre O (fun _ => True) p s) :
    OInstr.pre O (fun q => ∀ j, e j ≠ q) (p.map ρ) (extRegs ρ s) := by
  cases p with
  | basic i =>
    cases i with
    | append d r =>
      have hdr : d ≠ r := h
      show ρ d ≠ ρ r
      exact fun hh => hdr (ρ.injective hh)
    | _ => trivial
  | call q =>
    refine ⟨?_, fun j hj => hdisj q j hj.symm⟩
    simpa [OInstr.map] using h.1

/-- Abstract executions transport along register placement. -/
theorem exec_map (e : Embedding kE k) (hdisj : ∀ r j, ρ r ≠ e j) {S n : ℕ}
    {prog : Prog (OInstr (R + 1)) n} {i : Fin n} {s t : Regs (R + 1)} {N C : ℕ} {b : Bool}
    (h : Exec (oracleSem O (R + 1) (fun _ => True)) prog (Fits S) i s N C t b) :
    Exec (oracleSem O (k + 1) (fun q => ∀ j, e j ≠ q)) (prog.map ρ) (TapeInv e S) i
      (extRegs ρ s) N C (extRegs ρ t) b := by
  have hinv : ∀ s : Regs (R + 1), Fits S s → TapeInv e S (extRegs ρ s) := fun s hs =>
    ⟨fits_extRegs ρ hs, fun j => extRegs_outside ρ s (fun r => hdisj r j)⟩
  induction h with
  | @halt i s t b hs hp he ht hn =>
    have hc := cost_map ρ O (prog.prim i) s
    have := Exec.halt (σ := oracleSem O (k + 1) (fun q => ∀ j, e j ≠ q)) (prog := prog.map ρ)
      (Inv := TapeInv e S) (i := i) (s := extRegs ρ s) (t := extRegs ρ t) (b := b)
      (hinv s hs) (pre_map ρ O e hdisj _ s hp)
      (by show OInstr.eval O ((prog.prim i).map ρ) (extRegs ρ s) = _
          rw [eval_map]; simp only [oracleSem] at he; rw [he])
      (hinv t ht) hn
    simpa [oracleSem, Prog.map, hc] using this
  | @step i j s s' t b b' N C hs hp he hn _ ih =>
    have hc := cost_map ρ O (prog.prim i) s
    have := Exec.step (σ := oracleSem O (k + 1) (fun q => ∀ j, e j ≠ q)) (prog := prog.map ρ)
      (Inv := TapeInv e S) (i := i) (j := j) (s := extRegs ρ s) (s' := extRegs ρ s')
      (hinv s hs) (pre_map ρ O e hdisj _ s hp)
      (by show OInstr.eval O ((prog.prim i).map ρ) (extRegs ρ s) = _
          rw [eval_map]; simp only [oracleSem] at he; rw [he])
      hn ih
    simpa [oracleSem, Prog.map, hc] using this

end Ext

/-! ## Canonical layout: registers first, then the engine tapes -/

/-- Registers `0..R` on tapes `0..R`. -/
def stdRegEmb (R kE : ℕ) : Embedding R (R + kE + 1) :=
  ⟨fun r => ⟨r.val, by omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩

/-- Engine tape `j` on tape `R + 1 + j`. -/
def stdEngEmb (R kE : ℕ) : Embedding kE (R + kE + 1) :=
  ⟨fun j => ⟨R + 1 + j.val, by omega⟩, fun a b h => Fin.ext (by
    have := congrArg Fin.val h; simp at this; omega)⟩

theorem stdRegEmb_zero (R kE : ℕ) : stdRegEmb R kE 0 = 0 := rfl

theorem std_disjoint (R kE : ℕ) (r : Fin (R + 1)) (j : Fin (kE + 1)) :
    stdRegEmb R kE r ≠ stdEngEmb R kE j := by
  intro h
  have := congrArg Fin.val h
  change r.val = R + 1 + j.val at this
  omega

/-! ## Main theorem -/

variable {k kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]

/-- **Main theorem (user level).** Register programs with oracle calls, compiled to a
single `MultiTape.Machine` embedding the engine `E`: a halting abstract run (register
lengths `≤ S`, all queries allowed by `O.qok`) is realized by an actual completed run on
the input bits with the same answer, `time ≤ (3·kE+5)·C + N` and
`cells ≤ (k+1)·(2·max S Cb + 3)`, where `Cb` bounds the engine's cells on allowed
queries. Final register tapes are in normal form. -/
theorem oracle_completed {R n S Cb : ℕ} (E : Machine kE ΓE ΛE) (ρ : Embedding R k)
    (e : Embedding kE k) (hρ0 : ρ 0 = 0) (hdisj : ∀ r j, ρ r ≠ e j) (O : OracleSpec)
    (hE : ∀ w, O.qok w → ∃ run : Completed E w, run.output = O.oracle w ∧
      run.time + run.cells ≤ O.ocost w ∧ run.cells ≤ Cb)
    (prog : Prog (OInstr (R + 1)) n) {bits : List Bool} {N C : ℕ} {t : Regs (R + 1)} {b : Bool}
    (h : Exec (oracleSem O (R + 1) (fun _ => True)) prog (Fits S) prog.entry (inputRegs bits)
      N C t b) :
    ∃ run : Completed (oracleMachine E e (prog.map ρ)) bits,
      run.output = b ∧ run.time ≤ (3 * kE + 5) * C + N ∧
      run.cells ≤ (k + 1) * (2 * max S Cb + 3) ∧
      (∀ r, run.final.core.tapes (ρ r) = Tape.mk₁ ((t r).map sym)) ∧
      (∀ i, ↑(run.final.visited i) ⊆ oWindow e S Cb i) ∧
      run.final.position = fun _ => 0 := by
  have h' := exec_map ρ O e hdisj h
  rw [extRegs_inputRegs ρ hρ0] at h'
  obtain ⟨run, hout, htime, hcells, hvis, htapes, hpos⟩ :=
    oracle_completed_tapes E e O hE (prog.map ρ) h'
  refine ⟨run, hout, htime, hcells, fun r => ?_, hvis, hpos⟩
  rw [htapes (ρ r), extRegs_image]

end QecReliability.RegMachine
