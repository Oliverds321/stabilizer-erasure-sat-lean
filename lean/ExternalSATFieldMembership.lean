import ExternalSATPreservingEquality

/-! One actual extracted-field membership update against three fixed candidate
ports. No semantic comparison instruction: calls the accepted finite comparator,
pops its real decision bit, updates flags by Boolean instructions, and clears the
field. Candidate words are preserved. This is not a full clause matcher. -/
namespace QecReliability.ExternalSATBridge.FieldMembership

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls

abbrev registerPort : Fin 5 → Fin 10 := fun i => i.castAdd 5
abbrev candidatePort (i : Fin 3) : Fin 8 := i.castAdd 5
abbrev seenPort (i : Fin 3) : Fin 10 := ⟨5 + i.val, by omega⟩
def stackPort (i : Fin 3) : Fin 6 → Fin 8 := ![3, candidatePort i, 4, 5, 6, 7]

def regs (seen : Fin 3 → Bool) (bad found : Bool) : Fin 10 → Bool :=
  ![false, false, false, false, false, seen 0, seen 1, seen 2, bad, found]
def store (candidate : Fin 3 → List Bool) (field : List Bool)
    (seen : Fin 3 → Bool) (bad found : Bool) (decision : List Bool := []) :
    StructuredProgram.State 10 8 :=
  ⟨regs seen bad found, ![candidate 0, candidate 1, candidate 2, field, [], [], decision, []]⟩

theorem registerPort_injective : Function.Injective registerPort := by
  intro a b h; apply Fin.ext; exact congrArg (fun x : Fin 10 => x.val) h

theorem stackPort_injective (i : Fin 3) : Function.Injective (stackPort i) := by
  intro a b h
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp_all [stackPort, candidatePort]

theorem store_ext (a b : StructuredProgram.State 10 8)
    (hr : ∀ j, a.regs j = b.regs j) (hs : ∀ j, a.stacks j = b.stacks j) : a = b := by
  have hr' := funext hr
  have hs' := funext hs
  cases a; cases b; simp_all

/-- Small straight-line fragments still compile to actual bit instructions. -/
def atoms : List (StructuredProgram.Atom 10 8) → StructuredProgram.Cmd 10 8
  | [] => .skip
  | a :: as => .seq (.atom a) (atoms as)

theorem atoms_eval (as : List (StructuredProgram.Atom 10 8))
    (d : StructuredProgram.State 10 8) :
    StructuredProgram.Eval (atoms as) as.length d
      (as.foldl (fun d a => a.eval d) d) := by
  induction as generalizing d with
  | nil => exact StructuredProgram.Eval.skip d
  | cons a as ih =>
    simpa only [atoms, List.length_cons, List.foldl_cons, Nat.add_comm] using
      (StructuredProgram.Eval.atom a d).seq (ih (a.eval d))

theorem compare_embed (i : Fin 3) (candidate : Fin 3 → List Bool) (field : List Bool)
    (seen : Fin 3 → Bool) (bad found : Bool) (out : List Bool) :
    embedState registerPort (stackPort i) (store candidate field seen bad found)
      (PreservingEquality.store PreservingEquality.zeroRegs field (candidate i) [] [] out []) =
      store candidate field seen bad found out := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ registerPort_injective (stackPort_injective i)
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases i <;> fin_cases j <;> rfl
  · intro j hj
    fin_cases j <;> simp_all [registerPort, store, regs, Fin.exists_fin_succ]
  · intro j hj
    fin_cases i <;> fin_cases j <;>
      simp_all [stackPort, candidatePort, store, Fin.exists_fin_succ]

def consume (i : Fin 3) : List (StructuredProgram.Atom 10 8) :=
  [.pop 6 0 1, .bor (seenPort i) (seenPort i) 0, .bor 9 9 0,
    .set 0 false, .set 1 false]

theorem consume_eval (i : Fin 3) (candidate : Fin 3 → List Bool) (field : List Bool)
    (seen : Fin 3 → Bool) (bad found bit : Bool) :
    Eval (.base (atoms (consume i))) 5 (store candidate field seen bad found [bit])
      (store candidate field (Function.update seen i (seen i || bit)) bad (found || bit)) := by
  apply Eval.base
  have h := atoms_eval (consume i) (store candidate field seen bad found [bit])
  have he : (consume i).foldl (fun d a => a.eval d)
      (store candidate field seen bad found [bit]) =
      store candidate field (Function.update seen i (seen i || bit)) bad (found || bit) := by
    apply store_ext <;> intro j <;> fin_cases i <;> fin_cases j <;>
      simp [consume, seenPort, store, regs, StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
        StructuredProgram.State.withPC, execInstr, readRegs]
  rw [he] at h
  simpa only [show (consume i).length = 5 from rfl] using h

noncomputable def slot (i : Fin 3) : StructuredCalls.Cmd 10 8 :=
  .seq (.call (ProgramLinking.liftProgram PreservingEquality.program registerPort (stackPort i)))
    (.base (atoms (consume i)))

theorem slot_eval (i : Fin 3) (candidate : Fin 3 → List Bool) (field : List Bool)
    (seen : Fin 3 → Bool) (bad found : Bool) :
    ∃ steps, steps ≤ PreservingEquality.timeBound field.length (candidate i).length + 5 ∧
      Eval (slot i) steps (store candidate field seen bad found)
        (store candidate field (Function.update seen i (seen i || decide (field = candidate i)))
          bad (found || decide (field = candidate i))) := by
  obtain ⟨n, hn, ht⟩ := PreservingEquality.source_run field (candidate i)
  have ec := eval_call_lifted PreservingEquality.program registerPort (stackPort i)
    (store candidate field seen bad found) registerPort_injective (stackPort_injective i) ht
  rw [compare_embed, compare_embed] at ec
  exact ⟨n + 5, by omega, ec.seq (consume_eval i candidate field seen bad found _)⟩

def finishAtoms : List (StructuredProgram.Atom 10 8) :=
  [.bnot 0 9, .bor 8 8 0, .set 9 false, .set 0 false]
abbrev clearField : Program 10 8 3 := StackRoutines.clearProgram 3 0 1

theorem finish_eval (candidate : Fin 3 → List Bool) (field : List Bool)
    (seen : Fin 3 → Bool) (bad found : Bool) :
    Eval (.base (atoms finishAtoms)) 4 (store candidate field seen bad found)
      (store candidate field seen (bad || !found) false) := by
  apply Eval.base
  have h := atoms_eval finishAtoms (store candidate field seen bad found)
  have he : finishAtoms.foldl (fun d a => a.eval d) (store candidate field seen bad found) =
      store candidate field seen (bad || !found) false := by
    apply store_ext <;> intro j <;> fin_cases j <;>
      simp [finishAtoms, store, regs, StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
        StructuredProgram.State.withPC, execInstr]
  rw [he] at h
  simpa only [show finishAtoms.length = 4 from rfl] using h

theorem clear_eval (candidate : Fin 3 → List Bool) (field : List Bool)
    (seen : Fin 3 → Bool) (bad : Bool) :
    Eval (.call clearField) (2 * field.length + 3)
      (store candidate field seen bad false) (store candidate [] seen bad false) := by
  apply Eval.call
  have h := ListRegisterProgram.clear_run (3 : Fin 8) (0 : Fin 10) 1
    (regs seen bad false) (![candidate 0, candidate 1, candidate 2, field, [], [], [], []])
  have hr : readRegs (regs seen bad false) 0 1 none = regs seen bad false := by
    funext j; fin_cases j <;> simp [readRegs, regs]
  have hs : StackRoutines.clearStacks (3 : Fin 8)
      (![candidate 0, candidate 1, candidate 2, field, [], [], [], []] : Fin 8 → List Bool) =
        ![candidate 0, candidate 1, candidate 2, [], [], [], [], []] := by
    funext j; fin_cases j <;> simp [StackRoutines.clearStacks]
  have hl : (![candidate 0, candidate 1, candidate 2, field, [], [], [], []] :
      Fin 8 → List Bool) 3 = field := rfl
  simpa only [ListRegisterProgram.Run, store, StructuredProgram.State.withPC, hr, hs, hl] using h

noncomputable def command : StructuredCalls.Cmd 10 8 :=
  .seq (slot 0) (.seq (slot 1) (.seq (slot 2)
    (.seq (.base (atoms finishAtoms)) (.call clearField))))
noncomputable abbrev program := compiled command 3 6

def timeBound (candidate : Fin 3 → List Bool) (field : List Bool) : ℕ :=
  59 * field.length + 9 * ((candidate 0).length + (candidate 1).length +
    (candidate 2).length) + 119

def updatedSeen (candidate : Fin 3 → List Bool) (field : List Bool)
    (seen : Fin 3 → Bool) : Fin 3 → Bool := fun i => seen i || decide (field = candidate i)
def updatedBad (candidate : Fin 3 → List Bool) (field : List Bool) (bad : Bool) : Bool :=
  bad || !(decide (field = candidate 0) || decide (field = candidate 1) ||
    decide (field = candidate 2))

theorem eval_membership (candidate : Fin 3 → List Bool) (field : List Bool)
    (seen : Fin 3 → Bool) (bad : Bool) :
    ∃ steps, steps + 1 ≤ timeBound candidate field ∧
      Eval command steps (store candidate field seen bad false)
        (store candidate [] (updatedSeen candidate field seen) (updatedBad candidate field bad) false) := by
  let e : Fin 3 → Bool := fun i => decide (field = candidate i)
  let s0 := Function.update seen 0 (seen 0 || e 0)
  let s1 := Function.update s0 1 (s0 1 || e 1)
  let s2 := Function.update s1 2 (s1 2 || e 2)
  let f0 := false || e 0
  let f1 := f0 || e 1
  let f2 := f1 || e 2
  obtain ⟨n0, hn0, h0⟩ := slot_eval 0 candidate field seen bad false
  obtain ⟨n1, hn1, h1⟩ := slot_eval 1 candidate field s0 bad f0
  obtain ⟨n2, hn2, h2⟩ := slot_eval 2 candidate field s1 bad f1
  have he := h0.seq (h1.seq (h2.seq ((finish_eval candidate field s2 bad f2).seq
    (clear_eval candidate field s2 (bad || !f2)))))
  have hs : s2 = updatedSeen candidate field seen := by
    funext i; fin_cases i <;> simp [s2, s1, s0, e, updatedSeen]
  have hf : (bad || !f2) = updatedBad candidate field bad := by
    simp [f2, f1, f0, e, updatedBad]
  refine ⟨n0 + (n1 + (n2 + (4 + (2 * field.length + 3)))), ?_, ?_⟩
  · dsimp only [PreservingEquality.timeBound] at hn0 hn1 hn2
    dsimp only [timeBound]
    omega
  · change Eval command _ _ (store candidate [] s2 (bad || !f2) false) at he
    rw [hs, hf] at he
    exact he

theorem source_run (candidate : Fin 3 → List Bool) (field : List Bool)
    (seen : Fin 3 → Bool) (bad : Bool) :
    BitProgram.RunsIn program (timeBound candidate field)
      ((store candidate field seen bad false).withPC (some program.entry))
      ((store candidate [] (updatedSeen candidate field seen)
        (updatedBad candidate field bad) false).withPC none) := by
  obtain ⟨n, hn, he⟩ := eval_membership candidate field seen bad
  exact ⟨n + 1, hn, compiled_halt_trace he 3 6⟩

noncomputable abbrev primitive := GuardedCompiler.primitive program

theorem primitive_run (candidate : Fin 3 → List Bool) (field : List Bool)
    (seen : Fin 3 → Bool) (bad : Bool) :
    Computation.RunsIn primitive.step (7 * timeBound candidate field)
      (GuardedCompiler.primitiveCfg program
        ((store candidate field seen bad false).withPC (some program.entry)))
      (GuardedCompiler.primitiveCfg program
        ((store candidate [] (updatedSeen candidate field seen)
          (updatedBad candidate field bad) false).withPC none)) :=
  GuardedCompiler.primitive_execution program (source_run candidate field seen bad)

end QecReliability.ExternalSATBridge.FieldMembership

#print axioms QecReliability.ExternalSATBridge.FieldMembership.source_run
#print axioms QecReliability.ExternalSATBridge.FieldMembership.primitive_run
