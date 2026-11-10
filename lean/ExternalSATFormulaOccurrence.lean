import ExternalSATRawClauseMatcher

/-! Real preserved-body copy followed by a presence-driven clause scan.
No runtime list iterator or semantic occurrence test is an instruction.
The finite while loop branches on an actual stack-presence register. -/
namespace QecReliability.ExternalSATBridge.FormulaOccurrence
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls

abbrev clauseRegister : Fin 12 → Fin 14 := fun i => i.castAdd 2
abbrev clauseStack : Fin 10 → Fin 12 := fun i => i.castAdd 2

def regs (occ test : Bool) : Fin 14 → Bool :=
  ![false, false, false, false, false, false, false, false, false, false, false, false, occ, test]
def store (candidate : Fin 3 → List Bool) (input original out : List Bool)
    (occ test : Bool) : StructuredProgram.State 14 12 :=
  ⟨regs occ test, ![candidate 0, candidate 1, candidate 2, [], [], [], [], [], input, out, original, []]⟩
def rawBody (clauses : List (List ℕ)) : List Bool := clauses.flatMap RawClauseMatcher.rawClause

theorem clauseRegister_injective : Function.Injective clauseRegister := by
  intro a b h; apply Fin.ext; exact congrArg (fun x : Fin 14 => x.val) h
theorem clauseStack_injective : Function.Injective clauseStack := by
  intro a b h; apply Fin.ext; exact congrArg (fun x : Fin 12 => x.val) h

theorem clause_embed (candidate : Fin 3 → List Bool) (input original out : List Bool)
    (occ test : Bool) :
    embedState clauseRegister clauseStack (store candidate [] original [] occ test)
      (RawClauseMatcher.store candidate [] input out RawClauseMatcher.noSeen false false false) =
        store candidate input original out occ test := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ clauseRegister_injective clauseStack_injective
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i <;> simp_all [clauseRegister, store, regs, Fin.exists_fin_succ]
  · intro i hi
    fin_cases i <;> simp_all [clauseStack, store, Fin.exists_fin_succ]

def atoms : List (StructuredProgram.Atom 14 12) → StructuredProgram.Cmd 14 12
  | [] => .skip
  | a :: as => .seq (.atom a) (atoms as)
theorem atoms_eval (as : List (StructuredProgram.Atom 14 12))
    (d : StructuredProgram.State 14 12) :
    StructuredProgram.Eval (atoms as) as.length d (as.foldl (fun d a => a.eval d) d) := by
  induction as generalizing d with
  | nil => exact StructuredProgram.Eval.skip d
  | cons a as ih =>
    simpa only [atoms, List.length_cons, List.foldl_cons, Nat.add_comm] using
      (StructuredProgram.Eval.atom a d).seq (ih (a.eval d))
theorem state_ext (a b : StructuredProgram.State 14 12)
    (hr : ∀ i, a.regs i = b.regs i) (hs : ∀ i, a.stacks i = b.stacks i) : a = b := by
  have hr' := funext hr; have hs' := funext hs
  cases a; cases b; simp_all

def gateAtoms : List (StructuredProgram.Atom 14 12) := [.peek 8 0 13, .set 0 false]
theorem gate_eval (candidate : Fin 3 → List Bool) (input original out : List Bool)
    (occ test : Bool) :
    Eval (.base (atoms gateAtoms)) 2 (store candidate input original out occ test)
      (store candidate input original out occ input.head?.isSome) := by
  apply Eval.base
  have h := atoms_eval gateAtoms (store candidate input original out occ test)
  have he : gateAtoms.foldl (fun d a => a.eval d) (store candidate input original out occ test) =
      store candidate input original out occ input.head?.isSome := by
    apply state_ext <;> intro i <;> fin_cases i <;>
      simp [gateAtoms, store, regs, StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs]
  rw [he] at h
  simpa only [show gateAtoms.length = 2 from rfl] using h

def collectAtoms : List (StructuredProgram.Atom 14 12) :=
  [.pop 9 0 1, .bor 12 12 0, .set 0 false, .set 1 false]
theorem collect_eval (candidate : Fin 3 → List Bool) (input original out : List Bool)
    (occ test answer : Bool) :
    Eval (.base (atoms collectAtoms)) 4 (store candidate input original (answer :: out) occ test)
      (store candidate input original out (occ || answer) test) := by
  apply Eval.base
  have h := atoms_eval collectAtoms (store candidate input original (answer :: out) occ test)
  have he : collectAtoms.foldl (fun d a => a.eval d)
      (store candidate input original (answer :: out) occ test) =
      store candidate input original out (occ || answer) test := by
    apply state_ext <;> intro i <;> fin_cases i <;>
      simp [collectAtoms, store, regs, StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs]
  rw [he] at h
  simpa only [show collectAtoms.length = 4 from rfl] using h

noncomputable def body : StructuredCalls.Cmd 14 12 :=
  .seq (.call (ProgramLinking.liftProgram RawClauseMatcher.program clauseRegister clauseStack))
    (.seq (.base (atoms collectAtoms)) (.base (atoms gateAtoms)))

theorem body_eval (candidate : Fin 3 → List Bool) (codes : List ℕ) (hc : codes.length ≤ 3)
    (tail original out : List Bool) (occ test : Bool) :
    ∃ steps, steps ≤ RawClauseMatcher.fieldsCost candidate codes + 38 ∧
      Eval body steps (store candidate (RawClauseMatcher.rawClause codes ++ tail) original out occ test)
        (store candidate tail original out (occ || RawClauseMatcher.clauseResult candidate codes)
          tail.head?.isSome) := by
  obtain ⟨n, hn, ht⟩ := RawClauseMatcher.source_run candidate codes hc tail out
  have ec := eval_call_lifted RawClauseMatcher.program clauseRegister clauseStack
    (store candidate [] original [] occ test) clauseRegister_injective clauseStack_injective ht
  rw [clause_embed, clause_embed] at ec
  exact ⟨n + (4 + 2), by omega, ec.seq ((collect_eval candidate tail original out occ test _).seq
    (gate_eval candidate tail original out _ test))⟩

def scanCost (candidate : Fin 3 → List Bool) (clauses : List (List ℕ)) : ℕ :=
  (clauses.map (fun c => RawClauseMatcher.fieldsCost candidate c + 39)).sum

theorem loop_eval (candidate : Fin 3 → List Bool) (clauses : List (List ℕ))
    (hc : ∀ c ∈ clauses, c.length ≤ 3) (original out : List Bool) (occ : Bool) :
    ∃ steps, steps ≤ scanCost candidate clauses + 1 ∧
      Eval (.while 13 body) steps
        (store candidate (rawBody clauses) original out occ (rawBody clauses).head?.isSome)
        (store candidate [] original out (occ || clauses.any (RawClauseMatcher.clauseResult candidate)) false) := by
  induction clauses generalizing occ with
  | nil =>
    refine ⟨1, by simp [scanCost], ?_⟩
    simpa [rawBody] using
      (Eval.while_false (body := body) (a := store candidate [] original out occ false) rfl)
  | cons c cs ih =>
    have hcc := hc c (by simp)
    have hcs : ∀ d ∈ cs, d.length ≤ 3 := by intro d hd; exact hc d (by simp [hd])
    obtain ⟨n, hn, he⟩ := body_eval candidate c hcc (rawBody cs) original out occ true
    obtain ⟨m, hm, ht⟩ := ih hcs (occ || RawClauseMatcher.clauseResult candidate c)
    have hp : (rawBody (c :: cs)).head?.isSome = true := by
      rfl
    have hw := Eval.while_true (show
      (store candidate (RawClauseMatcher.rawClause c ++ rawBody cs) original out occ true).regs 13 = true from rfl)
      he ht
    refine ⟨n + m + 1, ?_, ?_⟩
    · change n + m + 1 ≤ (RawClauseMatcher.fieldsCost candidate c + 39) +
        scanCost candidate cs + 1
      omega
    · rw [hp]
      simpa only [rawBody, List.flatMap_cons, List.any_cons, Bool.or_assoc] using hw

abbrev copyBody : Program 14 12 8 := StackRoutines.copyProgram 10 8 11 0 1

theorem copy_eval (candidate : Fin 3 → List Bool) (original out : List Bool) :
    Eval (.call copyBody) (7 * original.length + 5)
      (store candidate [] original out false false)
      (store candidate original original out false false) := by
  apply Eval.call
  have h := ListRegisterProgram.copy_run (10 : Fin 12) 8 11 (0 : Fin 14) 1
    (by decide) (by decide) (by decide) (by decide)
    (regs false false)
    (![candidate 0, candidate 1, candidate 2, [], [], [], [], [], [], out, original, []]) rfl
  have hr : readRegs (regs false false) 0 1 none = regs false false := by
    funext i; fin_cases i <;> simp [readRegs, regs]
  have hs : StackRoutines.copyStacks (10 : Fin 12) 8
      (![candidate 0, candidate 1, candidate 2, [], [], [], [], [], [], out, original, []] : Fin 12 → List Bool) =
        ![candidate 0, candidate 1, candidate 2, [], [], [], [], [], original, out, original, []] := by
    funext i; fin_cases i <;> simp [StackRoutines.copyStacks]
  have hl : (![candidate 0, candidate 1, candidate 2, [], [], [], [], [], [], out, original, []] :
      Fin 12 → List Bool) 10 = original := rfl
  simpa only [ListRegisterProgram.Run, store, StructuredProgram.State.withPC, hr, hs, hl] using h

def finishAtoms : List (StructuredProgram.Atom 14 12) := [.push 9 12, .set 12 false]
theorem finish_eval (candidate : Fin 3 → List Bool) (original out : List Bool) (occ : Bool) :
    Eval (.base (atoms finishAtoms)) 2 (store candidate [] original out occ false)
      (store candidate [] original (occ :: out) false false) := by
  apply Eval.base
  have h := atoms_eval finishAtoms (store candidate [] original out occ false)
  have he : finishAtoms.foldl (fun d a => a.eval d) (store candidate [] original out occ false) =
      store candidate [] original (occ :: out) false false := by
    apply state_ext <;> intro i <;> fin_cases i <;>
      simp [finishAtoms, store, regs, StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  rw [he] at h
  simpa only [show finishAtoms.length = 2 from rfl] using h

noncomputable def command : StructuredCalls.Cmd 14 12 :=
  .seq (.call copyBody) (.seq (.base (atoms gateAtoms))
    (.seq (.while 13 body) (.base (atoms finishAtoms))))
noncomputable abbrev program := compiled command 10 9

def timeBound (candidate : Fin 3 → List Bool) (clauses : List (List ℕ)) : ℕ :=
  7 * (rawBody clauses).length + scanCost candidate clauses + 11

theorem eval_formula (candidate : Fin 3 → List Bool) (clauses : List (List ℕ))
    (hc : ∀ c ∈ clauses, c.length ≤ 3) (out : List Bool) :
    ∃ steps, steps + 1 ≤ timeBound candidate clauses ∧
      Eval command steps (store candidate [] (rawBody clauses) out false false)
        (store candidate [] (rawBody clauses)
          (clauses.any (RawClauseMatcher.clauseResult candidate) :: out) false false) := by
  obtain ⟨n, hn, he⟩ := loop_eval candidate clauses hc (rawBody clauses) out false
  have ht := (copy_eval candidate (rawBody clauses) out).seq
    ((gate_eval candidate (rawBody clauses) (rawBody clauses) out false false).seq
      (he.seq (finish_eval candidate (rawBody clauses) out _)))
  refine ⟨7 * (rawBody clauses).length + 5 + (2 + (n + 2)), ?_, ?_⟩
  · dsimp only [timeBound]; omega
  · simpa only [command, Bool.false_or] using ht

theorem source_run (candidate : Fin 3 → List Bool) (clauses : List (List ℕ))
    (hc : ∀ c ∈ clauses, c.length ≤ 3) (out : List Bool) :
    BitProgram.RunsIn program (timeBound candidate clauses)
      ((store candidate [] (rawBody clauses) out false false).withPC (some program.entry))
      ((store candidate [] (rawBody clauses)
        (clauses.any (RawClauseMatcher.clauseResult candidate) :: out) false false).withPC none) := by
  obtain ⟨n, hn, he⟩ := eval_formula candidate clauses hc out
  exact ⟨n + 1, hn, compiled_halt_trace he 10 9⟩
noncomputable abbrev primitive := GuardedCompiler.primitive program

theorem primitive_run (candidate : Fin 3 → List Bool) (clauses : List (List ℕ))
    (hc : ∀ c ∈ clauses, c.length ≤ 3) (out : List Bool) :
    Computation.RunsIn primitive.step (7 * timeBound candidate clauses)
      (GuardedCompiler.primitiveCfg program
        ((store candidate [] (rawBody clauses) out false false).withPC (some program.entry)))
      (GuardedCompiler.primitiveCfg program
        ((store candidate [] (rawBody clauses)
          (clauses.any (RawClauseMatcher.clauseResult candidate) :: out) false false).withPC none)) :=
  GuardedCompiler.primitive_execution program (source_run candidate clauses hc out)

end QecReliability.ExternalSATBridge.FormulaOccurrence
#print axioms QecReliability.ExternalSATBridge.FormulaOccurrence.source_run
#print axioms QecReliability.ExternalSATBridge.FormulaOccurrence.primitive_run
