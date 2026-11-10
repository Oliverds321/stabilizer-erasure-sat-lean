import ExternalSATWordEquality

/-! Repeatable measured word comparison: two real copies, destructive comparison,
actual cleanup and register reset. Original words are preserved. This supplies
a matching primitive, not the complete canonical-clause membership controller.
All programs are fixed; no semantic equality instruction is introduced.
-/
namespace QecReliability.ExternalSATBridge.PreservingEquality

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls

/-- Stronger endpoint for the already accepted comparison table. -/
theorem compare_residuals (left right : List Bool) (r : Fin 5 → Bool) (out : List Bool) :
    ∃ steps r' a b,
      Trace WordEquality.program steps (WordEquality.cfg (some 0) r left right out)
        (WordEquality.cfg none r' a b (decide (left = right) :: out)) ∧
      steps ≤ 10 * (left.length + 1) ∧ a.length ≤ left.length ∧ b.length ≤ right.length := by
  induction left generalizing right r with
  | nil =>
    cases right with
    | nil =>
      refine ⟨8, WordEquality.registers false false false false true, [], [],
        ?_, by simp, le_rfl, le_rfl⟩
      simpa using WordEquality.nil_nil_trace r out
    | cons b bs =>
      refine ⟨7, WordEquality.registers false false b true false, [], bs,
        ?_, by simp, le_rfl, by simp⟩
      simpa using WordEquality.nil_cons_trace r b bs out
  | cons a as ih =>
    cases right with
    | nil =>
      refine ⟨7, WordEquality.registers a true false false false, as, [],
        ?_, ?_, by simp, le_rfl⟩
      · simpa using WordEquality.cons_nil_trace r a as out
      · simp only [List.length_cons]; omega
    | cons b bs =>
      by_cases hab : a = b
      · subst b
        obtain ⟨steps, r', x, y, ht, htime, hx, hy⟩ :=
          ih bs (WordEquality.registers a true a true false)
        refine ⟨7 + steps, r', x, y, ?_, ?_, ?_, ?_⟩
        · simpa using (WordEquality.equal_head_trace r a as bs out).trans ht
        · simp only [List.length_cons]; omega
        · simp only [List.length_cons]; omega
        · simp only [List.length_cons]; omega
      · refine ⟨10, WordEquality.registers a true b true false, as, bs,
          ?_, ?_, by simp, by simp⟩
        · simpa [hab] using WordEquality.unequal_head_trace r a b hab as bs out
        · simp only [List.length_cons]; omega

def zeroRegs : Fin 5 → Bool := fun _ => false

/-- Originals 0/1; compared copies 2/3; result 4; copy temporary 5. -/
def store (r : Fin 5 → Bool) (a b c d e f : List Bool) : StructuredProgram.State 5 6 :=
  ⟨r, ![a, b, c, d, e, f]⟩

def comparePorts : Fin 3 → Fin 6 := ![2, 3, 4]

theorem comparePorts_injective : Function.Injective comparePorts := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [comparePorts]

theorem compare_embed (r : Fin 5 → Bool) (left right a b out : List Bool) :
    embedState (id : Fin 5 → Fin 5) comparePorts (store zeroRegs left right [] [] [] [])
      (⟨r, ![a, b, out]⟩ : StructuredProgram.State 5 3) =
        store r left right a b out [] := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ Function.injective_id comparePorts_injective
  · intro i; rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi
    exact False.elim (hi ⟨i, rfl⟩)
  · intro i hi
    fin_cases i <;> simp_all [store, comparePorts, Fin.exists_fin_succ]

abbrev copyLeft : Program 5 6 8 := StackRoutines.copyProgram 0 2 5 0 1
abbrev copyRight : Program 5 6 8 := StackRoutines.copyProgram 1 3 5 0 1
abbrev clearLeft : Program 5 6 3 := StackRoutines.clearProgram 2 0 1
abbrev clearRight : Program 5 6 3 := StackRoutines.clearProgram 3 0 1

theorem copy_left_eval (left right : List Bool) :
    Eval (.call copyLeft) (7 * left.length + 5)
      (store zeroRegs left right [] [] [] []) (store zeroRegs left right left [] [] []) := by
  apply Eval.call
  have h := ListRegisterProgram.copy_run (0 : Fin 6) 2 5 (0 : Fin 5) 1
    (by decide) (by decide) (by decide) (by decide)
    zeroRegs (![left, right, [], [], [], []] : Fin 6 → List Bool) rfl
  have hr : readRegs zeroRegs 0 1 none = zeroRegs := by
    funext i; fin_cases i <;> simp [readRegs, zeroRegs]
  have ht : StackRoutines.copyStacks (0 : Fin 6) 2
      (![left, right, [], [], [], []] : Fin 6 → List Bool) =
        ![left, right, left, [], [], []] := by
    funext i; fin_cases i <;> simp [StackRoutines.copyStacks]
  have hl : (![left, right, [], [], [], []] : Fin 6 → List Bool) 0 = left := rfl
  simpa only [ListRegisterProgram.Run, store, StructuredProgram.State.withPC, hr, ht, hl] using h

theorem copy_right_eval (left right : List Bool) :
    Eval (.call copyRight) (7 * right.length + 5)
      (store zeroRegs left right left [] [] []) (store zeroRegs left right left right [] []) := by
  apply Eval.call
  have h := ListRegisterProgram.copy_run (1 : Fin 6) 3 5 (0 : Fin 5) 1
    (by decide) (by decide) (by decide) (by decide)
    zeroRegs (![left, right, left, [], [], []] : Fin 6 → List Bool) rfl
  have hr : readRegs zeroRegs 0 1 none = zeroRegs := by
    funext i; fin_cases i <;> simp [readRegs, zeroRegs]
  have ht : StackRoutines.copyStacks (1 : Fin 6) 3
      (![left, right, left, [], [], []] : Fin 6 → List Bool) =
        ![left, right, left, right, [], []] := by
    funext i; fin_cases i <;> simp [StackRoutines.copyStacks]
  have hl : (![left, right, left, [], [], []] : Fin 6 → List Bool) 1 = right := rfl
  simpa only [ListRegisterProgram.Run, store, StructuredProgram.State.withPC, hr, ht, hl] using h

theorem clear_left_eval (r : Fin 5 → Bool) (left right a b out : List Bool) :
    Eval (.call clearLeft) (2 * a.length + 3) (store r left right a b out [])
      (store (readRegs r 0 1 none) left right [] b out []) := by
  apply Eval.call
  have h := ListRegisterProgram.clear_run (2 : Fin 6) (0 : Fin 5) 1 r
    (![left, right, a, b, out, []] : Fin 6 → List Bool)
  have ht : StackRoutines.clearStacks (2 : Fin 6)
      (![left, right, a, b, out, []] : Fin 6 → List Bool) =
        ![left, right, [], b, out, []] := by
    funext i; fin_cases i <;> simp [StackRoutines.clearStacks]
  have hl : (![left, right, a, b, out, []] : Fin 6 → List Bool) 2 = a := rfl
  simpa only [ListRegisterProgram.Run, store, StructuredProgram.State.withPC, ht, hl] using h

theorem clear_right_eval (r : Fin 5 → Bool) (left right b out : List Bool) :
    Eval (.call clearRight) (2 * b.length + 3) (store r left right [] b out [])
      (store (readRegs r 0 1 none) left right [] [] out []) := by
  apply Eval.call
  have h := ListRegisterProgram.clear_run (3 : Fin 6) (0 : Fin 5) 1 r
    (![left, right, [], b, out, []] : Fin 6 → List Bool)
  have ht : StackRoutines.clearStacks (3 : Fin 6)
      (![left, right, [], b, out, []] : Fin 6 → List Bool) =
        ![left, right, [], [], out, []] := by
    funext i; fin_cases i <;> simp [StackRoutines.clearStacks]
  have hl : (![left, right, [], b, out, []] : Fin 6 → List Bool) 3 = b := rfl
  simpa only [ListRegisterProgram.Run, store, StructuredProgram.State.withPC, ht, hl] using h

def reset : StructuredCalls.Cmd 5 6 := .base
  (.seq (.atom (.set 0 false)) (.seq (.atom (.set 1 false))
    (.seq (.atom (.set 2 false)) (.seq (.atom (.set 3 false)) (.atom (.set 4 false))))))

theorem reset_eval (r : Fin 5 → Bool) (left right out : List Bool) :
    Eval reset 5 (store r left right [] [] out []) (store zeroRegs left right [] [] out []) := by
  apply Eval.base
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 5) false)
      (store r left right [] [] out [])).seq
    ((StructuredProgram.Eval.atom (.set (1 : Fin 5) false) _).seq
      ((StructuredProgram.Eval.atom (.set (2 : Fin 5) false) _).seq
        ((StructuredProgram.Eval.atom (.set (3 : Fin 5) false) _).seq
          (StructuredProgram.Eval.atom (.set (4 : Fin 5) false) _))))
  have hr : Function.update (Function.update (Function.update (Function.update
      (Function.update r 0 false) 1 false) 2 false) 3 false) 4 false = zeroRegs := by
    funext i; fin_cases i <;> simp [zeroRegs]
  simpa only [reset, store, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, hr] using h

def command : StructuredCalls.Cmd 5 6 :=
  .seq (.call copyLeft) (.seq (.call copyRight)
    (.seq (.call (ProgramLinking.liftProgram WordEquality.program id comparePorts))
      (.seq (.call clearLeft) (.seq (.call clearRight) reset))))

noncomputable abbrev program := compiled command 0 4

def timeBound (leftLength rightLength : ℕ) : ℕ := 19 * leftLength + 9 * rightLength + 32

/-- Original words preserved, comparison/copy scratch empty, registers reset,
and exactly one answer bit ready for the caller to inspect. -/
theorem eval_preserving (left right : List Bool) :
    ∃ steps, steps + 1 ≤ timeBound left.length right.length ∧
      Eval command steps (store zeroRegs left right [] [] [] [])
        (store zeroRegs left right [] [] [decide (left = right)] []) := by
  obtain ⟨n, r, a, b, ht, hn, ha, hb⟩ := compare_residuals left right zeroRegs []
  have ht' : Trace WordEquality.program n
      ((⟨zeroRegs, ![left, right, []]⟩ : StructuredProgram.State 5 3).withPC
        (some WordEquality.program.entry))
      ((⟨r, ![a, b, [decide (left = right)]]⟩ : StructuredProgram.State 5 3).withPC none) := by
    simpa only [WordEquality.cfg, StructuredProgram.State.withPC,
      show WordEquality.program.entry = 0 from rfl] using ht
  have ec := eval_call_lifted WordEquality.program (id : Fin 5 → Fin 5) comparePorts
    (store zeroRegs left right [] [] [] []) Function.injective_id comparePorts_injective ht'
  rw [compare_embed, compare_embed] at ec
  have he := (copy_left_eval left right).seq ((copy_right_eval left right).seq
    (ec.seq ((clear_left_eval r left right a b [decide (left = right)]).seq
      ((clear_right_eval (readRegs r 0 1 none) left right b [decide (left = right)]).seq
        (reset_eval _ left right [decide (left = right)])))))
  refine ⟨_, ?_, he⟩
  dsimp only [timeBound]
  omega

theorem source_run (left right : List Bool) :
    BitProgram.RunsIn program (timeBound left.length right.length)
      ((store zeroRegs left right [] [] [] []).withPC (some program.entry))
      ((store zeroRegs left right [] [] [decide (left = right)] []).withPC none) := by
  obtain ⟨steps, hs, he⟩ := eval_preserving left right
  exact ⟨steps + 1, hs, compiled_halt_trace he 0 4⟩

noncomputable abbrev primitive := GuardedCompiler.primitive program

/-- Physical fixed-controller execution from the caller's actual framed state. -/
theorem primitive_run (left right : List Bool) :
    Computation.RunsIn primitive.step (7 * timeBound left.length right.length)
      (GuardedCompiler.primitiveCfg program
        ((store zeroRegs left right [] [] [] []).withPC (some program.entry)))
      (GuardedCompiler.primitiveCfg program
        ((store zeroRegs left right [] [] [decide (left = right)] []).withPC none)) :=
  GuardedCompiler.primitive_execution program (source_run left right)

end QecReliability.ExternalSATBridge.PreservingEquality

#print axioms QecReliability.ExternalSATBridge.PreservingEquality.compare_residuals
#print axioms QecReliability.ExternalSATBridge.PreservingEquality.source_run
#print axioms QecReliability.ExternalSATBridge.PreservingEquality.primitive_run
