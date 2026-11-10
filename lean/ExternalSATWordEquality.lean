import ExternalSATHeaderToUnary

/-! A concrete destructive word-equality subroutine for canonical clause matching.
Both words occupy real stacks; comparison does not call a semantic equality
oracle. The caller must copy words that must be preserved. Stack 2 is an output
stack: the decision is prepended to its arbitrary old contents. Unassigned caller
storage can be framed using the already checked fixed-port lifting theorem.
This is not yet the complete clause matcher or canonical traversal controller.
Source-only pending independent review and the sole runner's check.
-/
namespace QecReliability.ExternalSATBridge.WordEquality

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram

/-- Five Boolean registers, three stacks and eleven fixed control labels. -/
def program : Program 5 3 11 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code := ![.pop 0 0 1 1, .pop 1 2 3 2, .bxor 4 1 3 3,
    .branch 4 7 4, .branch 1 5 10, .bxor 4 0 2 6, .branch 4 7 0,
    .set 4 false 8, .push 2 4 9, .halt, .set 4 true 8]

def registers (a ap b bp tmp : Bool) : Fin 5 → Bool := ![a, ap, b, bp, tmp]

def cfg (pc : Option (Fin 11)) (r : Fin 5 → Bool)
    (left right out : List Bool) : Cfg 5 3 11 :=
  ⟨pc, r, ![left, right, out]⟩

theorem nil_nil_trace (r : Fin 5 → Bool) (out : List Bool) :
    Trace program 8 (cfg (some 0) r [] [] out)
      (cfg none (registers false false false false true) [] [] (true :: out)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, cfg, execInstr,
    registers, readRegs, funext_iff, Fin.forall_fin_succ]

theorem nil_cons_trace (r : Fin 5 → Bool) (b : Bool) (bs out : List Bool) :
    Trace program 7 (cfg (some 0) r [] (b :: bs) out)
      (cfg none (registers false false b true false) [] bs (false :: out)) := by
  apply Computation.Trace.of_iterate
  cases b <;>
    simp [Function.iterate_succ_apply, step, program, cfg, execInstr,
      registers, readRegs, funext_iff, Fin.forall_fin_succ]

theorem cons_nil_trace (r : Fin 5 → Bool) (a : Bool) (as out : List Bool) :
    Trace program 7 (cfg (some 0) r (a :: as) [] out)
      (cfg none (registers a true false false false) as [] (false :: out)) := by
  apply Computation.Trace.of_iterate
  cases a <;>
    simp [Function.iterate_succ_apply, step, program, cfg, execInstr,
      registers, readRegs, funext_iff, Fin.forall_fin_succ]

theorem unequal_head_trace (r : Fin 5 → Bool) (a b : Bool) (hab : a ≠ b)
    (as bs out : List Bool) :
    Trace program 10 (cfg (some 0) r (a :: as) (b :: bs) out)
      (cfg none (registers a true b true false) as bs (false :: out)) := by
  apply Computation.Trace.of_iterate
  cases a <;> cases b <;>
    simp_all [Function.iterate_succ_apply, step, program, cfg, execInstr,
      registers, readRegs, funext_iff, Fin.forall_fin_succ]

theorem equal_head_trace (r : Fin 5 → Bool) (a : Bool) (as bs out : List Bool) :
    Trace program 7 (cfg (some 0) r (a :: as) (a :: bs) out)
      (cfg (some 0) (registers a true a true false) as bs out) := by
  apply Computation.Trace.of_iterate
  cases a <;>
    simp [Function.iterate_succ_apply, step, program, cfg, execInstr,
      registers, readRegs, funext_iff, Fin.forall_fin_succ]

/-- Actual transition trace, a linear bound, and a physical output word.
The two compared stacks are destructive scratch; their remaining suffixes are
not asserted empty after a mismatch. The old output suffix is preserved. -/
theorem compare_trace (left right : List Bool) (r : Fin 5 → Bool) (out : List Bool) :
    ∃ steps final, Trace program steps (cfg (some 0) r left right out) final ∧
      steps ≤ 10 * (left.length + 1) ∧ final.pc = none ∧
      final.stacks 2 = decide (left = right) :: out := by
  induction left generalizing right r with
  | nil =>
    cases right with
    | nil =>
      exact ⟨8, _, nil_nil_trace r out, by simp, rfl, by simp [cfg]⟩
    | cons b bs =>
      exact ⟨7, _, nil_cons_trace r b bs out, by simp, rfl, by simp [cfg]⟩
  | cons a as ih =>
    cases right with
    | nil =>
      refine ⟨7, _, cons_nil_trace r a as out, ?_, rfl, ?_⟩
      · simp only [List.length_cons]; omega
      · simp [cfg]
    | cons b bs =>
      by_cases hab : a = b
      · subst b
        obtain ⟨steps, final, ht, htime, hhalt, hout⟩ :=
          ih bs (registers a true a true false)
        refine ⟨7 + steps, final, (equal_head_trace r a as bs out).trans ht,
          ?_, hhalt, ?_⟩
        · simp only [List.length_cons]; omega
        · simpa using hout
      · refine ⟨10, _, unequal_head_trace r a b hab as bs out, ?_, rfl, ?_⟩
        · simp only [List.length_cons]; omega
        · simp [cfg, hab]

theorem source_run (left right : List Bool) (r : Fin 5 → Bool) (out : List Bool) :
    ∃ final, BitProgram.RunsIn program (10 * (left.length + 1))
      (cfg (some program.entry) r left right out) final ∧ final.pc = none ∧
      final.stacks program.outputStack = decide (left = right) :: out := by
  obtain ⟨steps, final, ht, htime, hhalt, hout⟩ := compare_trace left right r out
  exact ⟨final, ⟨steps, htime, ht⟩, hhalt, hout⟩

noncomputable abbrev primitive := GuardedCompiler.primitive program

/-- The framed comparison lowers to an actual primitive machine. This is
not an initial-single-input claim: the caller supplies both word stacks. -/
theorem primitive_run (left right : List Bool) (r : Fin 5 → Bool) (out : List Bool) :
    ∃ final, Computation.RunsIn primitive.step (70 * (left.length + 1))
      (GuardedCompiler.primitiveCfg program (cfg (some program.entry) r left right out)) final ∧
      final.state = .inl (decide (left = right)) ∧
      final.tapes program.outputStack =
        Turing.Tape.mk₁ (((decide (left = right)) :: out).map some) := by
  obtain ⟨final, hrun, hhalt, hout⟩ := source_run left right r out
  refine ⟨GuardedCompiler.primitiveCfg program final, ?_, ?_, ?_⟩
  · have h := GuardedCompiler.primitive_execution program hrun
    convert h using 1 <;> ring
  · simp [GuardedCompiler.primitive_halted program final hhalt, hout]
  · rw [GuardedCompiler.primitive_tape, hout]

end QecReliability.ExternalSATBridge.WordEquality

#print axioms QecReliability.ExternalSATBridge.WordEquality.compare_trace
#print axioms QecReliability.ExternalSATBridge.WordEquality.primitive_run
