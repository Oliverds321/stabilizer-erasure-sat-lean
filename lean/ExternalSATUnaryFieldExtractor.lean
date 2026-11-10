import ExternalSATHeaderExtractor

/-! A real finite program extracting one external unary natural field from a
raw clause stream. The terminator is consumed, the following input is retained,
and the exact field is prepended to an arbitrary output suffix. No metadata
provides the field length: the actual input bits control the loop.
-/
namespace QecReliability.ExternalSATBridge.UnaryFieldExtractor

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram

/-- Two Boolean registers, two stacks, seven fixed labels. -/
def program : Program 2 2 7 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.set 0 false 1, .push 1 0 2, .pop 0 0 1 3,
    .branch 0 4 5, .push 1 0 2, .set 1 false 6, .halt]

def regs (value present : Bool) : Fin 2 → Bool := ![value, present]

def cfg (pc : Option (Fin 7)) (r : Fin 2 → Bool) (input out : List Bool) : Cfg 2 2 7 :=
  ⟨pc, r, ![input, out]⟩

theorem initialize_trace (r : Fin 2 → Bool) (input out : List Bool) :
    Trace program 2 (cfg (some 0) r input out)
      (cfg (some 2) (Function.update r 0 false) input (false :: out)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, cfg, execInstr,
    readRegs, HeaderExtractor.regs, funext_iff, Fin.forall_fin_succ]

theorem true_trace (r : Fin 2 → Bool) (input out : List Bool) :
    Trace program 3 (cfg (some 2) r (true :: input) out)
      (cfg (some 2) (regs true true) input (true :: out)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, cfg, execInstr,
    regs, readRegs, HeaderExtractor.regs, funext_iff, Fin.forall_fin_succ]

theorem false_trace (r : Fin 2 → Bool) (tail out : List Bool) :
    Trace program 4 (cfg (some 2) r (false :: tail) out)
      (cfg none (regs false false) tail out) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, cfg, execInstr,
    regs, readRegs, HeaderExtractor.regs, funext_iff, Fin.forall_fin_succ]

theorem replicate_tail (n : ℕ) (out : List Bool) :
    List.replicate n true ++ true :: out = List.replicate (n + 1) true ++ out := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons true) ih

theorem loop_trace (n : ℕ) (r : Fin 2 → Bool) (tail out : List Bool) :
    Trace program (3 * n + 4)
      (cfg (some 2) r (List.replicate n true ++ false :: tail) out)
      (cfg none (regs false false) tail (List.replicate n true ++ out)) := by
  induction n generalizing r out with
  | zero => simpa using false_trace r tail out
  | succ n ih =>
    have ht := true_trace r (List.replicate n true ++ false :: tail) out
    have hr := ih (regs true true) (true :: out)
    have hall := ht.trans hr
    have htime : 3 + (3 * n + 4) = 3 * (n + 1) + 4 := by omega
    rw [htime, replicate_tail] at hall
    simpa only [List.replicate_succ, List.cons_append] using hall

/-- Exact source transitions include the halt and leave both registers false. -/
theorem field_trace (n : ℕ) (r : Fin 2 → Bool) (tail out : List Bool) :
    Trace program (3 * n + 6)
      (cfg (some program.entry) r (Encoding.encodeNat n ++ tail) out)
      (cfg none (regs false false) tail (Encoding.encodeNat n ++ out)) := by
  have hi := initialize_trace r (Encoding.encodeNat n ++ tail) out
  have hl := loop_trace n (Function.update r 0 false) tail (false :: out)
  have hl' : Trace program (3 * n + 4)
      (cfg (some 2) (Function.update r 0 false) (Encoding.encodeNat n ++ tail) (false :: out))
      (cfg none (regs false false) tail (Encoding.encodeNat n ++ out)) := by
    simpa [Encoding.encodeNat, List.append_assoc] using hl
  have hall := hi.trans hl'
  have htime : 2 + (3 * n + 4) = 3 * n + 6 := by omega
  simpa only [htime, show program.entry = 0 from rfl] using hall

theorem source_run (n : ℕ) (r : Fin 2 → Bool) (tail out : List Bool) :
    BitProgram.RunsIn program (3 * n + 6)
      ((⟨r, ![Encoding.encodeNat n ++ tail, out]⟩ : StructuredProgram.State 2 2).withPC
        (some program.entry))
      ((⟨regs false false, ![tail, Encoding.encodeNat n ++ out]⟩ :
        StructuredProgram.State 2 2).withPC none) := by
  exact ⟨3 * n + 6, le_rfl, field_trace n r tail out⟩

noncomputable abbrev primitive := GuardedCompiler.primitive program

/-- Actual physical suffix-preserving extraction from the caller's framed state.
Neither a pre-isolated word nor a supplied width/countdown is required. -/
theorem primitive_run (n : ℕ) (r : Fin 2 → Bool) (tail out : List Bool) :
    ∃ final, Computation.RunsIn primitive.step (7 * (3 * n + 6))
      (GuardedCompiler.primitiveCfg program
        ((⟨r, ![Encoding.encodeNat n ++ tail, out]⟩ : StructuredProgram.State 2 2).withPC
          (some program.entry))) final ∧
      final.tapes program.inputStack = Turing.Tape.mk₁ (tail.map some) ∧
      final.tapes program.outputStack = Turing.Tape.mk₁ ((Encoding.encodeNat n ++ out).map some) := by
  refine ⟨GuardedCompiler.primitiveCfg program
    ((⟨regs false false, ![tail, Encoding.encodeNat n ++ out]⟩ :
      StructuredProgram.State 2 2).withPC none),
    GuardedCompiler.primitive_execution program (source_run n r tail out), ?_, ?_⟩
  · simp [GuardedCompiler.primitive_tape, program, StructuredProgram.State.withPC]
  · simp [GuardedCompiler.primitive_tape, program, StructuredProgram.State.withPC]

end QecReliability.ExternalSATBridge.UnaryFieldExtractor

#print axioms QecReliability.ExternalSATBridge.UnaryFieldExtractor.field_trace
#print axioms QecReliability.ExternalSATBridge.UnaryFieldExtractor.source_run
#print axioms QecReliability.ExternalSATBridge.UnaryFieldExtractor.primitive_run
