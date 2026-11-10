import ExternalSATHeaderToUnary

/-! Actual finite escape-frame emission into a reversed output accumulator.
Logical output is appended in forward order, while the physical stack stores its
reverse. No scratch stack is required. Whole-CNF emission is not asserted. -/
namespace QecReliability.ExternalSATBridge.FrameEmitter

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram

/-- Pop a data bit, push its true escape marker and then the bit. The empty-input
branch pushes the false terminator, then executes a real halt instruction. -/
def program : Program 2 2 6 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 4, .push 1 1 3,
    .push 1 0 0, .push 1 0 5, .halt]

def regs (top : Option Bool) : Fin 2 → Bool := ![top.getD false, top.isSome]

def cfg (pc : Fin 6) (r : Fin 2 → Bool) (input accumulator : List Bool) : Cfg 2 2 6 :=
  ⟨some pc, r, ![input, accumulator]⟩

def finalCfg (accumulator : List Bool) : Cfg 2 2 6 :=
  ⟨none, regs none, ![[], accumulator]⟩

@[simp] theorem read_regs (r : Fin 2 → Bool) (top : Option Bool) :
    readRegs r 0 1 top = regs top := by
  funext i
  fin_cases i <;> simp [readRegs, regs]

/-- Four instructions, including the terminating push and halt. -/
theorem emit_empty (r : Fin 2 → Bool) (accumulator : List Bool) :
    Trace program 4 (cfg 0 r [] accumulator) (finalCfg (false :: accumulator)) := by
  refine .cons (b := cfg 1 (regs none) [] accumulator) ?_ ?_
  · simp [step, program, cfg, execInstr, regs, HeaderExtractor.regs, funext_iff, Fin.forall_fin_succ]
  · refine .cons (b := cfg 4 (regs none) [] accumulator) ?_ ?_
    · simp [step, program, cfg, execInstr, regs]
    · refine .cons (b := cfg 5 (regs none) [] (false :: accumulator)) ?_ ?_
      · simp [step, program, cfg, execInstr, regs, funext_iff, Fin.forall_fin_succ]
      · refine .cons ?_ (.refl _)
        simp [step, program, cfg, finalCfg, execInstr]

/-- One data bit expands to two physical accumulator cells in four instructions. -/
theorem emit_one (r : Fin 2 → Bool) (b : Bool) (bits accumulator : List Bool) :
    Trace program 4 (cfg 0 r (b :: bits) accumulator)
      (cfg 0 (regs (some b)) bits (b :: true :: accumulator)) := by
  refine .cons (b := cfg 1 (regs (some b)) bits accumulator) ?_ ?_
  · simp [step, program, cfg, execInstr, regs, HeaderExtractor.regs, funext_iff, Fin.forall_fin_succ]
  · refine .cons (b := cfg 2 (regs (some b)) bits accumulator) ?_ ?_
    · simp [step, program, cfg, execInstr, regs]
    · refine .cons (b := cfg 3 (regs (some b)) bits (true :: accumulator)) ?_ ?_
      · simp [step, program, cfg, execInstr, regs, funext_iff, Fin.forall_fin_succ]
      · refine .cons ?_ (.refl _)
        simp [step, program, cfg, execInstr, regs, funext_iff, Fin.forall_fin_succ]

/-- The exact real trace consumes input and prefixes the reversed frame to an
arbitrary physical accumulator. The final false terminator is charged. -/
theorem emit_trace (r : Fin 2 → Bool) (bits accumulator : List Bool) :
    Trace program (4 * bits.length + 4) (cfg 0 r bits accumulator)
      (finalCfg ((Encoding.frame bits).reverse ++ accumulator)) := by
  induction bits generalizing r accumulator with
  | nil => simpa using emit_empty r accumulator
  | cons b bits ih =>
    have hfirst := emit_one r b bits accumulator
    have hrest := ih (regs (some b)) (b :: true :: accumulator)
    have hchain := hfirst.trans hrest
    convert hchain using 1 <;>
      simp [Encoding.frame_cons, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Reading the accumulator in reverse, this is an append of one exact frame.
Repeated calls therefore preserve the intended logical emission order. -/
theorem append_frame_trace (r : Fin 2 → Bool) (bits priorOutput : List Bool) :
    Trace program (4 * bits.length + 4) (cfg 0 r bits priorOutput.reverse)
      (finalCfg ((priorOutput ++ Encoding.frame bits).reverse)) := by
  simpa only [List.reverse_append] using emit_trace r bits priorOutput.reverse

noncomputable abbrev primitive := GuardedCompiler.primitive program

/-- A genuine primitive execution from a framed stack configuration, with exact
specified final data. The caller may embed both ports into a larger controller. -/
theorem primitive_emit (r : Fin 2 → Bool) (bits accumulator : List Bool) :
    Computation.RunsIn primitive.step (7 * (4 * bits.length + 4))
      (GuardedCompiler.primitiveCfg program (cfg 0 r bits accumulator))
      (GuardedCompiler.primitiveCfg program
        (finalCfg ((Encoding.frame bits).reverse ++ accumulator))) :=
  GuardedCompiler.primitive_execution program ⟨_, le_rfl, emit_trace r bits accumulator⟩

end QecReliability.ExternalSATBridge.FrameEmitter
