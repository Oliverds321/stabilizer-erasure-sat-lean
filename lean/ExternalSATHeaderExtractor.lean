import ExternalSATBinaryToUnary

/-! Actual extraction of one self-delimiting native query header. The rest of
an arbitrary query stream is retained exactly. This finite component is suitable
for subsequent instruction-table linking; whole-CNF normalization is not claimed.
Pending independent review and compiler verification. -/
namespace QecReliability.ExternalSATBridge.HeaderExtractor

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram

/-- Two bit registers, three Boolean stacks, eleven fixed labels. -/
def program : Program 2 3 11 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.pop 0 0 1 1, .branch 0 2 3, .push 1 0 0,
    .pop 1 0 1 4, .branch 1 5 7, .pop 0 0 1 6, .push 2 0 3,
    .pop 2 0 1 8, .branch 1 9 10, .push 1 0 7, .halt]

def regs (top : Option Bool) : Fin 2 → Bool := ![top.getD false, top.isSome]

def cfg (pc : Fin 11) (r : Fin 2 → Bool) (input count output : List Bool) : Cfg 2 3 11 :=
  ⟨some pc, r, ![input, count, output]⟩

def finalCfg (tail bits : List Bool) : Cfg 2 3 11 :=
  ⟨none, regs none, ![tail, bits, []]⟩

@[simp] theorem read_regs (r : Fin 2 → Bool) (top : Option Bool) :
    readRegs r 0 1 top = regs top := by
  funext i
  fin_cases i <;> simp [readRegs, regs]

theorem scan_false (r : Fin 2 → Bool) (tail count out : List Bool) :
    Trace program 2 (cfg 0 r (false :: tail) count out)
      (cfg 3 (regs (some false)) tail count out) := by
  refine .cons (b := cfg 1 (regs (some false)) tail count out) ?_ ?_
  · simp [step, program, cfg, execInstr, funext_iff, Fin.forall_fin_succ]
  · refine .cons ?_ (.refl _)
    simp [step, program, cfg, execInstr, regs]

theorem scan_true (r : Fin 2 → Bool) (tail count out : List Bool) :
    Trace program 3 (cfg 0 r (true :: tail) count out)
      (cfg 0 (regs (some true)) tail (true :: count) out) := by
  refine .cons (b := cfg 1 (regs (some true)) tail count out) ?_ ?_
  · simp [step, program, cfg, execInstr, funext_iff, Fin.forall_fin_succ]
  · refine .cons (b := cfg 2 (regs (some true)) tail count out) ?_ ?_
    · simp [step, program, cfg, execInstr, regs]
    · refine .cons ?_ (.refl _)
      simp [step, program, cfg, execInstr, regs, funext_iff, Fin.forall_fin_succ]

theorem scan_length (k base : ℕ) (r : Fin 2 → Bool) (tail out : List Bool) :
    Trace program (3 * k + 2)
      (cfg 0 r (List.replicate k true ++ false :: tail) (List.replicate base true) out)
      (cfg 3 (regs (some false)) tail (List.replicate (k + base) true) out) := by
  induction k generalizing base r with
  | zero => simpa using scan_false r tail (List.replicate base true) out
  | succ k ih =>
    have hfirst := scan_true r (List.replicate k true ++ false :: tail)
      (List.replicate base true) out
    have hrest := ih (base + 1) (regs (some true))
    have hchain := hfirst.trans (by
      simpa only [List.replicate_succ] using hrest)
    convert hchain using 1 <;>
      simp [List.replicate_succ, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem take_empty (r : Fin 2 → Bool) (tail out : List Bool) :
    Trace program 2 (cfg 3 r tail [] out) (cfg 7 (regs none) tail [] out) := by
  refine .cons (b := cfg 4 (regs none) tail [] out) ?_ ?_
  · simp [step, program, cfg, execInstr, funext_iff, Fin.forall_fin_succ]
  · refine .cons ?_ (.refl _)
    simp [step, program, cfg, execInstr, regs]

theorem take_one (r : Fin 2 → Bool) (b : Bool) (tail count out : List Bool) :
    Trace program 4 (cfg 3 r (b :: tail) (true :: count) out)
      (cfg 3 (regs (some b)) tail count (b :: out)) := by
  refine .cons (b := cfg 4 (regs (some true)) (b :: tail) count out) ?_ ?_
  · simp [step, program, cfg, execInstr, funext_iff, Fin.forall_fin_succ]
  · refine .cons (b := cfg 5 (regs (some true)) (b :: tail) count out) ?_ ?_
    · simp [step, program, cfg, execInstr, regs]
    · refine .cons (b := cfg 6 (regs (some b)) tail count out) ?_ ?_
      · simp [step, program, cfg, execInstr, funext_iff, Fin.forall_fin_succ]
      · refine .cons ?_ (.refl _)
        simp [step, program, cfg, execInstr, regs, funext_iff, Fin.forall_fin_succ]

theorem take_bits (bits : List Bool) (r : Fin 2 → Bool) (tail out : List Bool) :
    Trace program (4 * bits.length + 2)
      (cfg 3 r (bits ++ tail) (List.replicate bits.length true) out)
      (cfg 7 (regs none) tail [] (bits.reverse ++ out)) := by
  induction bits generalizing r out with
  | nil => simpa using take_empty r tail out
  | cons b bits ih =>
    have hfirst := take_one r b (bits ++ tail) (List.replicate bits.length true) out
    have hrest := ih (regs (some b)) (b :: out)
    have hchain := hfirst.trans hrest
    convert hchain using 1 <;>
      simp [List.replicate_succ, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem reverse_finish (bits tail : List Bool) :
    Trace program (3 * bits.length + 3)
      (cfg 7 (regs none) tail [] bits.reverse) (finalCfg tail bits) := by
  have ht := StackRoutines.transfer_trace program 2 1 0 1 7 8 9 10
    (by decide) (by decide) rfl rfl rfl (regs none) ![tail, [], bits.reverse]
  have hstacks : Function.update
      (Function.update (![tail, [], bits.reverse] : Fin 3 → List Bool) 2 []) 1 bits =
        ![tail, bits, []] := by
    funext i
    fin_cases i <;> simp
  have he : Trace program (3 * bits.length + 2)
      (cfg 7 (regs none) tail [] bits.reverse) (cfg 10 (regs none) tail bits []) := by
    simpa [cfg, StackRoutines.transferResult, StackRoutines.transferStacks,
      funext_iff, Fin.forall_fin_succ, hstacks] using ht
  have hhalt := StackRoutines.halt_after_trace program he 10 rfl rfl
  simpa [cfg, finalCfg, Nat.add_assoc] using hhalt

/-- The exact source instruction trace consumes both header framing and its
binary word, preserving the arbitrary tail for the next parser stage. -/
theorem extract_trace (r : Fin 2 → Bool) (bits tail : List Bool) :
    Trace program (10 * bits.length + 7)
      (cfg 0 r (List.replicate bits.length true ++ false :: (bits ++ tail)) [] [])
      (finalCfg tail bits) := by
  have hs := scan_length bits.length 0 r (bits ++ tail) []
  have ht := take_bits bits (regs (some false)) tail []
  have hr := reverse_finish bits tail
  have hs' : Trace program (3 * bits.length + 2)
      (cfg 0 r (List.replicate bits.length true ++ false :: (bits ++ tail)) [] [])
      (cfg 3 (regs (some false)) (bits ++ tail) (List.replicate bits.length true) []) := by
    simpa using hs
  have ht' : Trace program (4 * bits.length + 2)
      (cfg 3 (regs (some false)) (bits ++ tail) (List.replicate bits.length true) [])
      (cfg 7 (regs none) tail [] bits.reverse) := by simpa using ht
  have hall := hs'.trans (ht'.trans hr)
  convert hall using 1 <;> omega

theorem header_trace (r : Fin 2 → Bool) (n : ℕ) (tail : List Bool) :
    Trace program (10 * n.size + 7)
      (cfg 0 r (QueryCodec.natHeader n ++ tail) [] [])
      (finalCfg tail (QueryCodec.word n.size n)) := by
  simpa [QueryCodec.natHeader, List.append_assoc] using
    extract_trace r (QueryCodec.word n.size n) tail

theorem header_initial (input : List Bool) :
    cfg 0 (fun _ => false) input [] [] = BitProgram.initial program input := by
  unfold cfg BitProgram.initial
  congr 1
  funext i
  fin_cases i <;> rfl

noncomputable abbrev primitive := GuardedCompiler.primitive program

/-- A real primitive run preserves the unconsumed query suffix on input tape0
and exposes the parsed binary field on output tape1, within linear header time. -/
theorem header_primitive (n : ℕ) (tail : List Bool) :
    ∃ steps final,
      Computation.Trace primitive.step steps (primitive.init (QueryCodec.natHeader n ++ tail)) final ∧
      steps ≤ 7 * (10 * n.size + 7) ∧
      final.tapes program.inputStack = Turing.Tape.mk₁ (tail.map some) ∧
      final.tapes program.outputStack = Turing.Tape.mk₁ ((QueryCodec.word n.size n).map some) := by
  have ht := header_trace (fun _ => false) n tail
  rw [header_initial] at ht
  have hp := GuardedCompiler.primitive_execution program ⟨_, le_rfl, ht⟩
  rw [GuardedCompiler.primitive_initial] at hp
  obtain ⟨steps, hsteps, htrace⟩ := hp
  refine ⟨steps, GuardedCompiler.primitiveCfg program
    (finalCfg tail (QueryCodec.word n.size n)), htrace, hsteps, ?_, ?_⟩
  · rw [GuardedCompiler.primitive_tape]
    rfl
  · rw [GuardedCompiler.primitive_tape]
    rfl

end QecReliability.ExternalSATBridge.HeaderExtractor
