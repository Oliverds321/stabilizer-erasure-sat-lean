import ExternalSATHeaderToUnary

/-! Measured construction of a reusable literal-width word. It preserves a parsed
binary variable header and arbitrary query suffix. The width is computed by actual
instructions, not read from semantic metadata. No whole-query machine is asserted. -/
namespace QecReliability.ExternalSATBridge.WidthPreparation

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls

def store (a b c d e : List Bool) : StructuredProgram.State 3 5 :=
  ⟨fun _ => false, ![a, b, c, d, e]⟩

def lengthPorts : Fin 3 → Fin 5 := ![2, 3, 4]
def encodePorts : Fin 3 → Fin 5 := ![3, 2, 4]

theorem lengthPorts_injective : Function.Injective lengthPorts := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [lengthPorts]

theorem encodePorts_injective : Function.Injective encodePorts := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [encodePorts]

theorem length_embed (tail bits a b : List Bool) :
    embedState (id : Fin 3 → Fin 3) lengthPorts (store tail bits [] [] [])
      (⟨CounterConversions.zeroRegs, ![a, b, []]⟩ : StructuredProgram.State 3 3) =
        store tail bits a b [] := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ Function.injective_id lengthPorts_injective
  · intro i; rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; rfl
  · intro i hi
    fin_cases i <;> simp_all [store, lengthPorts, Fin.exists_fin_succ]

theorem encode_embed (tail bits a b : List Bool) :
    embedState (id : Fin 3 → Fin 3) encodePorts (store tail bits [] [] [])
      (CounterConversions.state CounterConversions.zeroRegs a b) = store tail bits b a [] := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ Function.injective_id encodePorts_injective
  · intro i; rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; rfl
  · intro i hi
    fin_cases i <;> simp_all [store, encodePorts, Fin.exists_fin_succ]

abbrev copyProgram : Program 3 5 8 := StackRoutines.copyProgram 1 2 4 0 1

/-- Includes the halt at label7, beyond the library's trace-to-exit cost. -/
theorem copy_trace (tail bits : List Bool) :
    Trace copyProgram (7 * bits.length + 5)
      ((store tail bits [] [] []).withPC (some copyProgram.entry))
      ((store tail bits bits [] []).withPC none) := by
  have ht := StackRoutines.copyProgram_trace (1 : Fin 5) 2 4 (0 : Fin 3) 1
    (by decide) (by decide) (by decide) (by decide)
    (fun _ => false) (![tail, bits, [], [], []] : Fin 5 → List Bool) rfl
  have hh := StackRoutines.halt_after_trace copyProgram ht 7 rfl rfl
  have hregs : readRegs (fun _ : Fin 3 => false) 0 1 none = (fun _ => false) := by
    funext i
    fin_cases i <;> simp [readRegs]
  have hstacks : StackRoutines.copyStacks (1 : Fin 5) 2
      (![tail, bits, [], [], []] : Fin 5 → List Bool) = ![tail, bits, bits, [], []] := by
    funext i
    fin_cases i <;> simp [StackRoutines.copyStacks]
  simpa only [StackRoutines.copyResult, hregs, hstacks, store,
    StructuredProgram.State.withPC, Nat.add_assoc,
    show (![tail, bits, [], [], []] : Fin 5 → List Bool) 1 = bits from rfl,
    show (4 : ℕ) + 1 = 5 from rfl] using hh

theorem length_initial (bits : List Bool) :
    BitProgram.initial CounterPrograms.lengthProgram bits =
      ((⟨CounterConversions.zeroRegs, ![bits, [], []]⟩ : StructuredProgram.State 3 3).withPC
        (some CounterPrograms.lengthProgram.entry)) := by
  dsimp only [BitProgram.initial, StructuredProgram.State.withPC]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem length_terminal (bits : List Bool) :
    BitProgram.terminal CounterPrograms.lengthProgram bits =
      ((⟨CounterConversions.zeroRegs, ![[], bits, []]⟩ : StructuredProgram.State 3 3).withPC none) := by
  dsimp only [BitProgram.terminal, StructuredProgram.State.withPC]
  congr 1
  funext i
  fin_cases i <;> rfl

def command : StructuredCalls.Cmd 3 5 :=
  .seq (.call copyProgram)
    (.seq (.call (ProgramLinking.liftProgram CounterPrograms.lengthProgram id lengthPorts))
      (.call (ProgramLinking.liftProgram CounterConversions.encodeNatProgram id encodePorts)))

noncomputable abbrev program := compiled command 0 2

def timeBound (k : ℕ) : ℕ := 7 * k + 9 + k * (8 * k + 10) + 32 * (k + 1) ^ 2

/-- Actual measured instructions preserve both words and produce encodeNat(k).
Its length is k+1, exactly the polarity-plus-address field width. -/
theorem eval_width (tail bits : List Bool) :
    ∃ steps, steps + 1 ≤ timeBound bits.length ∧
      StructuredCalls.Eval command steps (store tail bits [] [] [])
        (store tail bits (Encoding.encodeNat bits.length) [] []) := by
  have ecopy : StructuredCalls.Eval (.call copyProgram) (7 * bits.length + 5)
      (store tail bits [] [] []) (store tail bits bits [] []) :=
    .call copyProgram (copy_trace tail bits)
  obtain ⟨count, hvalue, hsize, stepsL, hstepsL, traceL⟩ := CounterPrograms.length_correct bits
  rw [length_initial, length_terminal] at traceL
  have elength := eval_call_lifted CounterPrograms.lengthProgram
    (id : Fin 3 → Fin 3) lengthPorts (store tail bits [] [] [])
    Function.injective_id lengthPorts_injective traceL
  rw [length_embed, length_embed] at elength
  obtain ⟨stepsE, hstepsE, traceE⟩ := CounterConversions.encodeNat_runs CounterConversions.zeroRegs count
  have eencode := eval_call_lifted CounterConversions.encodeNatProgram
    (id : Fin 3 → Fin 3) encodePorts (store tail bits [] [] [])
    Function.injective_id encodePorts_injective traceE
  rw [encode_embed, encode_embed, hvalue] at eencode
  refine ⟨7 * bits.length + 5 + (stepsL + stepsE), ?_, ecopy.seq (elength.seq eencode)⟩
  have hE : stepsE ≤ 32 * (bits.length + 1) ^ 2 := by
    simp only [CounterConversions.runtimeBound, hvalue] at hstepsE
    calc
      stepsE ≤ 32 * (bits.length + 1) * (count.length + 1) := hstepsE
      _ ≤ 32 * (bits.length + 1) * (bits.length + 1) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right hsize 1)
      _ = 32 * (bits.length + 1) ^ 2 := by ring
  dsimp only [timeBound]
  omega

theorem source_width (tail bits : List Bool) :
    BitProgram.RunsIn program (timeBound bits.length)
      ((store tail bits [] [] []).withPC (some program.entry))
      ((store tail bits (Encoding.encodeNat bits.length) [] []).withPC none) := by
  obtain ⟨steps, hsteps, he⟩ := eval_width tail bits
  exact ⟨steps + 1, hsteps, compiled_halt_trace he 0 2⟩

noncomputable abbrev primitive := GuardedCompiler.primitive program

theorem primitive_width (tail bits : List Bool) :
    Computation.RunsIn primitive.step (7 * timeBound bits.length)
      (GuardedCompiler.primitiveCfg program ((store tail bits [] [] []).withPC (some program.entry)))
      (GuardedCompiler.primitiveCfg program
        ((store tail bits (Encoding.encodeNat bits.length) [] []).withPC none)) :=
  GuardedCompiler.primitive_execution program (source_width tail bits)

end QecReliability.ExternalSATBridge.WidthPreparation
