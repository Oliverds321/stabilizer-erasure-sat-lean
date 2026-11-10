import ExternalSATHeaderExtractor

/-! Suffix-preserving composition of two actual finite instruction tables.
The first native self-delimiting natural field becomes external unary encoding;
the rest of the query remains on stack zero. This is not whole-CNF lowering. -/
namespace QecReliability.ExternalSATBridge.HeaderToUnary

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredProgram StructuredCalls

abbrev headerRegister : Fin 2 → Fin 3 := fun i => i.castAdd 1
abbrev headerStack : Fin 3 → Fin 4 := fun i => i.castAdd 1
abbrev counterStack : Fin 3 → Fin 4 := Fin.succ

def store (a b c d : List Bool) : StructuredProgram.State 3 4 :=
  ⟨fun _ => false, ![a, b, c, d]⟩

theorem headerRegister_injective : Function.Injective headerRegister := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin 3 => x.val) h

theorem headerStack_injective : Function.Injective headerStack := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin 4 => x.val) h

theorem counterStack_injective : Function.Injective counterStack := by
  intro a b h
  apply Fin.ext
  have := congrArg (fun x : Fin 4 => x.val) h
  simpa using this

/-- Portwise equality, including genuinely unassigned caller storage. -/
theorem embed_eq {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : StructuredProgram.State R S) (d : StructuredProgram.State r s) (target : StructuredProgram.State R S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (hreg : ∀ i, d.regs i = target.regs (register i))
    (hstack : ∀ i, d.stacks i = target.stacks (stack i))
    (hregFrame : ∀ i, (¬ ∃ j, register j = i) → frame.regs i = target.regs i)
    (hstackFrame : ∀ i, (¬ ∃ j, stack j = i) → frame.stacks i = target.stacks i) :
    embedState register stack frame d = target := by
  have hregs : (embedState register stack frame d).regs = target.regs := by
    funext i
    by_cases hi : ∃ j, register j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedState_register register stack frame d hr j).trans (hreg j)
    · exact (embedState_register_frame register stack frame d i hi).trans (hregFrame i hi)
  have hstacks : (embedState register stack frame d).stacks = target.stacks := by
    funext i
    by_cases hi : ∃ j, stack j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedState_stack register stack frame d hs j).trans (hstack j)
    · exact (embedState_stack_frame register stack frame d i hi).trans (hstackFrame i hi)
  cases he : embedState register stack frame d
  cases target
  simp_all

theorem header_embed (a b c : List Bool) :
    embedState headerRegister headerStack (store [] [] [] [])
      (⟨fun _ => false, ![a, b, c]⟩ : StructuredProgram.State 2 3) = store a b c [] := by
  apply embed_eq _ _ _ _ _ headerRegister_injective headerStack_injective
  · intro i; rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; rfl
  · intro i hi
    fin_cases i <;> simp_all [store, headerStack, Fin.exists_fin_succ]

theorem counter_embed (tail a b : List Bool) :
    embedState (id : Fin 3 → Fin 3) counterStack (store tail [] [] [])
      (CounterConversions.state CounterConversions.zeroRegs a b) = store tail a b [] := by
  apply embed_eq _ _ _ _ _ Function.injective_id counterStack_injective
  · intro i; rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; rfl
  · intro i hi
    fin_cases i <;> simp_all [store, counterStack, Fin.exists_fin_succ]

def command : StructuredCalls.Cmd 3 4 :=
  .seq (.call (ProgramLinking.liftProgram HeaderExtractor.program headerRegister headerStack))
    (.call (ProgramLinking.liftProgram CounterConversions.encodeNatProgram id counterStack))

noncomputable abbrev program := StructuredCalls.compiled command 0 2

/-- Exact source trace counts compose; the conversion bound is an upper bound,
not an assertion that every binary value takes the same number of steps. -/
theorem eval_header (n : ℕ) (tail : List Bool) :
    ∃ steps, steps ≤ 10 * n.size + 7 + 32 * (n + 1) * (n.size + 1) ∧
      StructuredCalls.Eval command steps
        (store (QueryCodec.natHeader n ++ tail) [] [] [])
        (store tail [] (Encoding.encodeNat n) []) := by
  have hv := PrimitiveTransport.binary_word_value n.size n (Nat.lt_size_self n)
  have hh := HeaderExtractor.header_trace (fun _ => false) n tail
  have hh' : Trace HeaderExtractor.program (10 * n.size + 7)
      ((⟨fun _ => false, ![QueryCodec.natHeader n ++ tail, [], []]⟩ : StructuredProgram.State 2 3).withPC
        (some HeaderExtractor.program.entry))
      ((⟨fun _ => false, ![tail, QueryCodec.word n.size n, []]⟩ : StructuredProgram.State 2 3).withPC none) := by
    have hr : HeaderExtractor.regs none = (fun _ => false) := by
      funext i
      fin_cases i <;> rfl
    simpa only [HeaderExtractor.cfg, HeaderExtractor.finalCfg, hr,
      StructuredProgram.State.withPC, show HeaderExtractor.program.entry = 0 from rfl] using hh
  have eh := eval_call_lifted HeaderExtractor.program headerRegister headerStack
    (store [] [] [] []) headerRegister_injective headerStack_injective hh'
  rw [header_embed, header_embed] at eh
  obtain ⟨k, hk, ht⟩ := CounterConversions.encodeNat_runs CounterConversions.zeroRegs
    (QueryCodec.word n.size n)
  have ec := eval_call_lifted CounterConversions.encodeNatProgram
    (id : Fin 3 → Fin 3) counterStack (store tail [] [] [])
    Function.injective_id counterStack_injective ht
  rw [counter_embed, counter_embed, hv] at ec
  refine ⟨10 * n.size + 7 + k, ?_, eh.seq ec⟩
  have hk' : k ≤ 32 * (n + 1) * (n.size + 1) := by
    simpa [CounterConversions.runtimeBound, hv] using hk
  omega

theorem source_run (n : ℕ) (tail : List Bool) :
    BitProgram.RunsIn program (10 * n.size + 8 + 32 * (n + 1) * (n.size + 1))
      (BitProgram.initial program (QueryCodec.natHeader n ++ tail))
      ((store tail [] (Encoding.encodeNat n) []).withPC none) := by
  obtain ⟨k, hk, he⟩ := eval_header n tail
  have ht := StructuredCalls.compiled_halt_trace he 0 2
  have hi : (store (QueryCodec.natHeader n ++ tail) [] [] []).withPC
      (some program.entry) = BitProgram.initial program (QueryCodec.natHeader n ++ tail) := by
    dsimp only [store, StructuredProgram.State.withPC, BitProgram.initial]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hi] at ht
  exact ⟨k + 1, by omega, ht⟩

noncomputable abbrev primitive := GuardedCompiler.primitive program

/-- Actual physical tape preservation, obtained from the linked finite program.
The final Boolean control is not being advertised as a SAT answer. -/
theorem primitive_run (n : ℕ) (tail : List Bool) :
    ∃ steps final,
      Computation.Trace primitive.step steps
        (primitive.init (QueryCodec.natHeader n ++ tail)) final ∧
      steps ≤ 7 * (10 * n.size + 8 + 32 * (n + 1) * (n.size + 1)) ∧
      final.tapes program.inputStack = Turing.Tape.mk₁ (tail.map some) ∧
      final.tapes program.outputStack = Turing.Tape.mk₁ ((Encoding.encodeNat n).map some) := by
  have hp := GuardedCompiler.primitive_execution program (source_run n tail)
  rw [GuardedCompiler.primitive_initial] at hp
  obtain ⟨steps, hsteps, htrace⟩ := hp
  refine ⟨steps, GuardedCompiler.primitiveCfg program
    ((store tail [] (Encoding.encodeNat n) []).withPC none), htrace, hsteps, ?_, ?_⟩
  · rw [GuardedCompiler.primitive_tape]; rfl
  · rw [GuardedCompiler.primitive_tape]; rfl

end QecReliability.ExternalSATBridge.HeaderToUnary
