import ExternalSATCandidateBound

/-! Physical unary header emission from the retained binary variable word.
No supplied unary header, shift, or whole-query/SAT claim is used. -/
namespace QecReliability.ExternalSATBridge.CanonicalHeader

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls

def store (bits work unary scratch outer : List Bool) : StructuredProgram.State 3 5 :=
  ⟨(fun _ => false), ![bits, work, unary, scratch, outer]⟩

abbrev copyProgram : Program 3 5 8 := StackRoutines.copyProgram 0 1 3 0 1
abbrev transferProgram : Program 3 5 4 := StackRoutines.transferProgram 2 4 0 1

def encodePorts : Fin 3 → Fin 5 := ![1, 2, 3]

theorem encodePorts_injective : Function.Injective encodePorts := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [encodePorts]

theorem encode_embed (bits outer a b : List Bool) :
    embedState (id : Fin 3 → Fin 3) encodePorts (store bits [] [] [] outer)
      (CounterConversions.state CounterConversions.zeroRegs a b) = store bits a b [] outer := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ Function.injective_id encodePorts_injective
  · intro i; rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; rfl
  · intro i hi
    fin_cases i <;> simp_all [store, encodePorts, Fin.exists_fin_succ]

theorem copy_trace (bits outer : List Bool) :
    Trace copyProgram (7 * bits.length + 5)
      ((store bits [] [] [] outer).withPC (some copyProgram.entry))
      ((store bits bits [] [] outer).withPC none) := by
  have ht := StackRoutines.copyProgram_trace (0 : Fin 5) 1 3 (0 : Fin 3) 1
    (by decide) (by decide) (by decide) (by decide)
    (fun _ => false) (![bits, [], [], [], outer] : Fin 5 → List Bool) rfl
  have hh := StackRoutines.halt_after_trace copyProgram ht 7 rfl rfl
  have hr : readRegs (fun _ : Fin 3 => false) 0 1 none = (fun _ => false) := by
    funext i; fin_cases i <;> simp [readRegs]
  have hs : StackRoutines.copyStacks (0 : Fin 5) 1
      (![bits, [], [], [], outer] : Fin 5 → List Bool) = ![bits, bits, [], [], outer] := by
    funext i; fin_cases i <;> simp [StackRoutines.copyStacks]
  simpa only [StackRoutines.copyResult, hr, hs, store, StructuredProgram.State.withPC,
    Nat.add_assoc, show (![bits, [], [], [], outer] : Fin 5 → List Bool) 0 = bits from rfl,
    show (4 : ℕ) + 1 = 5 from rfl] using hh

theorem transfer_trace (bits unary outer : List Bool) :
    Trace transferProgram (3 * unary.length + 3)
      ((store bits [] unary [] outer).withPC (some transferProgram.entry))
      ((store bits [] [] [] (unary.reverse ++ outer)).withPC none) := by
  have ht := StackRoutines.transferProgram_trace (2 : Fin 5) 4 (0 : Fin 3) 1
    (by decide) (by decide) (fun _ => false)
    (![bits, [], unary, [], outer] : Fin 5 → List Bool)
  have hh := StackRoutines.halt_after_trace transferProgram ht 3 rfl rfl
  have hr : readRegs (fun _ : Fin 3 => false) 0 1 none = (fun _ => false) := by
    funext i; fin_cases i <;> simp [readRegs]
  have hs : StackRoutines.transferStacks (2 : Fin 5) 4
      (![bits, [], unary, [], outer] : Fin 5 → List Bool) =
      ![bits, [], [], [], unary.reverse ++ outer] := by
    funext i; fin_cases i <;> simp [StackRoutines.transferStacks]
  simpa only [StackRoutines.transferResult, hr, hs, store, StructuredProgram.State.withPC,
    Nat.add_assoc, show (![bits, [], unary, [], outer] : Fin 5 → List Bool) 2 = unary from rfl,
    show (2 : ℕ) + 1 = 3 from rfl] using hh

noncomputable def command : StructuredCalls.Cmd 3 5 :=
  .seq (.call copyProgram)
    (.seq (.call (ProgramLinking.liftProgram CounterConversions.encodeNatProgram id encodePorts))
      (.call transferProgram))
noncomputable abbrev program := compiled command 0 4

def timeBound (k value : ℕ) : ℕ :=
  7 * k + 9 + 32 * (value + 1) * (k + 1) + 3 * (value + 1)

theorem eval_header (bits outer : List Bool) :
    ∃ steps, steps + 1 ≤ timeBound bits.length (CounterPrograms.value bits) ∧
      Eval command steps (store bits [] [] [] outer)
        (store bits [] [] [] ((Encoding.encodeNat (CounterPrograms.value bits)).reverse ++ outer)) := by
  obtain ⟨n, hn, ht⟩ := CounterConversions.encodeNat_runs CounterConversions.zeroRegs bits
  have he := eval_call_lifted CounterConversions.encodeNatProgram
    (id : Fin 3 → Fin 3) encodePorts (store bits [] [] [] outer)
    Function.injective_id encodePorts_injective ht
  rw [encode_embed, encode_embed] at he
  have hall := (Eval.call copyProgram (copy_trace bits outer)).seq
    (he.seq (Eval.call transferProgram (transfer_trace bits _ outer)))
  refine ⟨_, ?_, hall⟩
  simp only [Encoding.length_encodeNat]
  dsimp only [CounterConversions.runtimeBound] at hn
  dsimp only [timeBound]
  omega

theorem source_bits (bits outer : List Bool) :
    BitProgram.RunsIn program (timeBound bits.length (CounterPrograms.value bits))
      ((store bits [] [] [] outer).withPC (some program.entry))
      ((store bits [] [] [] ((Encoding.encodeNat (CounterPrograms.value bits)).reverse ++ outer)).withPC none) := by
  obtain ⟨n, hn, ht⟩ := eval_header bits outer
  exact ⟨n + 1, hn, compiled_halt_trace ht 0 4⟩

theorem source_variable_header (v : ℕ) (outer : List Bool) :
    BitProgram.RunsIn program (timeBound v.size v)
      ((store (QueryCodec.word v.size v) [] [] [] outer).withPC (some program.entry))
      ((store (QueryCodec.word v.size v) [] [] [] ((Encoding.encodeNat v).reverse ++ outer)).withPC none) := by
  have hv := PrimitiveTransport.binary_word_value v.size v (Nat.lt_size_self v)
  simpa only [hv, QueryCodec.word_length] using source_bits (QueryCodec.word v.size v) outer

end QecReliability.ExternalSATBridge.CanonicalHeader
