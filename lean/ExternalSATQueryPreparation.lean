import ExternalSATWidthPreparation

/-! A fixed initial-query controller: consume BOTH native headers, compute the
literal-width word by measured instructions, and retain the exact clause body.
It starts from the real QueryCodec.encode input. Clause parsing is subsequent. -/
namespace QecReliability.ExternalSATBridge.QueryPreparation

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls

def store (input vars width clauses work output scratch : List Bool) : StructuredProgram.State 3 7 :=
  ⟨fun _ => false, ![input, vars, width, clauses, work, output, scratch]⟩

def firstPorts : Fin 3 → Fin 7 := ![0, 1, 6]
def widthPorts : Fin 5 → Fin 7 := ![0, 1, 2, 4, 6]
def secondPorts : Fin 3 → Fin 7 := ![0, 3, 6]

theorem firstPorts_injective : Function.Injective firstPorts := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [firstPorts]
theorem widthPorts_injective : Function.Injective widthPorts := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [widthPorts]
theorem secondPorts_injective : Function.Injective secondPorts := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [secondPorts]

theorem first_embed (a b c : List Bool) :
    embedState HeaderToUnary.headerRegister firstPorts (store [] [] [] [] [] [] [])
      (⟨fun _ => false, ![a, b, c]⟩ : StructuredProgram.State 2 3) = store a b [] [] [] [] c := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ HeaderToUnary.headerRegister_injective firstPorts_injective
  · intro i; rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; rfl
  · intro i hi
    fin_cases i <;> simp_all [store, firstPorts, Fin.exists_fin_succ]

theorem width_embed (a b c d e : List Bool) :
    embedState (id : Fin 3 → Fin 3) widthPorts (store [] [] [] [] [] [] [])
      (WidthPreparation.store a b c d e) = store a b c [] d [] e := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ Function.injective_id widthPorts_injective
  · intro i; rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; rfl
  · intro i hi
    fin_cases i <;> simp_all [store, widthPorts, Fin.exists_fin_succ]

theorem second_embed (vars width a b c : List Bool) :
    embedState HeaderToUnary.headerRegister secondPorts (store [] vars width [] [] [] [])
      (⟨fun _ => false, ![a, b, c]⟩ : StructuredProgram.State 2 3) =
        store a vars width b [] [] c := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ HeaderToUnary.headerRegister_injective secondPorts_injective
  · intro i; rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; rfl
  · intro i hi
    fin_cases i <;> simp_all [store, secondPorts, Fin.exists_fin_succ]

theorem header_data_trace (n : ℕ) (tail : List Bool) :
    Trace HeaderExtractor.program (10 * n.size + 7)
      ((⟨fun _ => false, ![QueryCodec.natHeader n ++ tail, [], []]⟩ : StructuredProgram.State 2 3).withPC
        (some HeaderExtractor.program.entry))
      ((⟨fun _ => false, ![tail, QueryCodec.word n.size n, []]⟩ : StructuredProgram.State 2 3).withPC none) := by
  have h := HeaderExtractor.header_trace (fun _ => false) n tail
  have hr : HeaderExtractor.regs none = (fun _ => false) := by
    funext i; fin_cases i <;> rfl
  simpa only [HeaderExtractor.cfg, HeaderExtractor.finalCfg, hr,
    StructuredProgram.State.withPC, show HeaderExtractor.program.entry = 0 from rfl] using h

noncomputable def command : StructuredCalls.Cmd 3 7 :=
  .seq (.call (ProgramLinking.liftProgram HeaderExtractor.program HeaderToUnary.headerRegister firstPorts))
    (.seq (.call (ProgramLinking.liftProgram WidthPreparation.program id widthPorts))
      (.call (ProgramLinking.liftProgram HeaderExtractor.program HeaderToUnary.headerRegister secondPorts)))

noncomputable abbrev program := compiled command 0 0

def timeBound (v m : ℕ) : ℕ :=
  (10 * v.size + 7) + WidthPreparation.timeBound v.size + (10 * m.size + 7) + 1

theorem eval_headers (v m : ℕ) (body : List Bool) :
    ∃ steps, steps + 1 ≤ timeBound v m ∧
      StructuredCalls.Eval command steps
        (store (QueryCodec.natHeader v ++ (QueryCodec.natHeader m ++ body)) [] [] [] [] [] [])
        (store body (QueryCodec.word v.size v) (Encoding.encodeNat v.size)
          (QueryCodec.word m.size m) [] [] []) := by
  have hfirst := eval_call_lifted HeaderExtractor.program HeaderToUnary.headerRegister firstPorts
    (store [] [] [] [] [] [] []) HeaderToUnary.headerRegister_injective firstPorts_injective
    (header_data_trace v (QueryCodec.natHeader m ++ body))
  rw [first_embed, first_embed] at hfirst
  obtain ⟨k, hk, ht⟩ := WidthPreparation.source_width
    (QueryCodec.natHeader m ++ body) (QueryCodec.word v.size v)
  have hwidth := eval_call_lifted WidthPreparation.program (id : Fin 3 → Fin 3) widthPorts
    (store [] [] [] [] [] [] []) Function.injective_id widthPorts_injective ht
  rw [width_embed, width_embed, QueryCodec.word_length] at hwidth
  have hsecond := eval_call_lifted HeaderExtractor.program HeaderToUnary.headerRegister secondPorts
    (store [] (QueryCodec.word v.size v) (Encoding.encodeNat v.size) [] [] [] [])
    HeaderToUnary.headerRegister_injective secondPorts_injective (header_data_trace m body)
  rw [second_embed, second_embed] at hsecond
  refine ⟨(10 * v.size + 7) + (k + (10 * m.size + 7)), ?_, hfirst.seq (hwidth.seq hsecond)⟩
  simp only [QueryCodec.word_length] at hk
  dsimp only [timeBound]
  omega

def ready (q : SATRequest) : StructuredProgram.State 3 7 :=
  store (QueryCodec.body q.varCount.size (QueryCodec.plain q.formula))
    (QueryCodec.word q.varCount.size q.varCount) (Encoding.encodeNat q.varCount.size)
    (QueryCodec.word q.formula.length.size q.formula.length) [] [] []

theorem initial_eq (input : List Bool) :
    (store input [] [] [] [] [] []).withPC (some program.entry) = BitProgram.initial program input := by
  dsimp only [store, StructuredProgram.State.withPC, BitProgram.initial]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The actual complete native query, not pre-isolated fields, is consumed up to
its clause-body boundary. All retained words occur on physical program stacks. -/
theorem source_query (q : SATRequest) :
    BitProgram.RunsIn program (timeBound q.varCount q.formula.length)
      (BitProgram.initial program (QueryCodec.encode q)) ((ready q).withPC none) := by
  obtain ⟨k, hk, he⟩ := eval_headers q.varCount q.formula.length
    (QueryCodec.body q.varCount.size (QueryCodec.plain q.formula))
  have ht := compiled_halt_trace he 0 0
  rw [initial_eq] at ht
  exact ⟨k + 1, hk, by simpa only [QueryCodec.encode, ready, List.append_assoc] using ht⟩

noncomputable abbrev primitive := GuardedCompiler.primitive program

theorem primitive_query (q : SATRequest) :
    ∃ steps final,
      Computation.Trace primitive.step steps (primitive.init (QueryCodec.encode q)) final ∧
      steps ≤ 7 * timeBound q.varCount q.formula.length ∧
      (∀ i : Fin 7, final.tapes i = Turing.Tape.mk₁ (((ready q).stacks i).map some)) := by
  have hp := GuardedCompiler.primitive_execution program (source_query q)
  rw [GuardedCompiler.primitive_initial] at hp
  obtain ⟨steps, hs, ht⟩ := hp
  refine ⟨steps, GuardedCompiler.primitiveCfg program ((ready q).withPC none), ht, hs, ?_⟩
  intro i
  rw [GuardedCompiler.primitive_tape]

end QecReliability.ExternalSATBridge.QueryPreparation
