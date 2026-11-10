import ExternalSATCanonicalBytes
import ExternalSATRawQueryLowering

/-! Whole valid binary query to the genuine external canonical encoding, using
one fixed finite controller. Raw parsing, metadata cleanup and canonical traversal
are actual calls. This module does not execute or assume an external SAT solver. -/
namespace QecReliability.ExternalSATBridge.QueryCanonicalController
open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls

abbrev zeroRegs : Fin 16 → Bool := fun _ => false

def frontState (input vars width clauses work literal scratch raw : List Bool) :
    StructuredProgram.State 16 20 :=
  ⟨zeroRegs, ![input, [], [], [], raw, [], work, literal, scratch, [], [], [], [], [], [], [], [], width, clauses, vars]⟩
abbrev frontRegister : Fin 5 → Fin 16 := fun i => i.castAdd 11
def frontPorts : Fin 8 → Fin 20 := ![0, 19, 17, 18, 6, 7, 8, 4]

theorem frontRegister_injective : Function.Injective frontRegister := by
  intro a b h; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) h
theorem frontPorts_injective : Function.Injective frontPorts := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [frontPorts]

theorem front_embed (input vars width clauses work literal scratch raw : List Bool) :
    embedState frontRegister frontPorts (frontState [] [] [] [] [] [] [] [])
      (RawLiteralEmitter.state false false input vars width clauses work literal scratch raw) =
      frontState input vars width clauses work literal scratch raw := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ frontRegister_injective frontPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp_all [frontRegister, frontState, zeroRegs, Fin.exists_fin_succ]
  · intro i hi; fin_cases i <;> simp_all [frontPorts, frontState, Fin.exists_fin_succ]

abbrev clearWidth : Program 16 20 3 := StackRoutines.clearProgram 17 0 1
abbrev clearClauses : Program 16 20 3 := StackRoutines.clearProgram 18 0 1

theorem clear_width_eval (vars width clauses raw : List Bool) :
    Eval (.call clearWidth) (2 * width.length + 3)
      (frontState [] vars width clauses [] [] [] raw) (frontState [] vars [] clauses [] [] [] raw) := by
  apply Eval.call
  have h := ListRegisterProgram.clear_run (17 : Fin 20) (0 : Fin 16) 1 zeroRegs
    (frontState [] vars width clauses [] [] [] raw).stacks
  have hr : readRegs zeroRegs 0 1 none = zeroRegs := by
    funext i; fin_cases i <;> simp [readRegs, zeroRegs]
  have hs : StackRoutines.clearStacks (17 : Fin 20)
      (frontState [] vars width clauses [] [] [] raw).stacks =
      (frontState [] vars [] clauses [] [] [] raw).stacks := by
    funext i; fin_cases i <;> simp [StackRoutines.clearStacks, frontState]
  have hl : (frontState [] vars width clauses [] [] [] raw).stacks 17 = width := rfl
  rw [hr, hs, hl] at h
  simpa only [ListRegisterProgram.Run, frontState, StructuredProgram.State.withPC] using h

theorem clear_clauses_eval (vars clauses raw : List Bool) :
    Eval (.call clearClauses) (2 * clauses.length + 3)
      (frontState [] vars [] clauses [] [] [] raw) (CanonicalRawController.state vars raw [] [] []) := by
  apply Eval.call
  have h := ListRegisterProgram.clear_run (18 : Fin 20) (0 : Fin 16) 1 zeroRegs
    (frontState [] vars [] clauses [] [] [] raw).stacks
  have hr : readRegs zeroRegs 0 1 none = zeroRegs := by
    funext i; fin_cases i <;> simp [readRegs, zeroRegs]
  have hs : StackRoutines.clearStacks (18 : Fin 20)
      (frontState [] vars [] clauses [] [] [] raw).stacks =
      (CanonicalRawController.state vars raw [] [] []).stacks := by
    funext i; fin_cases i <;> simp [StackRoutines.clearStacks, frontState, CanonicalRawController.state]
  have hl : (frontState [] vars [] clauses [] [] [] raw).stacks 18 = clauses := rfl
  rw [hr, hs, hl] at h
  simpa only [ListRegisterProgram.Run, frontState, CanonicalRawController.state,
    CanonicalRawController.zeroRegs, zeroRegs, StructuredProgram.State.withPC] using h

theorem raw_body_eq {v : ℕ} (F : PrefixCNF.Formula v) :
    FormulaOccurrence.rawBody (CanonicalBytes.rawClauses F) = RawBodyParser.output F := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    change RawClauseMatcher.rawClause (ClauseMatchSemantics.literalCodes c) ++
        FormulaOccurrence.rawBody (CanonicalBytes.rawClauses F) =
      RawClauseParser.rawClause c ++ RawBodyParser.output F
    rw [ih]
    have hc : RawClauseMatcher.rawClause (ClauseMatchSemantics.literalCodes c) =
        RawClauseParser.rawClause c := by
      simpa only [ClauseMatchSemantics.literalCodes, FormulaBridge.literal] using
        RawClauseMatcher.rawClause_literalCodes c
    rw [hc]

theorem raw_width (q : SATRequest) :
    ∀ c ∈ CanonicalBytes.rawClauses q.formula, c.length ≤ 3 := by
  intro c hc
  obtain ⟨native, hn, rfl⟩ := List.mem_map.mp hc
  simpa only [ClauseMatchSemantics.literalCodes, List.length_map] using q.width native hn

theorem raw_code_bound (q : SATRequest) :
    ∀ c ∈ CanonicalBytes.rawClauses q.formula, ∀ x ∈ c, x < 2 * q.varCount := by
  intro c hc x hx
  obtain ⟨native, hn, rfl⟩ := List.mem_map.mp hc
  obtain ⟨literal, hl, rfl⟩ := List.mem_map.mp hx
  exact Encoding.literalCode_lt (FormulaBridge.literal literal)

noncomputable def command : StructuredCalls.Cmd 16 20 :=
  .seq (.call (ProgramLinking.liftProgram RawQueryLowering.program frontRegister frontPorts))
    (.seq (.call clearWidth) (.seq (.call clearClauses) (.call CanonicalRawController.program)))
noncomputable abbrev program := compiled command 0 5

def ready (q : SATRequest) : StructuredProgram.State 16 20 :=
  CanonicalRawController.state (QueryCodec.word q.varCount.size q.varCount)
    (RawBodyParser.output q.formula) (Encoding.encodeCNF (FormulaBridge.formula q.formula)) [] []

def timeBound (q : SATRequest) : ℕ := RawQueryLowering.timeBound q +
  (2 * (q.varCount.size + 1) + 3) + (2 * q.formula.length.size + 3) +
  CanonicalRawController.timeBound q.varCount (CanonicalBytes.rawClauses q.formula) + 1

theorem query_eval (q : SATRequest) :
    ∃ n, n + 1 ≤ timeBound q ∧
      Eval command n (frontState (QueryCodec.encode q) [] [] [] [] [] [] []) (ready q) := by
  obtain ⟨nf, hnf, htf⟩ := RawQueryLowering.source_query q
  rw [← RawQueryLowering.initial_eq] at htf
  have ef := eval_call_lifted RawQueryLowering.program frontRegister frontPorts
    (frontState [] [] [] [] [] [] [] []) frontRegister_injective frontPorts_injective htf
  rw [front_embed] at ef
  dsimp only [RawQueryLowering.ready] at ef
  rw [front_embed] at ef
  have ew := clear_width_eval (QueryCodec.word q.varCount.size q.varCount) (Encoding.encodeNat q.varCount.size)
    (QueryCodec.word q.formula.length.size q.formula.length) (RawBodyParser.output q.formula)
  have em := clear_clauses_eval (QueryCodec.word q.varCount.size q.varCount)
    (QueryCodec.word q.formula.length.size q.formula.length) (RawBodyParser.output q.formula)
  obtain ⟨nc, hnc, htc⟩ := CanonicalRawController.source_controller q.varCount
    (CanonicalBytes.rawClauses q.formula) (raw_width q)
    (fun c hc x hx => (raw_code_bound q c hc x hx).le)
  rw [raw_body_eq, CanonicalBytes.output_eq q.formula q.width] at htc
  have ec := Eval.call CanonicalRawController.program htc
  have hall := ef.seq (ew.seq (em.seq ec))
  refine ⟨nf + ((2 * (Encoding.encodeNat q.varCount.size).length + 3) +
    ((2 * (QueryCodec.word q.formula.length.size q.formula.length).length + 3) + nc)), ?_, hall⟩
  simp only [Encoding.length_encodeNat, QueryCodec.word_length]
  dsimp only [timeBound]
  omega

theorem initial_eq (bits : List Bool) :
    (frontState bits [] [] [] [] [] [] []).withPC (some program.entry) = BitProgram.initial program bits := by
  dsimp only [frontState, StructuredProgram.State.withPC, BitProgram.initial, zeroRegs]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Starts from the SINGLE actual binary query and ends with genuine external
canonical bytes on physical stack5. Metadata input and all work are accounted for. -/
theorem source_query (q : SATRequest) :
    BitProgram.RunsIn program (timeBound q) (BitProgram.initial program (QueryCodec.encode q))
      ((ready q).withPC none) := by
  obtain ⟨n, hn, he⟩ := query_eval q
  have ht := compiled_halt_trace he 0 5
  rw [initial_eq] at ht
  exact ⟨n + 1, hn, ht⟩

noncomputable abbrev primitive := GuardedCompiler.primitive program

theorem primitive_query (q : SATRequest) :
    ∃ steps final,
      Computation.Trace primitive.step steps (primitive.init (QueryCodec.encode q)) final ∧
      steps ≤ 7 * timeBound q ∧
      (∀ i : Fin 20, final.tapes i = Turing.Tape.mk₁ (((ready q).stacks i).map some)) := by
  have hp := GuardedCompiler.primitive_execution program (source_query q)
  rw [GuardedCompiler.primitive_initial] at hp
  obtain ⟨steps, hs, ht⟩ := hp
  refine ⟨steps, GuardedCompiler.primitiveCfg program ((ready q).withPC none), ht, hs, ?_⟩
  intro i
  exact GuardedCompiler.primitive_tape program ((ready q).withPC none) i

end QecReliability.ExternalSATBridge.QueryCanonicalController
