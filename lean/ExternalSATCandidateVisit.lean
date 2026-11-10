import ExternalSATFormulaOccurrence
import ExternalSATCandidateClauseEmitter

/-! One concrete candidate visit: preserved raw-body scan, real result-bit pop,
physical conditional branch, and the actual nested-frame emitter. Both candidate
words and the original raw body survive. This is not the full range traversal. -/
namespace QecReliability.ExternalSATBridge.CandidateVisit

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls

abbrev Candidates := Fin 3 → List Bool
abbrev zeroRegs : Fin 16 → Bool := fun _ => false

def store (candidate : Candidates) (raw outer answer : List Bool) (bit : Bool) :
    StructuredProgram.State 16 16 :=
  ⟨Function.update zeroRegs 0 bit,
    ![candidate 0, candidate 1, candidate 2, [], [], [], [], [], [], answer,
      raw, [], [], [], [], outer]⟩

abbrev scanRegister : Fin 14 → Fin 16 := fun i => i.castAdd 2
abbrev scanStack : Fin 12 → Fin 16 := fun i => i.castAdd 4
abbrev emitRegister : Fin 2 → Fin 16 := fun i => i.castAdd 14
def emitStack : Fin 7 → Fin 16 := ![0, 1, 2, 13, 12, 14, 15]

theorem scanRegister_injective : Function.Injective scanRegister := by
  intro a b h; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) h
theorem scanStack_injective : Function.Injective scanStack := by
  intro a b h; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) h
theorem emitRegister_injective : Function.Injective emitRegister := by
  intro a b h; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) h
theorem emitStack_injective : Function.Injective emitStack := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [emitStack]

theorem scan_embed (candidate : Candidates) (raw outer answer : List Bool) :
    embedState scanRegister scanStack (store candidate raw outer [] false)
      (FormulaOccurrence.store candidate [] raw answer false false) =
      store candidate raw outer answer false := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ scanRegister_injective scanStack_injective
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp_all [scanRegister, store, zeroRegs, Fin.exists_fin_succ]
  · intro i hi; fin_cases i <;> simp_all [scanStack, store, Fin.exists_fin_succ]

theorem emit_embed (candidate : Candidates) (raw outer : List Bool) :
    embedState emitRegister emitStack (store candidate raw [] [] false)
      (CandidateClauseEmitter.data candidate [] [] [] outer) =
      store candidate raw outer [] false := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ emitRegister_injective emitStack_injective
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp_all [emitRegister, store, zeroRegs, Fin.exists_fin_succ]
  · intro i hi; fin_cases i <;> simp_all [emitStack, store, Fin.exists_fin_succ]

def popAnswer : StructuredCalls.Cmd 16 16 := .base
  (.seq (.atom (.pop 9 0 1)) (.atom (.set 1 false)))

theorem pop_eval (candidate : Candidates) (raw outer : List Bool) (bit : Bool) :
    Eval popAnswer 2 (store candidate raw outer [bit] false)
      (store candidate raw outer [] bit) := by
  apply Eval.base
  have h := (StructuredProgram.Eval.atom (.pop (9 : Fin 16) (0 : Fin 16) 1)
    (store candidate raw outer [bit] false)).seq
      (StructuredProgram.Eval.atom (.set (1 : Fin 16) false) _)
  have hr : Function.update (readRegs zeroRegs 0 1 (some bit)) 1 false =
      Function.update zeroRegs 0 bit := by
    funext i; fin_cases i <;> simp [readRegs, zeroRegs]
  have hs : Function.update
      (![candidate 0, candidate 1, candidate 2, [], [], [], [], [], [], [bit], raw, [], [], [], [], outer] :
        Fin 16 → List Bool) 9 [] =
      ![candidate 0, candidate 1, candidate 2, [], [], [], [], [], [], [], raw, [], [], [], [], outer] := by
    funext i; fin_cases i <;> simp
  simpa [store, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, hr, hs] using h

def clearTest : StructuredCalls.Cmd 16 16 := .base (.atom (.set 0 false))

theorem clear_eval (candidate : Candidates) (raw outer : List Bool) :
    Eval clearTest 1 (store candidate raw outer [] true) (store candidate raw outer [] false) := by
  apply Eval.base
  have h := StructuredProgram.Eval.atom (.set (0 : Fin 16) false) (store candidate raw outer [] true)
  simpa [store, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h

noncomputable abbrev scanProgram := ProgramLinking.liftProgram FormulaOccurrence.program scanRegister scanStack
noncomputable abbrev emitProgram := ProgramLinking.liftProgram CandidateClauseEmitter.program emitRegister emitStack
noncomputable def yesCommand : StructuredCalls.Cmd 16 16 := .seq clearTest (.call emitProgram)
noncomputable def branch : StructuredCalls.Cmd 16 16 := .ite 0 yesCommand (.base .skip)
noncomputable def command : StructuredCalls.Cmd 16 16 :=
  .seq (.call scanProgram) (.seq popAnswer branch)
noncomputable abbrev program := compiled command 10 15

def occurs (candidate : Candidates) (clauses : List (List ℕ)) : Bool :=
  clauses.any (RawClauseMatcher.clauseResult candidate)
def output (candidate : Candidates) (clauses : List (List ℕ)) (outer : List Bool) : List Bool :=
  if occurs candidate clauses then (CandidateClauseEmitter.entry candidate).reverse ++ outer else outer

def timeBound (candidate : Candidates) (clauses : List (List ℕ)) : ℕ :=
  FormulaOccurrence.timeBound candidate clauses + 64 * (CandidateClauseEmitter.wordSize candidate + 4) + 5

theorem eval_visit (candidate : Candidates) (clauses : List (List ℕ))
    (hc : ∀ c ∈ clauses, c.length ≤ 3) (outer : List Bool) :
    ∃ n, n + 1 ≤ timeBound candidate clauses ∧
      Eval command n (store candidate (FormulaOccurrence.rawBody clauses) outer [] false)
        (store candidate (FormulaOccurrence.rawBody clauses) (output candidate clauses outer) [] false) := by
  obtain ⟨ns, hns, hts⟩ := FormulaOccurrence.source_run candidate clauses hc []
  have es := eval_call_lifted FormulaOccurrence.program scanRegister scanStack
    (store candidate (FormulaOccurrence.rawBody clauses) outer [] false)
    scanRegister_injective scanStack_injective hts
  rw [scan_embed, scan_embed] at es
  have es' : Eval (.call scanProgram) ns
      (store candidate (FormulaOccurrence.rawBody clauses) outer [] false)
      (store candidate (FormulaOccurrence.rawBody clauses) outer [occurs candidate clauses] false) := es
  have ep := pop_eval candidate (FormulaOccurrence.rawBody clauses) outer (occurs candidate clauses)
  cases ho : occurs candidate clauses with
  | false =>
    have eb : Eval branch 1
        (store candidate (FormulaOccurrence.rawBody clauses) outer [] false)
        (store candidate (FormulaOccurrence.rawBody clauses) outer [] false) :=
      .ite_false rfl (.base (.skip _))
    have ep' := ep
    rw [ho] at ep' es'
    have hall := es'.seq (ep'.seq eb)
    refine ⟨ns + (2 + 1), ?_, ?_⟩
    · dsimp only [timeBound]; omega
    · simpa [command, output, ho] using hall
  | true =>
    obtain ⟨ne, hne, hte⟩ := CandidateClauseEmitter.source_words candidate outer
    have ee := eval_call_lifted CandidateClauseEmitter.program emitRegister emitStack
      (store candidate (FormulaOccurrence.rawBody clauses) [] [] false)
      emitRegister_injective emitStack_injective hte
    rw [emit_embed, emit_embed] at ee
    have ey := (clear_eval candidate (FormulaOccurrence.rawBody clauses) outer).seq ee
    have eb := Eval.ite_true (no := (.base .skip))
      (show (store candidate (FormulaOccurrence.rawBody clauses) outer [] true).regs 0 = true from rfl) ey
    have ep' := ep
    rw [ho] at ep' es'
    have hall := es'.seq (ep'.seq eb)
    refine ⟨ns + (2 + ((1 + ne) + 1)), ?_, ?_⟩
    · dsimp only [timeBound]; omega
    · simpa [command, branch, yesCommand, output, ho] using hall

theorem source_visit (candidate : Candidates) (clauses : List (List ℕ))
    (hc : ∀ c ∈ clauses, c.length ≤ 3) (outer : List Bool) :
    BitProgram.RunsIn program (timeBound candidate clauses)
      ((store candidate (FormulaOccurrence.rawBody clauses) outer [] false).withPC (some program.entry))
      ((store candidate (FormulaOccurrence.rawBody clauses) (output candidate clauses outer) [] false).withPC none) := by
  obtain ⟨n, hn, he⟩ := eval_visit candidate clauses hc outer
  exact ⟨n + 1, hn, compiled_halt_trace he 10 15⟩

end QecReliability.ExternalSATBridge.CandidateVisit
