import ExternalSATOuterCandidateTraversal
import ExternalSATCanonicalHeader
import ExternalSATCanonicalFinalize
import ExternalSATCandidateBound

/-! Complete physical canonical traversal stage from a retained binary variable
header and an already measured raw unary body. Header/bound computation, empty
candidate, all three DFS depths, cleanup, outer terminator and final reversal are
actual instructions. Initial binary-query parsing and exact byte equality are
separate composition theorems, not assumptions hidden in this controller. -/
namespace QecReliability.ExternalSATBridge.CanonicalRawController
open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls

abbrev zeroRegs : Fin 16 → Bool := fun _ => false
/-- Outer traversal occupies0..18; retained binary header19 is framed. -/
def state (bits raw outer counter code : List Bool) : StructuredProgram.State 16 20 :=
  ⟨zeroRegs, ![counter, code, [], [], raw, outer, [], [], [], [], [], [], [], [], [], [], [], [], [], bits]⟩

abbrev register3 : Fin 3 → Fin 16 := fun i => i.castAdd 13
abbrev register2 : Fin 2 → Fin 16 := fun i => i.castAdd 14
def headerPorts : Fin 5 → Fin 20 := ![19, 6, 7, 8, 5]
def boundPorts : Fin 4 → Fin 20 := ![19, 6, 0, 8]
def rootPorts : Fin 16 → Fin 20 := ![1, 2, 3, 6, 7, 8, 9, 10, 11, 12, 4, 13, 14, 15, 16, 5]
abbrev outerPorts : Fin 19 → Fin 20 := fun i => i.castAdd 1
def finalPorts : Fin 3 → Fin 20 := ![5, 6, 7]

theorem register3_injective : Function.Injective register3 := by
  intro a b h; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) h
theorem register2_injective : Function.Injective register2 := by
  intro a b h; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) h
theorem headerPorts_injective : Function.Injective headerPorts := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [headerPorts]
theorem boundPorts_injective : Function.Injective boundPorts := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [boundPorts]
theorem rootPorts_injective : Function.Injective rootPorts := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [rootPorts]
theorem outerPorts_injective : Function.Injective outerPorts := by
  intro a b h; apply Fin.ext; exact congrArg (fun x : Fin 20 => x.val) h
theorem finalPorts_injective : Function.Injective finalPorts := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [finalPorts]

theorem header_embed (bits raw outer counter code : List Bool) :
    embedState register3 headerPorts (state bits raw [] counter code)
      (CanonicalHeader.store bits [] [] [] outer) = state bits raw outer counter code := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ register3_injective headerPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp_all [register3, state, zeroRegs, Fin.exists_fin_succ]
  · intro i hi; fin_cases i <;> simp_all [headerPorts, state, Fin.exists_fin_succ]

theorem bound_embed (bits raw outer counter code : List Bool) :
    embedState register3 boundPorts (state bits raw outer [] code)
      (HeaderToUnary.store bits [] counter []) = state bits raw outer counter code := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ register3_injective boundPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp_all [register3, state, zeroRegs, Fin.exists_fin_succ]
  · intro i hi; fin_cases i <;> simp_all [boundPorts, state, Fin.exists_fin_succ]

theorem root_embed (bits raw outer counter : List Bool) :
    embedState (id : Fin 16 → Fin 16) rootPorts (state bits raw [] counter [])
      (CandidateVisit.store ![[], [], []] raw outer [] false) = state bits raw outer counter [] := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ Function.injective_id rootPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i hi; fin_cases i <;> simp_all [rootPorts, state, Fin.exists_fin_succ]

theorem outer_embed (bits raw outer counter code : List Bool) :
    embedState (id : Fin 16 → Fin 16) outerPorts (state bits [] [] [] [])
      (OuterCandidateTraversal.state counter code raw outer) = state bits raw outer counter code := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ Function.injective_id outerPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i hi; fin_cases i <;> simp_all [outerPorts, state, Fin.exists_fin_succ]

theorem final_embed (bits raw outer : List Bool) :
    embedState register2 finalPorts (state bits raw [] [] [])
      (CanonicalFinalize.store outer) = state bits raw outer [] [] := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ register2_injective finalPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp_all [register2, state, zeroRegs, Fin.exists_fin_succ]
  · intro i hi; fin_cases i <;> simp_all [finalPorts, state, Fin.exists_fin_succ]

def initializeCode : StructuredCalls.Cmd 16 20 := .base (.atom (.push 1 0))
theorem initialize_eval (bits raw outer counter : List Bool) :
    Eval initializeCode 1 (state bits raw outer counter []) (state bits raw outer counter [false]) := by
  apply Eval.base
  have h := StructuredProgram.Eval.atom (.push (1 : Fin 20) (0 : Fin 16)) (state bits raw outer counter [])
  have hs : Function.update (state bits raw outer counter []).stacks 1 [false] =
      (state bits raw outer counter [false]).stacks := by
    funext i; fin_cases i <;> simp [state]
  have h' := h
  simp only [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
    show (state bits raw outer counter []).regs 0 = false from rfl,
    show (state bits raw outer counter []).stacks 1 = [] from rfl, hs] at h'
  simpa only [state] using h'

abbrev clearCode : Program 16 20 3 := StackRoutines.clearProgram 1 0 1

theorem clear_eval (bits raw outer counter code : List Bool) :
    Eval (.call clearCode) (2 * code.length + 3)
      (state bits raw outer counter code) (state bits raw outer counter []) := by
  apply Eval.call
  have h := ListRegisterProgram.clear_run (1 : Fin 20) (0 : Fin 16) 1 zeroRegs
    (state bits raw outer counter code).stacks
  have hr : readRegs zeroRegs 0 1 none = zeroRegs := by
    funext i; fin_cases i <;> simp [readRegs, zeroRegs]
  have hs : StackRoutines.clearStacks (1 : Fin 20) (state bits raw outer counter code).stacks =
      (state bits raw outer counter []).stacks := by
    funext i; fin_cases i <;> simp [StackRoutines.clearStacks, state]
  have hl : (state bits raw outer counter code).stacks 1 = code := rfl
  rw [hr, hs, hl] at h
  simpa only [ListRegisterProgram.Run, state, StructuredProgram.State.withPC] using h

noncomputable def command : StructuredCalls.Cmd 16 20 :=
  .seq (.call (ProgramLinking.liftProgram CanonicalHeader.program register3 headerPorts))
    (.seq (.call (ProgramLinking.liftProgram CandidateBound.program register3 boundPorts))
      (.seq (.call (ProgramLinking.liftProgram CandidateVisit.program id rootPorts))
        (.seq initializeCode
          (.seq (.call (ProgramLinking.liftProgram OuterCandidateTraversal.program id outerPorts))
            (.seq (.call clearCode)
              (.call (ProgramLinking.liftProgram CanonicalFinalize.program register2 finalPorts)))))))
noncomputable abbrev program := compiled command 19 5

def accumulator (v : ℕ) (clauses : List (List ℕ)) : List Bool :=
  OuterCandidateTraversal.output clauses 0 (2 * v) (2 * v)
    (CandidateVisit.output ![[], [], []] clauses (Encoding.encodeNat v).reverse)
def output (v : ℕ) (clauses : List (List ℕ)) : List Bool := (accumulator v clauses).reverse ++ [false]
def boundCost (v : ℕ) : ℕ := 7 * v.size + 7 + 32 * (2 * v + 1) * (v.size + 2)
def timeBound (v : ℕ) (clauses : List (List ℕ)) : ℕ :=
  CanonicalHeader.timeBound v.size v + boundCost v + CandidateVisit.timeBound ![[], [], []] clauses + 1 +
    (2 * v * (OuterCandidateTraversal.budget (2 * v) clauses + 7) + 4) +
    (2 * (2 * v + 1) + 3) + (9 * (accumulator v clauses).length + 19) + 1

/-- Every premise concerns validity of already physical input words. No visited
candidate list, decision oracle, or precomputed unary bound is supplied. -/
theorem eval_controller (v : ℕ) (clauses : List (List ℕ))
    (hw : ∀ c ∈ clauses, c.length ≤ 3) (hn : ∀ c ∈ clauses, ∀ x ∈ c, x ≤ 2 * v) :
    ∃ n, n + 1 ≤ timeBound v clauses ∧
      Eval command n (state (QueryCodec.word v.size v) (FormulaOccurrence.rawBody clauses) [] [] [])
        (state (QueryCodec.word v.size v) (FormulaOccurrence.rawBody clauses) (output v clauses) [] []) := by
  let bits := QueryCodec.word v.size v
  let raw := FormulaOccurrence.rawBody clauses
  let head := (Encoding.encodeNat v).reverse
  let root := CandidateVisit.output ![[], [], []] clauses head
  let final := accumulator v clauses
  obtain ⟨nh, hnh, hth⟩ := CanonicalHeader.source_variable_header v []
  have eh := eval_call_lifted CanonicalHeader.program register3 headerPorts
    (state bits raw [] [] []) register3_injective headerPorts_injective hth
  rw [header_embed, header_embed] at eh
  simp only [List.append_nil] at eh
  obtain ⟨nb, hnb, htb⟩ := CandidateBound.source_variable_header v
  have eb := eval_call_lifted CandidateBound.program register3 boundPorts
    (state bits raw head [] []) register3_injective boundPorts_injective htb
  rw [bound_embed, bound_embed] at eb
  obtain ⟨nr, hnr, htr⟩ := CandidateVisit.source_visit ![[], [], []] clauses hw head
  have er := eval_call_lifted CandidateVisit.program (id : Fin 16 → Fin 16) rootPorts
    (state bits raw [] (Encoding.encodeNat (2 * v)) []) Function.injective_id rootPorts_injective htr
  rw [root_embed, root_embed] at er
  have ei := initialize_eval bits raw root (Encoding.encodeNat (2 * v))
  obtain ⟨no, hno, hto⟩ := OuterCandidateTraversal.source_traversal (2 * v) 0 (2 * v) clauses (by omega) hw hn root
  have eo := eval_call_lifted OuterCandidateTraversal.program (id : Fin 16 → Fin 16) outerPorts
    (state bits [] [] [] []) Function.injective_id outerPorts_injective hto
  rw [outer_embed, outer_embed] at eo
  simp only [Nat.zero_add] at eo
  have ec := clear_eval bits raw final [] (Encoding.encodeNat (2 * v))
  obtain ⟨nf, hnf, htf⟩ := CanonicalFinalize.source_finalize final
  have ef := eval_call_lifted CanonicalFinalize.program register2 finalPorts
    (state bits raw [] [] []) register2_injective finalPorts_injective htf
  rw [final_embed, final_embed] at ef
  have hall := eh.seq (eb.seq (er.seq (ei.seq (eo.seq (ec.seq ef)))))
  refine ⟨nh + (nb + (nr + (1 + (no + ((2 * (Encoding.encodeNat (2 * v)).length + 3) + nf))))), ?_, hall⟩
  rw [Encoding.length_encodeNat]
  change nf ≤ 9 * (accumulator v clauses).length + 19 at hnf
  dsimp only [timeBound, boundCost]
  omega

theorem source_controller (v : ℕ) (clauses : List (List ℕ))
    (hw : ∀ c ∈ clauses, c.length ≤ 3) (hn : ∀ c ∈ clauses, ∀ x ∈ c, x ≤ 2 * v) :
    BitProgram.RunsIn program (timeBound v clauses)
      ((state (QueryCodec.word v.size v) (FormulaOccurrence.rawBody clauses) [] [] []).withPC (some program.entry))
      ((state (QueryCodec.word v.size v) (FormulaOccurrence.rawBody clauses) (output v clauses) [] []).withPC none) := by
  obtain ⟨n, hn, he⟩ := eval_controller v clauses hw hn
  exact ⟨n + 1, hn, compiled_halt_trace he 19 5⟩

end QecReliability.ExternalSATBridge.CanonicalRawController
