import ExternalSATMiddleCandidateTraversal

/-! Concrete outer DFS traversal. Each first-code prefix is visited, its actual
middle range is initialized and run, and the final second-code word is physically
cleared. The empty candidate and query/header initialization remain callers. -/
namespace QecReliability.ExternalSATBridge.OuterCandidateTraversal
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls

def frame (second third raw outer secondCounter thirdCounter : List Bool) : UnaryRangeLoop.Frame 17 :=
  ![[], [], second, third, raw, outer, [], [], [], [], [], [], [], [], [], [], [], secondCounter, thirdCounter]
abbrev store (counter code second third raw outer secondCounter thirdCounter : List Bool) :=
  UnaryRangeLoop.store counter code (frame second third raw outer secondCounter thirdCounter)
abbrev state (counter code raw outer : List Bool) := store counter code [] [] raw outer [] []

def prefixPorts : Fin 16 → Fin 19 := ![1, 2, 3, 6, 7, 8, 9, 10, 11, 12, 4, 13, 14, 15, 16, 5]
def childPorts : Fin 6 → Fin 19 := ![1, 0, 2, 17, 15, 16]
abbrev childRegister : Fin 5 → Fin 16 := fun i => i.castAdd 11
def middlePorts : Fin 18 → Fin 19 := ![17, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18]

theorem prefixPorts_injective : Function.Injective prefixPorts := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [prefixPorts]
theorem childPorts_injective : Function.Injective childPorts := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [childPorts]
theorem childRegister_injective : Function.Injective childRegister := by
  intro a b h; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) h
theorem middlePorts_injective : Function.Injective middlePorts := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [middlePorts]

theorem prefix_embed (counter code raw oldOuter outer : List Bool) :
    embedState (id : Fin 16 → Fin 16) prefixPorts (state counter code raw oldOuter)
      (CandidateVisit.store ![code, [], []] raw outer [] false) = state counter code raw outer := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ Function.injective_id prefixPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i hi
    fin_cases i <;> simp_all [prefixPorts, state, store, frame, UnaryRangeLoop.store, Fin.exists_fin_succ]

theorem child_embed (counter code child raw outer childCounter : List Bool) :
    embedState childRegister childPorts (state [] [] raw outer)
      (PreservingEquality.store PreservingEquality.zeroRegs code counter child childCounter [] []) =
      store counter code child [] raw outer childCounter [] := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ childRegister_injective childPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i <;> simp_all [childRegister, state, store, frame, UnaryRangeLoop.store,
      UnaryRangeLoop.zeroRegs, Fin.exists_fin_succ]
  · intro i hi
    fin_cases i <;> simp_all [childPorts, state, store, frame, UnaryRangeLoop.store, Fin.exists_fin_succ]

theorem middle_embed (counter code child raw oldOuter outer childCounter : List Bool) :
    embedState (id : Fin 16 → Fin 16) middlePorts (state counter code raw oldOuter)
      (MiddleCandidateTraversal.state childCounter child code raw outer) =
      store counter code child [] raw outer childCounter [] := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ Function.injective_id middlePorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i hi
    fin_cases i <;> simp_all [middlePorts, state, store, frame, UnaryRangeLoop.store, Fin.exists_fin_succ]

abbrev clearChild : Program 16 19 3 := StackRoutines.clearProgram 2 0 1

theorem clear_eval (counter code child raw outer : List Bool) :
    Eval (.call clearChild) (2 * child.length + 3)
      (store counter code child [] raw outer [] []) (state counter code raw outer) := by
  apply Eval.call
  let tapeWords : Fin 19 → List Bool :=
    ![counter, code, child, [], raw, outer, [], [], [], [], [], [], [], [], [], [], [], [], []]
  have h := ListRegisterProgram.clear_run (2 : Fin 19) (0 : Fin 16) 1 UnaryRangeLoop.zeroRegs tapeWords
  have hr : readRegs UnaryRangeLoop.zeroRegs 0 1 none = UnaryRangeLoop.zeroRegs := by
    funext i; fin_cases i <;> simp [readRegs, UnaryRangeLoop.zeroRegs]
  have hs : StackRoutines.clearStacks (2 : Fin 19) tapeWords = (state counter code raw outer).stacks := by
    funext i; fin_cases i <;> simp [StackRoutines.clearStacks, tapeWords, state, store, frame, UnaryRangeLoop.store]
  have hi : tapeWords = (store counter code child [] raw outer [] []).stacks := by
    funext i; fin_cases i <;> rfl
  have hl : tapeWords 2 = child := rfl
  have h' := h
  rw [hr, hs, hl] at h'
  change Trace clearChild (2 * child.length + 3)
    ((store counter code child [] raw outer [] []).withPC (some clearChild.entry))
    ((state counter code raw outer).withPC none)
  simpa only [ListRegisterProgram.Run, hi, StructuredProgram.State.withPC, state, store,
    UnaryRangeLoop.store] using h'

noncomputable def visit : StructuredCalls.Cmd 16 19 :=
  .seq (.call (ProgramLinking.liftProgram CandidateVisit.program id prefixPorts))
    (.seq (.call (ProgramLinking.liftProgram CandidateChild.program childRegister childPorts))
      (.seq (.call (ProgramLinking.liftProgram MiddleCandidateTraversal.program id middlePorts)) (.call clearChild)))
noncomputable abbrev program := UnaryRangeLoop.program visit

def budget (U : ℕ) (clauses : List (List ℕ)) : ℕ :=
  (U + 1) * (MiddleCandidateTraversal.budget U clauses + 16) + 64

def visitOutput (clauses : List (List ℕ)) (b r : ℕ) (outer : List Bool) : List Bool :=
  MiddleCandidateTraversal.output (Encoding.encodeNat b) clauses (b + 1) r r
    (CandidateVisit.output ![Encoding.encodeNat b, [], []] clauses outer)

theorem visit_eval (U b r : ℕ) (clauses : List (List ℕ)) (hrange : b + 1 + r ≤ U + 1)
    (hw : ∀ c ∈ clauses, c.length ≤ 3) (hn : ∀ c ∈ clauses, ∀ x ∈ c, x ≤ U)
    (outer : List Bool) :
    ∃ steps, steps ≤ budget U clauses ∧
      Eval visit steps (state (Encoding.encodeNat r) (Encoding.encodeNat b) (FormulaOccurrence.rawBody clauses) outer)
        (state (Encoding.encodeNat r) (Encoding.encodeNat b) (FormulaOccurrence.rawBody clauses)
          (visitOutput clauses b r outer)) := by
  let raw := FormulaOccurrence.rawBody clauses
  let mid := CandidateVisit.output ![Encoding.encodeNat b, [], []] clauses outer
  let final := visitOutput clauses b r outer
  have hb : b ≤ U := by omega
  have hbl : (Encoding.encodeNat b).length ≤ U + 1 := by
    simpa only [Encoding.length_encodeNat] using Nat.add_le_add_right hb 1
  have hc : ∀ i : Fin 3, (![Encoding.encodeNat b, [], []] i).length ≤ U + 1 := by
    intro i; fin_cases i
    · exact hbl
    · simp
    · simp
  obtain ⟨np, hnp, htp⟩ := CandidateVisit.source_visit ![Encoding.encodeNat b, [], []] clauses hw outer
  have ep := eval_call_lifted CandidateVisit.program (id : Fin 16 → Fin 16) prefixPorts
    (state (Encoding.encodeNat r) (Encoding.encodeNat b) raw outer)
    Function.injective_id prefixPorts_injective htp
  rw [prefix_embed, prefix_embed] at ep
  have hbase : DeepCandidateTraversal.budget U clauses ≤ MiddleCandidateTraversal.budget U clauses := by
    dsimp only [MiddleCandidateTraversal.budget]
    nlinarith
  have hp : np ≤ MiddleCandidateTraversal.budget U clauses :=
    (hnp.trans (VisitBounds.timeBound_le _ U clauses hc hw hn)).trans hbase
  obtain ⟨nc, hnc, htc⟩ := CandidateChild.source_child b r
  have ec := eval_call_lifted CandidateChild.program childRegister childPorts
    (state [] [] raw mid) childRegister_injective childPorts_injective htc
  rw [child_embed, child_embed] at ec
  obtain ⟨nm, hnm, htm⟩ := MiddleCandidateTraversal.source_traversal (Encoding.encodeNat b)
    U (b + 1) r clauses hbl hrange hw hn mid
  have em := eval_call_lifted MiddleCandidateTraversal.program (id : Fin 16 → Fin 16) middlePorts
    (state (Encoding.encodeNat r) (Encoding.encodeNat b) raw mid)
    Function.injective_id middlePorts_injective htm
  rw [middle_embed, middle_embed] at em
  have ee := clear_eval (Encoding.encodeNat r) (Encoding.encodeNat b)
    (Encoding.encodeNat (b + 1 + r)) raw final
  have hall := ep.seq (ec.seq (em.seq ee))
  refine ⟨np + (nc + (nm + (2 * (Encoding.encodeNat (b + 1 + r)).length + 3))), ?_, hall⟩
  rw [Encoding.length_encodeNat]
  have hmul := Nat.mul_le_mul_right (MiddleCandidateTraversal.budget U clauses) (show r ≤ U from by omega)
  dsimp only [budget]
  nlinarith

def output (clauses : List (List ℕ)) (a n : ℕ) : ℕ → List Bool → List Bool
  | 0, outer => outer
  | i + 1, outer => visitOutput clauses (a + i) (n - 1 - i) (output clauses a n i outer)

theorem source_traversal (U a n : ℕ) (clauses : List (List ℕ)) (hrange : a + n ≤ U + 1)
    (hw : ∀ c ∈ clauses, c.length ≤ 3) (hn : ∀ c ∈ clauses, ∀ x ∈ c, x ≤ U)
    (outer : List Bool) :
    BitProgram.RunsIn program (n * (budget U clauses + 7) + 4)
      ((state (Encoding.encodeNat n) (Encoding.encodeNat a) (FormulaOccurrence.rawBody clauses) outer).withPC
        (some program.entry))
      ((state [] (Encoding.encodeNat (a + n)) (FormulaOccurrence.rawBody clauses)
        (output clauses a n n outer)).withPC none) := by
  let frames : ℕ → UnaryRangeLoop.Frame 17 := fun i =>
    frame [] [] (FormulaOccurrence.rawBody clauses) (output clauses a n i outer) [] []
  have hvisit : ∀ i, i < n → ∃ k, k ≤ budget U clauses ∧
      Eval visit k
        (UnaryRangeLoop.store (Encoding.encodeNat (n - 1 - i)) (Encoding.encodeNat (a + i)) (frames i))
        (UnaryRangeLoop.store (Encoding.encodeNat (n - 1 - i)) (Encoding.encodeNat (a + i)) (frames (i + 1))) := by
    intro i hi
    obtain ⟨k, hk, he⟩ := visit_eval U (a + i) (n - 1 - i) clauses (by omega) hw hn
      (output clauses a n i outer)
    exact ⟨k, hk, he⟩
  simpa only [program, state, store, frames, output] using
    UnaryRangeLoop.source_range visit n a (budget U clauses) frames hvisit

noncomputable abbrev primitive := GuardedCompiler.primitive program

theorem primitive_traversal (U a n : ℕ) (clauses : List (List ℕ)) (hrange : a + n ≤ U + 1)
    (hw : ∀ c ∈ clauses, c.length ≤ 3) (hn : ∀ c ∈ clauses, ∀ x ∈ c, x ≤ U)
    (outer : List Bool) :
    Computation.RunsIn primitive.step (7 * (n * (budget U clauses + 7) + 4))
      (GuardedCompiler.primitiveCfg program
        ((state (Encoding.encodeNat n) (Encoding.encodeNat a) (FormulaOccurrence.rawBody clauses) outer).withPC
          (some program.entry)))
      (GuardedCompiler.primitiveCfg program
        ((state [] (Encoding.encodeNat (a + n)) (FormulaOccurrence.rawBody clauses)
          (output clauses a n n outer)).withPC none)) :=
  GuardedCompiler.primitive_execution program (source_traversal U a n clauses hrange hw hn outer)

end QecReliability.ExternalSATBridge.OuterCandidateTraversal
