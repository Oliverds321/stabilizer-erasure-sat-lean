import ExternalSATDeepCandidateTraversal
import ExternalSATCandidateChild

/-! Concrete middle DFS traversal. Each iteration visits its two-field prefix,
physically initializes a child range, invokes the concrete deepest traversal,
and physically clears the child's final code. No callback premise is exported. -/
namespace QecReliability.ExternalSATBridge.MiddleCandidateTraversal
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls

/-- Parent counter0/code1, first2, child3, raw4, output5, scratch6..16,
child counter17. Both counters are physical unary words. -/
def frame (first child raw outer childCounter : List Bool) : UnaryRangeLoop.Frame 16 :=
  ![[], [], first, child, raw, outer, [], [], [], [], [], [], [], [], [], [], [], childCounter]
abbrev store (counter code first child raw outer childCounter : List Bool) :=
  UnaryRangeLoop.store counter code (frame first child raw outer childCounter)
abbrev state (counter code first raw outer : List Bool) :=
  store counter code first [] raw outer []

def prefixPorts : Fin 16 → Fin 18 := ![2, 1, 3, 6, 7, 8, 9, 10, 11, 12, 4, 13, 14, 15, 16, 5]
def childPorts : Fin 6 → Fin 18 := ![1, 0, 3, 17, 15, 16]
abbrev childRegister : Fin 5 → Fin 16 := fun i => i.castAdd 11
def deepPorts : Fin 17 → Fin 18 := ![17, 3, 2, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]

theorem prefixPorts_injective : Function.Injective prefixPorts := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [prefixPorts]
theorem childPorts_injective : Function.Injective childPorts := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [childPorts]
theorem childRegister_injective : Function.Injective childRegister := by
  intro a b h; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) h
theorem deepPorts_injective : Function.Injective deepPorts := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [deepPorts]

theorem prefix_embed (counter code first raw oldOuter outer : List Bool) :
    embedState (id : Fin 16 → Fin 16) prefixPorts (state counter code first raw oldOuter)
      (CandidateVisit.store ![first, code, []] raw outer [] false) =
      state counter code first raw outer := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ Function.injective_id prefixPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i hi
    fin_cases i <;> simp_all [prefixPorts, state, store, frame, UnaryRangeLoop.store, Fin.exists_fin_succ]

theorem child_embed (counter code first child raw outer childCounter : List Bool) :
    embedState childRegister childPorts (state [] [] first raw outer)
      (PreservingEquality.store PreservingEquality.zeroRegs code counter child childCounter [] []) =
      store counter code first child raw outer childCounter := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ childRegister_injective childPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i <;> simp_all [childRegister, state, store, frame, UnaryRangeLoop.store,
      UnaryRangeLoop.zeroRegs, Fin.exists_fin_succ]
  · intro i hi
    fin_cases i <;> simp_all [childPorts, state, store, frame, UnaryRangeLoop.store, Fin.exists_fin_succ]

theorem deep_embed (counter code first child raw oldOuter outer childCounter : List Bool) :
    embedState (id : Fin 16 → Fin 16) deepPorts (state counter code first raw oldOuter)
      (DeepCandidateTraversal.state childCounter child first code raw outer) =
      store counter code first child raw outer childCounter := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ Function.injective_id deepPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i hi
    fin_cases i <;> simp_all [deepPorts, state, store, frame, UnaryRangeLoop.store, Fin.exists_fin_succ]

abbrev clearChild : Program 16 18 3 := StackRoutines.clearProgram 3 0 1

theorem clear_eval (counter code first child raw outer : List Bool) :
    Eval (.call clearChild) (2 * child.length + 3)
      (store counter code first child raw outer []) (state counter code first raw outer) := by
  apply Eval.call
  let tapeWords : Fin 18 → List Bool :=
    ![counter, code, first, child, raw, outer, [], [], [], [], [], [], [], [], [], [], [], []]
  have h := ListRegisterProgram.clear_run (3 : Fin 18) (0 : Fin 16) 1 UnaryRangeLoop.zeroRegs tapeWords
  have hr : readRegs UnaryRangeLoop.zeroRegs 0 1 none = UnaryRangeLoop.zeroRegs := by
    funext i; fin_cases i <;> simp [readRegs, UnaryRangeLoop.zeroRegs]
  have hs : StackRoutines.clearStacks (3 : Fin 18) tapeWords =
      (state counter code first raw outer).stacks := by
    funext i; fin_cases i <;> simp [StackRoutines.clearStacks, tapeWords, state, store, frame, UnaryRangeLoop.store]
  have hi : tapeWords = (store counter code first child raw outer []).stacks := by
    funext i; fin_cases i <;> rfl
  have hl : tapeWords 3 = child := rfl
  have h' := h
  rw [hr, hs, hl] at h'
  change Trace clearChild (2 * child.length + 3)
    ((store counter code first child raw outer []).withPC (some clearChild.entry))
    ((state counter code first raw outer).withPC none)
  simpa only [ListRegisterProgram.Run, hi, StructuredProgram.State.withPC,
    state, store, UnaryRangeLoop.store] using h'

noncomputable def visit : StructuredCalls.Cmd 16 18 :=
  .seq (.call (ProgramLinking.liftProgram CandidateVisit.program id prefixPorts))
    (.seq (.call (ProgramLinking.liftProgram CandidateChild.program childRegister childPorts))
      (.seq (.call (ProgramLinking.liftProgram DeepCandidateTraversal.program id deepPorts)) (.call clearChild)))
noncomputable abbrev program := UnaryRangeLoop.program visit

def budget (U : ℕ) (clauses : List (List ℕ)) : ℕ :=
  (U + 1) * (DeepCandidateTraversal.budget U clauses + 16) + 64

def visitOutput (first : List Bool) (clauses : List (List ℕ)) (b r : ℕ) (outer : List Bool) : List Bool :=
  DeepCandidateTraversal.output first (Encoding.encodeNat b) clauses (b + 1) r
    (CandidateVisit.output ![first, Encoding.encodeNat b, []] clauses outer)

theorem visit_eval (first : List Bool) (U b r : ℕ) (clauses : List (List ℕ))
    (hf : first.length ≤ U + 1) (hrange : b + 1 + r ≤ U + 1)
    (hw : ∀ c ∈ clauses, c.length ≤ 3) (hn : ∀ c ∈ clauses, ∀ x ∈ c, x ≤ U)
    (outer : List Bool) :
    ∃ steps, steps ≤ budget U clauses ∧
      Eval visit steps
        (state (Encoding.encodeNat r) (Encoding.encodeNat b) first (FormulaOccurrence.rawBody clauses) outer)
        (state (Encoding.encodeNat r) (Encoding.encodeNat b) first (FormulaOccurrence.rawBody clauses)
          (visitOutput first clauses b r outer)) := by
  let raw := FormulaOccurrence.rawBody clauses
  let mid := CandidateVisit.output ![first, Encoding.encodeNat b, []] clauses outer
  let final := visitOutput first clauses b r outer
  have hb : b ≤ U := by omega
  have hc : ∀ i : Fin 3, (![first, Encoding.encodeNat b, []] i).length ≤ U + 1 := by
    intro i; fin_cases i
    · exact hf
    · change (Encoding.encodeNat b).length ≤ U + 1
      simpa only [Encoding.length_encodeNat] using Nat.add_le_add_right hb 1
    · simp
  obtain ⟨np, hnp, htp⟩ := CandidateVisit.source_visit ![first, Encoding.encodeNat b, []] clauses hw outer
  have ep := eval_call_lifted CandidateVisit.program (id : Fin 16 → Fin 16) prefixPorts
    (state (Encoding.encodeNat r) (Encoding.encodeNat b) first raw outer)
    Function.injective_id prefixPorts_injective htp
  rw [prefix_embed, prefix_embed] at ep
  have hp : np ≤ DeepCandidateTraversal.budget U clauses :=
    hnp.trans (VisitBounds.timeBound_le _ U clauses hc hw hn)
  obtain ⟨nc, hnc, htc⟩ := CandidateChild.source_child b r
  have ec := eval_call_lifted CandidateChild.program childRegister childPorts
    (state [] [] first raw mid) childRegister_injective childPorts_injective htc
  rw [child_embed, child_embed] at ec
  have hbl : (Encoding.encodeNat b).length ≤ U + 1 := by
    simpa only [Encoding.length_encodeNat] using Nat.add_le_add_right hb 1
  obtain ⟨nd, hnd, htd⟩ := DeepCandidateTraversal.source_traversal first (Encoding.encodeNat b)
    U (b + 1) r clauses hf hbl hrange hw hn mid
  have ed := eval_call_lifted DeepCandidateTraversal.program (id : Fin 16 → Fin 16) deepPorts
    (state (Encoding.encodeNat r) (Encoding.encodeNat b) first raw mid)
    Function.injective_id deepPorts_injective htd
  rw [deep_embed, deep_embed] at ed
  have ee := clear_eval (Encoding.encodeNat r) (Encoding.encodeNat b) first
    (Encoding.encodeNat (b + 1 + r)) raw final
  have hall := ep.seq (ec.seq (ed.seq ee))
  refine ⟨np + (nc + (nd + (2 * (Encoding.encodeNat (b + 1 + r)).length + 3))), ?_, hall⟩
  rw [Encoding.length_encodeNat]
  have hmul := Nat.mul_le_mul_right (DeepCandidateTraversal.budget U clauses) (show r ≤ U from by omega)
  dsimp only [budget]
  nlinarith

/-- Prefix before descendants: each middle value is visited, then its strictly
larger third-code range, before the middle code physically advances. -/
def output (first : List Bool) (clauses : List (List ℕ)) (a n : ℕ) : ℕ → List Bool → List Bool
  | 0, outer => outer
  | i + 1, outer => visitOutput first clauses (a + i) (n - 1 - i)
      (output first clauses a n i outer)

theorem source_traversal (first : List Bool) (U a n : ℕ) (clauses : List (List ℕ))
    (hf : first.length ≤ U + 1) (hrange : a + n ≤ U + 1)
    (hw : ∀ c ∈ clauses, c.length ≤ 3) (hn : ∀ c ∈ clauses, ∀ x ∈ c, x ≤ U)
    (outer : List Bool) :
    BitProgram.RunsIn program (n * (budget U clauses + 7) + 4)
      ((state (Encoding.encodeNat n) (Encoding.encodeNat a) first
        (FormulaOccurrence.rawBody clauses) outer).withPC (some program.entry))
      ((state [] (Encoding.encodeNat (a + n)) first (FormulaOccurrence.rawBody clauses)
        (output first clauses a n n outer)).withPC none) := by
  let frames : ℕ → UnaryRangeLoop.Frame 16 := fun i =>
    frame first [] (FormulaOccurrence.rawBody clauses) (output first clauses a n i outer) []
  have hvisit : ∀ i, i < n → ∃ k, k ≤ budget U clauses ∧
      Eval visit k
        (UnaryRangeLoop.store (Encoding.encodeNat (n - 1 - i)) (Encoding.encodeNat (a + i)) (frames i))
        (UnaryRangeLoop.store (Encoding.encodeNat (n - 1 - i)) (Encoding.encodeNat (a + i)) (frames (i + 1))) := by
    intro i hi
    obtain ⟨k, hk, he⟩ := visit_eval first U (a + i) (n - 1 - i) clauses hf (by omega) hw hn
      (output first clauses a n i outer)
    exact ⟨k, hk, he⟩
  simpa only [program, state, store, frames, output] using
    UnaryRangeLoop.source_range visit n a (budget U clauses) frames hvisit

noncomputable abbrev primitive := GuardedCompiler.primitive program

theorem primitive_traversal (first : List Bool) (U a n : ℕ) (clauses : List (List ℕ))
    (hf : first.length ≤ U + 1) (hrange : a + n ≤ U + 1)
    (hw : ∀ c ∈ clauses, c.length ≤ 3) (hn : ∀ c ∈ clauses, ∀ x ∈ c, x ≤ U)
    (outer : List Bool) :
    Computation.RunsIn primitive.step (7 * (n * (budget U clauses + 7) + 4))
      (GuardedCompiler.primitiveCfg program
        ((state (Encoding.encodeNat n) (Encoding.encodeNat a) first
          (FormulaOccurrence.rawBody clauses) outer).withPC (some program.entry)))
      (GuardedCompiler.primitiveCfg program
        ((state [] (Encoding.encodeNat (a + n)) first (FormulaOccurrence.rawBody clauses)
          (output first clauses a n n outer)).withPC none)) :=
  GuardedCompiler.primitive_execution program (source_traversal first U a n clauses hf hrange hw hn outer)

end QecReliability.ExternalSATBridge.MiddleCandidateTraversal
#print axioms QecReliability.ExternalSATBridge.MiddleCandidateTraversal.source_traversal
#print axioms QecReliability.ExternalSATBridge.MiddleCandidateTraversal.primitive_traversal
