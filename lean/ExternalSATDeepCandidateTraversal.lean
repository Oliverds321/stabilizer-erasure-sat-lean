import ExternalSATUnaryRangeLoop
import ExternalSATVisitBounds

/-! The deepest concrete canonical traversal: retain two candidate fields and
visit the physically incremented third field over an actual unary countdown.
The callback is the actual scan/conditional-emission controller, not a hypothesis.
This does not yet compose the middle/outer traversal or initial query parser. -/
namespace QecReliability.ExternalSATBridge.DeepCandidateTraversal

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls

/-- Counter0, current third code1, fixed first/second2/3, rawbody4, output5,
and eleven genuinely empty scratch stacks6..16. -/
def frame (first second raw outer : List Bool) : UnaryRangeLoop.Frame 15 :=
  ![[], [], first, second, raw, outer, [], [], [], [], [], [], [], [], [], [], []]
abbrev state (counter code first second raw outer : List Bool) :=
  UnaryRangeLoop.store counter code (frame first second raw outer)

def visitPorts : Fin 16 → Fin 17 := ![2, 3, 1, 6, 7, 8, 9, 10, 11, 12, 4, 13, 14, 15, 16, 5]

theorem visitPorts_injective : Function.Injective visitPorts := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [visitPorts]

theorem visit_embed (counter code first second raw oldOuter outer : List Bool) :
    embedState (id : Fin 16 → Fin 16) visitPorts (state counter code first second raw oldOuter)
      (CandidateVisit.store ![first, second, code] raw outer [] false) =
      state counter code first second raw outer := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ Function.injective_id visitPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i hi
    fin_cases i <;> simp_all [visitPorts, state, UnaryRangeLoop.store, frame, Fin.exists_fin_succ]

noncomputable def visit : StructuredCalls.Cmd 16 17 :=
  .call (ProgramLinking.liftProgram CandidateVisit.program id visitPorts)
noncomputable abbrev program := UnaryRangeLoop.program visit

def budget (U : ℕ) (clauses : List (List ℕ)) : ℕ :=
  clauses.length * (288 * U + 707) + 192 * U + 464

/-- Real invocation with a uniform budget; the counter is framed, not read by
any semantic operation. Both fixed candidate fields and the rawbody survive. -/
theorem visit_eval (first second : List Bool) (U code : ℕ) (clauses : List (List ℕ))
    (hf : first.length ≤ U + 1) (hs : second.length ≤ U + 1) (hcode : code ≤ U)
    (hw : ∀ c ∈ clauses, c.length ≤ 3) (hn : ∀ c ∈ clauses, ∀ n ∈ c, n ≤ U)
    (counter outer : List Bool) :
    ∃ n, n ≤ budget U clauses ∧
      Eval visit n (state counter (Encoding.encodeNat code) first second (FormulaOccurrence.rawBody clauses) outer)
        (state counter (Encoding.encodeNat code) first second (FormulaOccurrence.rawBody clauses)
          (CandidateVisit.output ![first, second, Encoding.encodeNat code] clauses outer)) := by
  have hc : ∀ i : Fin 3, (![first, second, Encoding.encodeNat code] i).length ≤ U + 1 := by
    intro i
    fin_cases i
    · exact hf
    · exact hs
    · change (Encoding.encodeNat code).length ≤ U + 1
      simpa only [Encoding.length_encodeNat] using Nat.add_le_add_right hcode 1
  obtain ⟨n, hnb, ht⟩ := CandidateVisit.source_visit ![first, second, Encoding.encodeNat code] clauses hw outer
  have he := eval_call_lifted CandidateVisit.program (id : Fin 16 → Fin 16) visitPorts
    (state counter (Encoding.encodeNat code) first second (FormulaOccurrence.rawBody clauses) outer)
    Function.injective_id visitPorts_injective ht
  rw [visit_embed, visit_embed] at he
  exact ⟨n, hnb.trans (VisitBounds.timeBound_le _ U clauses hc hw hn), he⟩

/-- Proof-level record of successive actual accumulator states, not an
instruction or supplied list of candidates. The code word controls each visit. -/
def output (first second : List Bool) (clauses : List (List ℕ)) (a : ℕ) : ℕ → List Bool → List Bool
  | 0, outer => outer
  | n + 1, outer => CandidateVisit.output ![first, second, Encoding.encodeNat (a + n)] clauses
      (output first second clauses a n outer)

/-- Concrete measured loop, with its callback premise fully discharged by
CandidateVisit. The last code a+n is not visited and the false counter terminator
is consumed. The caller must physically clear that final code before slot reuse. -/
theorem source_traversal (first second : List Bool) (U a n : ℕ) (clauses : List (List ℕ))
    (hf : first.length ≤ U + 1) (hs : second.length ≤ U + 1) (hrange : a + n ≤ U + 1)
    (hw : ∀ c ∈ clauses, c.length ≤ 3) (hn : ∀ c ∈ clauses, ∀ x ∈ c, x ≤ U)
    (outer : List Bool) :
    BitProgram.RunsIn program (n * (budget U clauses + 7) + 4)
      ((state (Encoding.encodeNat n) (Encoding.encodeNat a) first second
        (FormulaOccurrence.rawBody clauses) outer).withPC (some program.entry))
      ((state [] (Encoding.encodeNat (a + n)) first second (FormulaOccurrence.rawBody clauses)
        (output first second clauses a n outer)).withPC none) := by
  let frames : ℕ → UnaryRangeLoop.Frame 15 := fun i =>
    frame first second (FormulaOccurrence.rawBody clauses) (output first second clauses a i outer)
  have hvisit : ∀ i, i < n → ∃ k, k ≤ budget U clauses ∧
      Eval visit k
        (UnaryRangeLoop.store (Encoding.encodeNat (n - 1 - i)) (Encoding.encodeNat (a + i)) (frames i))
        (UnaryRangeLoop.store (Encoding.encodeNat (n - 1 - i)) (Encoding.encodeNat (a + i)) (frames (i + 1))) := by
    intro i hi
    obtain ⟨k, hk, he⟩ := visit_eval first second U (a + i) clauses hf hs (by omega) hw hn
      (Encoding.encodeNat (n - 1 - i)) (output first second clauses a i outer)
    exact ⟨k, hk, he⟩
  simpa only [program, state, frames, output] using
    UnaryRangeLoop.source_range visit n a (budget U clauses) frames hvisit

noncomputable abbrev primitive := GuardedCompiler.primitive program

theorem primitive_traversal (first second : List Bool) (U a n : ℕ) (clauses : List (List ℕ))
    (hf : first.length ≤ U + 1) (hs : second.length ≤ U + 1) (hrange : a + n ≤ U + 1)
    (hw : ∀ c ∈ clauses, c.length ≤ 3) (hn : ∀ c ∈ clauses, ∀ x ∈ c, x ≤ U)
    (outer : List Bool) :
    Computation.RunsIn primitive.step (7 * (n * (budget U clauses + 7) + 4))
      (GuardedCompiler.primitiveCfg program
        ((state (Encoding.encodeNat n) (Encoding.encodeNat a) first second
          (FormulaOccurrence.rawBody clauses) outer).withPC (some program.entry)))
      (GuardedCompiler.primitiveCfg program
        ((state [] (Encoding.encodeNat (a + n)) first second (FormulaOccurrence.rawBody clauses)
          (output first second clauses a n outer)).withPC none)) :=
  GuardedCompiler.primitive_execution program (source_traversal first second U a n clauses hf hs hrange hw hn outer)

end QecReliability.ExternalSATBridge.DeepCandidateTraversal
