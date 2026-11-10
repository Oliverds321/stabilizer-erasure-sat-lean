import ExternalSATMatchingBounds
import ExternalSATCandidateVisit

/-! A uniform polynomial budget for the actual scan/branch/emission visitor.
The old reversed outer-output suffix is unrestricted and never scanned by this
visitor. No claim here drops that suffix from a framed observed-space charge. -/
namespace QecReliability.ExternalSATBridge.VisitBounds
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem timeBound_le (candidate : CandidateVisit.Candidates) (U : ℕ)
    (clauses : List (List ℕ)) (hc : ∀ i, (candidate i).length ≤ U + 1)
    (hw : ∀ c ∈ clauses, c.length ≤ 3) (hn : ∀ c ∈ clauses, ∀ n ∈ c, n ≤ U) :
    CandidateVisit.timeBound candidate clauses ≤
      clauses.length * (288 * U + 707) + 192 * U + 464 := by
  have hs := MatchingBounds.timeBound_le candidate U clauses hc hw hn
  have h0 := hc 0; have h1 := hc 1; have h2 := hc 2
  dsimp only [CandidateVisit.timeBound, CandidateClauseEmitter.wordSize]
  omega

/-- A single budget valid for every candidate in a dimension-bounded traversal. -/
theorem timeBound_quadratic (candidate : CandidateVisit.Candidates) (U R : ℕ)
    (clauses : List (List ℕ)) (hc : ∀ i, (candidate i).length ≤ U + 1)
    (hw : ∀ c ∈ clauses, c.length ≤ 3) (hn : ∀ c ∈ clauses, ∀ n ∈ c, n ≤ U)
    (hU : U ≤ 2 * R) (hm : clauses.length ≤ R) :
    CandidateVisit.timeBound candidate clauses ≤ 2048 * (R + 1) ^ 2 := by
  have ht := timeBound_le candidate U clauses hc hw hn
  have hp : clauses.length * (288 * U + 707) ≤ R * (576 * R + 707) :=
    Nat.mul_le_mul hm (by omega)
  nlinarith

theorem source_visit (candidate : CandidateVisit.Candidates) (U R : ℕ)
    (clauses : List (List ℕ)) (hc : ∀ i, (candidate i).length ≤ U + 1)
    (hw : ∀ c ∈ clauses, c.length ≤ 3) (hn : ∀ c ∈ clauses, ∀ n ∈ c, n ≤ U)
    (hU : U ≤ 2 * R) (hm : clauses.length ≤ R) (outer : List Bool) :
    BitProgram.RunsIn CandidateVisit.program (2048 * (R + 1) ^ 2)
      ((CandidateVisit.store candidate (FormulaOccurrence.rawBody clauses) outer [] false).withPC
        (some CandidateVisit.program.entry))
      ((CandidateVisit.store candidate (FormulaOccurrence.rawBody clauses)
        (CandidateVisit.output candidate clauses outer) [] false).withPC none) := by
  obtain ⟨n, hn', ht⟩ := CandidateVisit.source_visit candidate clauses hw outer
  exact ⟨n, hn'.trans (timeBound_quadratic candidate U R clauses hc hw hn hU hm), ht⟩

noncomputable abbrev primitive := GuardedCompiler.primitive CandidateVisit.program

theorem primitive_visit (candidate : CandidateVisit.Candidates) (U R : ℕ)
    (clauses : List (List ℕ)) (hc : ∀ i, (candidate i).length ≤ U + 1)
    (hw : ∀ c ∈ clauses, c.length ≤ 3) (hn : ∀ c ∈ clauses, ∀ n ∈ c, n ≤ U)
    (hU : U ≤ 2 * R) (hm : clauses.length ≤ R) (outer : List Bool) :
    Computation.RunsIn primitive.step (7 * (2048 * (R + 1) ^ 2))
      (GuardedCompiler.primitiveCfg CandidateVisit.program
        ((CandidateVisit.store candidate (FormulaOccurrence.rawBody clauses) outer [] false).withPC
          (some CandidateVisit.program.entry)))
      (GuardedCompiler.primitiveCfg CandidateVisit.program
        ((CandidateVisit.store candidate (FormulaOccurrence.rawBody clauses)
          (CandidateVisit.output candidate clauses outer) [] false).withPC none)) :=
  GuardedCompiler.primitive_execution CandidateVisit.program
    (source_visit candidate U R clauses hc hw hn hU hm outer)

end QecReliability.ExternalSATBridge.VisitBounds
#print axioms QecReliability.ExternalSATBridge.VisitBounds.timeBound_quadratic
#print axioms QecReliability.ExternalSATBridge.VisitBounds.primitive_visit
