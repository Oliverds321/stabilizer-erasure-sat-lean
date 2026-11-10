import ExternalSATFormulaOccurrence

/-! Explicit polynomial time for the actual preserved-body occurrence machine.
Bounds are independent of the old output suffix length. This is NOT an observed
space theorem: a framed space charge must include every preserved input tape. -/
namespace QecReliability.ExternalSATBridge.MatchingBounds
open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- U is a numerical upper bound, not a machine register or extra oracle. -/
theorem fieldCost_le (candidate : Fin 3 → List Bool) (U n : ℕ)
    (hc : ∀ i, (candidate i).length ≤ U + 1) (hn : n ≤ U) :
    RawClauseMatcher.fieldCost candidate n ≤ 89 * U + 211 := by
  have h0 := hc 0; have h1 := hc 1; have h2 := hc 2
  have hlen : (Encoding.encodeNat n).length = n + 1 := by
    simp [Encoding.encodeNat]
  dsimp only [RawClauseMatcher.fieldCost, FieldMembership.timeBound]
  rw [hlen]
  omega

theorem fieldsCost_le (candidate : Fin 3 → List Bool) (U : ℕ) (codes : List ℕ)
    (hc : ∀ i, (candidate i).length ≤ U + 1) (hn : ∀ n ∈ codes, n ≤ U) :
    RawClauseMatcher.fieldsCost candidate codes ≤ codes.length * (89 * U + 211) := by
  induction codes with
  | nil => simp [RawClauseMatcher.fieldsCost]
  | cons n ns ih =>
    have hf := fieldCost_le candidate U n hc (hn n (by simp))
    have ht := ih (by intro x hx; exact hn x (by simp [hx]))
    simp only [RawClauseMatcher.fieldsCost, List.map_cons, List.sum_cons, List.length_cons] at *
    nlinarith

theorem fields_length_le (U : ℕ) (codes : List ℕ) (hn : ∀ n ∈ codes, n ≤ U) :
    (RawClauseMatcher.fields codes).length ≤ codes.length * (U + 1) := by
  induction codes with
  | nil => simp [RawClauseMatcher.fields]
  | cons n ns ih =>
    have hf := hn n (by simp)
    have ht := ih (by intro x hx; exact hn x (by simp [hx]))
    have hlen : (Encoding.encodeNat n).length = n + 1 := by simp [Encoding.encodeNat]
    simp only [RawClauseMatcher.fields, List.flatMap_cons, List.length_append,
      List.length_cons, hlen] at *
    nlinarith

theorem clause_length_le (U : ℕ) (codes : List ℕ)
    (hw : codes.length ≤ 3) (hn : ∀ n ∈ codes, n ≤ U) :
    (RawClauseMatcher.rawClause codes).length ≤ 3 * U + 5 := by
  have hf := fields_length_le U codes hn
  have hm := Nat.mul_le_mul_right (U + 1) hw
  have hb : (QueryCodec.word 2 codes.length).length = 2 := rfl
  simp only [RawClauseMatcher.rawClause, List.length_append, hb]
  nlinarith

theorem clause_scanCost_le (candidate : Fin 3 → List Bool) (U : ℕ) (codes : List ℕ)
    (hc : ∀ i, (candidate i).length ≤ U + 1) (hw : codes.length ≤ 3)
    (hn : ∀ n ∈ codes, n ≤ U) :
    RawClauseMatcher.fieldsCost candidate codes + 39 ≤ 267 * U + 672 := by
  have hf := fieldsCost_le candidate U codes hc hn
  have hm := Nat.mul_le_mul_right (89 * U + 211) hw
  nlinarith

theorem rawBody_length_le (U : ℕ) (clauses : List (List ℕ))
    (hw : ∀ c ∈ clauses, c.length ≤ 3) (hn : ∀ c ∈ clauses, ∀ n ∈ c, n ≤ U) :
    (FormulaOccurrence.rawBody clauses).length ≤ clauses.length * (3 * U + 5) := by
  induction clauses with
  | nil => simp [FormulaOccurrence.rawBody]
  | cons c cs ih =>
    have hhead := clause_length_le U c (hw c (by simp)) (hn c (by simp))
    have htail := ih (by intro d hd; exact hw d (by simp [hd]))
      (by intro d hd; exact hn d (by simp [hd]))
    simp only [FormulaOccurrence.rawBody, List.flatMap_cons, List.length_append, List.length_cons] at *
    nlinarith

theorem scanCost_le (candidate : Fin 3 → List Bool) (U : ℕ) (clauses : List (List ℕ))
    (hc : ∀ i, (candidate i).length ≤ U + 1) (hw : ∀ c ∈ clauses, c.length ≤ 3)
    (hn : ∀ c ∈ clauses, ∀ n ∈ c, n ≤ U) :
    FormulaOccurrence.scanCost candidate clauses ≤ clauses.length * (267 * U + 672) := by
  induction clauses with
  | nil => simp [FormulaOccurrence.scanCost]
  | cons c cs ih =>
    have hhead := clause_scanCost_le candidate U c hc (hw c (by simp)) (hn c (by simp))
    have htail := ih (by intro d hd; exact hw d (by simp [hd]))
      (by intro d hd; exact hn d (by simp [hd]))
    simp only [FormulaOccurrence.scanCost, List.map_cons, List.sum_cons, List.length_cons] at *
    nlinarith

theorem timeBound_le (candidate : Fin 3 → List Bool) (U : ℕ) (clauses : List (List ℕ))
    (hc : ∀ i, (candidate i).length ≤ U + 1) (hw : ∀ c ∈ clauses, c.length ≤ 3)
    (hn : ∀ c ∈ clauses, ∀ n ∈ c, n ≤ U) :
    FormulaOccurrence.timeBound candidate clauses ≤ clauses.length * (288 * U + 707) + 11 := by
  have hb := rawBody_length_le U clauses hw hn
  have hs := scanCost_le candidate U clauses hc hw hn
  dsimp only [FormulaOccurrence.timeBound]
  nlinarith

/-- The SAME actual finite controller, with no restriction on preserved output. -/
theorem source_run (candidate : Fin 3 → List Bool) (U : ℕ) (clauses : List (List ℕ))
    (hc : ∀ i, (candidate i).length ≤ U + 1) (hw : ∀ c ∈ clauses, c.length ≤ 3)
    (hn : ∀ c ∈ clauses, ∀ n ∈ c, n ≤ U) (out : List Bool) :
    BitProgram.RunsIn FormulaOccurrence.program (clauses.length * (288 * U + 707) + 11)
      ((FormulaOccurrence.store candidate [] (FormulaOccurrence.rawBody clauses) out false false).withPC
        (some FormulaOccurrence.program.entry))
      ((FormulaOccurrence.store candidate [] (FormulaOccurrence.rawBody clauses)
        (clauses.any (RawClauseMatcher.clauseResult candidate) :: out) false false).withPC none) := by
  obtain ⟨n, hnb, ht⟩ := FormulaOccurrence.source_run candidate clauses hw out
  exact ⟨n, hnb.trans (timeBound_le candidate U clauses hc hw hn), ht⟩

theorem primitive_run (candidate : Fin 3 → List Bool) (U : ℕ) (clauses : List (List ℕ))
    (hc : ∀ i, (candidate i).length ≤ U + 1) (hw : ∀ c ∈ clauses, c.length ≤ 3)
    (hn : ∀ c ∈ clauses, ∀ n ∈ c, n ≤ U) (out : List Bool) :
    Computation.RunsIn FormulaOccurrence.primitive.step
      (7 * (clauses.length * (288 * U + 707) + 11))
      (GuardedCompiler.primitiveCfg FormulaOccurrence.program
        ((FormulaOccurrence.store candidate [] (FormulaOccurrence.rawBody clauses) out false false).withPC
          (some FormulaOccurrence.program.entry)))
      (GuardedCompiler.primitiveCfg FormulaOccurrence.program
        ((FormulaOccurrence.store candidate [] (FormulaOccurrence.rawBody clauses)
          (clauses.any (RawClauseMatcher.clauseResult candidate) :: out) false false).withPC none)) :=
  GuardedCompiler.primitive_execution FormulaOccurrence.program
    (source_run candidate U clauses hc hw hn out)

end QecReliability.ExternalSATBridge.MatchingBounds
#print axioms QecReliability.ExternalSATBridge.MatchingBounds.timeBound_le
#print axioms QecReliability.ExternalSATBridge.MatchingBounds.primitive_run
